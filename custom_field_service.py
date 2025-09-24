import os
import re

from dateutil.parser import parse
from django.core.cache import cache
from django.db import transaction
from django.utils import timezone

from cp.models import CField
from cp.models import CFieldAuto
from cp.models import CFieldMultiValue
from cp.models import CFieldOption
from cp.models import CFieldTable
from cp.models import CFieldType
from cp.models import CFieldValue
from cp.models import Contact
from cp.models import ContactEventForm
from cp.models import ContactImage
from cp.models import ContactLabel
from cp.models import ContactNote
from cp.models import ContactNoteSourceType
from cp.models import EventFormCField
from cp.models import Label
from cp.models import Opp
from cp.models import OppFormCField
from cp.models import stripped
from cplib.utils.user_input_helper import UserInputHelper

input_helper = UserInputHelper()

now = timezone.localtime(timezone.now())


class CustomFieldService:
    """
    This class is used to process custom fields.
    It handles various operations related to custom fields, such as loading, processing, and saving.
    It also supports image uploads and file uploads.
    """

    def __init__(self, post=None, table=None, company=None, edit=False, request=None, created_type=None):
        self.post = post
        self.table = table
        self.company = company
        self.edit = edit
        self.request = request
        self.now = timezone.localtime(timezone.now())
        self.contact = None
        self.entity = None
        self.contact_event_form = None
        self.created_type = created_type
        self.selected = {}
        self.errors = {}

        # Regular expressions for integers and decimals
        self.number_regex = re.compile(r'[^0-9\.]')

    @property
    def sourcetype(self):
        """Get the source type for event form."""
        return ContactNoteSourceType.objects.get(name='Event Form')

    @property
    def field_types(self):
        """Get the field types from the database."""
        from home.templatetags.home_extras import get_cfield_types
        field_types = cache.get('cfield_types')
        if field_types is None:
            field_types = get_cfield_types()
            field_types['image'] = CFieldType.objects.get(name='image')
            cache.set('cfield_types', field_types, 3600)
        return field_types

    def process(self):
        """Main processing method."""
        if not self._load_entity():
            return self.selected, self.errors

        if not self.post:
            return self.selected, self.errors

        self._process_custom_fields()

        if not self.created_type:
            self._process_files()
        self._process_auto_fields()

        return self.selected, self.errors

    def _load_entity(self):
        """Load the main entity based on the table type."""
        entity_id = input_helper.try_parse_int(self.post['entity'])

        if self.table == 'contact':
            self.contact = Contact.objects.filter(company=self.company, id=entity_id).first()
            self.entity = self.contact
        elif self.table == 'eventform':
            self.contact_event_form = ContactEventForm.objects.filter(company=self.company,
                                                                      id=entity_id).first()
            if self.contact_event_form:
                self.entity = self.contact_event_form
                self.contact = self.contact_event_form.contact
        elif self.table == 'opp':
            opportunity = Opp.objects.filter(company=self.company, id=entity_id).first()
            if opportunity:
                self.entity = opportunity
                self.contact = opportunity.contact

        return self.contact is not None

    def _process_custom_fields(self):
        """Process each custom field from the post data."""
        for key in self.post:
            if key.startswith('cf_'):
                self._process_field(key)

    def _process_field(self, key):
        """Process a single custom field."""

        self.post[key] = stripped(str(self.post[key]), default='')
        parts = key.split('_')

        field_id = input_helper.try_parse_int(parts[1])
        cfield = CField.objects.filter(company=self.company, id=field_id).first()
        if cfield:
            cfield_value = CFieldValue.objects.filter(cfield=cfield, entity_id=self.entity.id).order_by('-id').first()
            field_type_id = cfield.cfield_type_id

            # Delegate processing to specialized methods
            if field_type_id in (self.field_types['select'].id, self.field_types['radio'].id):
                self._process_select_radio(cfield, cfield_value, key)
            elif field_type_id == self.field_types['multiple_select'].id:
                self._process_multiple_select(cfield, key)
            elif field_type_id == self.field_types['checkbox'].id:
                self._process_checkbox(cfield, cfield_value, key)
            elif field_type_id == self.field_types['text'].id:
                self._process_text(cfield, cfield_value, key)
            elif field_type_id == self.field_types['textarea'].id:
                self._process_textarea(cfield, cfield_value, key)
            elif field_type_id == self.field_types['date'].id:
                self._process_date(cfield, cfield_value, key, field_type_id)
            elif field_type_id == self.field_types['time'].id:
                self._process_time(cfield, cfield_value, key, parts, field_type_id)
            elif field_type_id == self.field_types['datetime'].id:
                self._process_datetime(cfield, cfield_value, key, field_type_id)
            elif field_type_id == self.field_types['integer'].id:
                self._process_integer(cfield, cfield_value, key)
            elif field_type_id == self.field_types['decimal'].id:
                self._process_decimal(cfield, cfield_value, key)
            elif cfield.cfield_type is None and not self.created_type:
                self._process_rfield(cfield, cfield_value, key)

    @transaction.atomic
    def update_create_cfiled_value(self, cfield: CField = None, cfield_value: CFieldValue = None, cf_value: str = '',
                                   cfield_option: bool = False):
        """Update or create a CFieldValue based on the provided parameters."""
        cf_value = '' if cf_value is None or cf_value.strip() == 'None' else cf_value
        if isinstance(cfield_value, CFieldValue):
            cfield_value.cf_value = cf_value
            cfield_value.updated = self.now
            cfield_value.save()
        else:
            if not cfield_option:
                self._new_cfiled_value(cfield, cf_value)
            elif cfield_option and cf_value != 0:
                self._new_cfiled_value(cfield, cf_value)

    def _process_select_radio(self, cfield, cfield_value, key):
        """Process the Select and Radio option field."""
        if not self.created_type:
            cfield_option_id = input_helper.try_parse_int(self.post[key])
            cfield_option = CFieldOption.objects.filter(cfield=cfield, id=cfield_option_id).first()
        else:
            cfield_option = CFieldOption.objects.filter(cfield=cfield,
                                                        name__iexact=stripped(str(self.post[key]))).first()
        cfield_option_id = cfield_option.id if cfield_option else 0

        self.update_create_cfiled_value(cfield, cfield_value, str(cfield_option_id), True)

    @transaction.atomic
    def _process_multiple_select(self, cfield, key):
        """Process the Multiple select option field."""
        try:
            cfield_option_ids = self.post.getlist(key)
        except AttributeError:
            try:
                cfield_option_ids = self.post[key]
            except Exception:
                cfield_option_ids = []

        # Deleted the CFieldMultiValue
        CFieldMultiValue.objects.filter(cfield=cfield, entity_id=self.entity.id).delete()

        for cfield_option in CFieldOption.objects.filter(cfield=cfield, id__in=cfield_option_ids):
            cfield_multi_value = CFieldMultiValue(cfield=cfield,
                                                  option=cfield_option,
                                                  entity_id=self.entity.id,
                                                  updated=self.now)
            cfield_multi_value.save()

    def _process_checkbox(self, cfield, cfield_value, key):
        """Process a custom checkbox filed."""
        cf_value = input_helper.try_parse_int(self.post[key])
        cf_value = 0 if cf_value != 1 else cf_value
        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    def _process_text(self, cfield, cfield_value, key):
        """Process a custom text filed."""
        cf_value = str(self.post[key])[0:255]
        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    def _process_textarea(self, cfield, cfield_value, key):
        """Process the custom textarea filed."""
        cf_value = str(self.post[key])[0:4096]

        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    def _process_date(self, cfield, cfield_value, key, file_type_id):
        """Process a custom date filed."""
        cf_value = self._parse_date_time(self.post[key], file_type_id)
        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    def _process_time(self, cfield, cfield_value, key, parts, file_type_id):
        """Process the custom time field."""
        cf_value = self.post.get(key, '')
        if not self.created_type and len(parts) == 3 and parts[2] == 'hour':
            hour = self.post.get(f'cf_{cfield.id}_hour', '')
            minute = self.post.get(f'cf_{cfield.id}_minute', '')
            ampm = self.post.get(f'cf_{cfield.id}_ampm', '')

            cf_value = '%s:%s:%s' % (hour, minute, ampm)

        cf_value = self._parse_date_time(cf_value, file_type_id)
        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    def _process_datetime(self, cfield, cfield_value, key, field_type_id):
        """Process a custom datetime filed."""

        date_str = self.post.get(f'cf_{cfield.id}', '')
        hour = self.post.get(f'cf_{cfield.id}_hour', '')
        minute = self.post.get(f'cf_{cfield.id}_minute', '')
        ampm = self.post.get(f'cf_{cfield.id}_ampm', '')

        hour = hour or '12'
        minute = minute or '00'
        ampm = ampm or 'PM'

        cf_value = '%s %s:%s:%s' % (date_str, hour, minute, ampm) if not self.created_type else self.post[key]

        cf_value = self._parse_date_time(cf_value, field_type_id)
        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    def _parse_date_time(self, date_str, data_type):
        """Parse a date string into a datetime object."""

        if not self.created_type:
            return date_str
        try:
            date_str = date_str.strip()
            date_obj = parse(date_str)

            # Format the date object based on the data type
            if data_type == self.field_types['date'].id:
                date_obj = date_obj.strftime('%m/%d/%Y')
            elif data_type == self.field_types['datetime'].id:
                date_obj = date_obj.strftime('%m/%d/%Y %I:%M:%p')
            elif data_type == self.field_types['time'].id:
                date_obj = date_obj.strftime('%I:%M:%p')

            return date_obj
        except Exception:
            return None

    def _process_integer(self, cfield, cfield_value, key):
        """Process a custom integer filed."""
        cf_value = self.post[key]
        cf_value = input_helper.try_parse_int(self.number_regex.sub('', cf_value)[0:255])
        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    def _process_decimal(self, cfield, cfield_value, key):
        """Process a custom decimal filed."""
        cf_value = self.post[key]
        cf_value = input_helper.try_parse_float(self.number_regex.sub('', cf_value)[0:255])

        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

    @transaction.atomic
    def _process_rfield(self, cfield, cfield_value, key):
        """Process a custom field that is not a select, radio, or checkbox."""
        cf_value = str(self.post[key])
        regular_field_name = getattr(cfield.rfield, 'name', None)
        if cfield.rfield and cfield.rfield.name == regular_field_name:
            labels = self.request.POST.getlist(key, [])
            labels = [str(label).strip() for label in labels if stripped(str(label))]
            cf_value = ', '.join(labels)

        cf_value = cf_value[0:4096]
        self.update_create_cfiled_value(cfield, cfield_value, str(cf_value), False)

        if cfield.rfield and not self.edit:
            if regular_field_name in ['first_name', 'last_name']:
                self.post[key] = cf_value[:32]
            elif regular_field_name in ['email', 'city', 'title', 'company_name']:
                self.post[key] = cf_value[:64]
            elif regular_field_name in ['address', 'address2', 'account', 'website']:
                self.post[key] = cf_value[:80]
            elif regular_field_name in ['zip']:
                self.post[key] = cf_value[:10]
            elif '_id' in regular_field_name:
                self.post[key] = input_helper.try_parse_int(str(self.post[key])) or None

            if regular_field_name == 'company_name':
                contact_company = self.contact.contact_company
                contact_company.name = self.post[key]
                contact_company.updated = self.now
                contact_company.save()
            elif regular_field_name == 'notes':
                try:
                    self.post[key] = stripped(str(self.post[key]), '')[:4096]
                    if self.table == 'eventform' and self.post[key] != '':
                        note = ContactNote(company=self.company,
                                           contact=self.contact,
                                           user=self.post['user'],
                                           note=self.post[key] + ' [Event Form: ' + self.entity.event_form.name + ']',
                                           sourcetype=self.sourcetype,
                                           source_id=self.entity.id,
                                           created=self.now)
                        note.save()
                except Exception:
                    pass
            elif regular_field_name == 'labels':
                try:
                    labels = self.request.POST.getlist(key, [])
                    labels = list(dict.fromkeys(map(str.strip, labels)))
                except Exception:
                    labels = []

                ContactLabel.objects.filter(contact=self.contact).delete()
                for label in labels:
                    if label:
                        try:
                            label, _ = Label.objects.get_or_create(company=self.company, name=label)
                        except Exception:
                            # Handle the case where multiple Label objects are found
                            label = Label.objects.filter(company=self.company, name=label).first()
                        ContactLabel.objects.create(label=label, contact=self.contact)
            else:
                setattr(self.contact, regular_field_name, self.post.get(key))
                try:
                    self.contact.save()
                except Exception:
                    pass

    @transaction.atomic
    def _new_cfiled_value(self, cfield, cf_value):
        """Save a new custom field value."""
        cf_value = cf_value or None
        cfield_value = None

        try:
            if cf_value:
                cfield_value = CFieldValue(cfield=cfield, cf_value=cf_value,
                                           entity_id=self.entity.id, updated=self.now)
                cfield_value.save()
            return cfield_value
        except Exception:
            return cfield_value

    def _process_files(self):
        """Process files from the post data."""
        if 'files' in self.post:
            for key in self.post['files']:
                if key.startswith('cf_'):
                    self._process_file_field(key)

    def _process_file_field(self, key):
        """Process a single file field."""

        parts = key.split('_')
        field_id = input_helper.try_parse_int(parts[1])

        cfield = CField.objects.filter(company=self.company, id=field_id).first()
        cfield_value = CFieldValue.objects.filter(cfield=cfield, entity_id=self.entity.id).order_by('-id').first()

        if cfield and cfield.cfield_type == self.field_types['image']:
            self._process_image(cfield, cfield_value, key)

    def _process_auto_fields(self):
        """Process auto-calculated fields."""
        auto_fields = self._gather_auto_fields()
        for field in auto_fields:
            self._calculate_auto_field(field)

    def _gather_auto_fields(self):
        """Gather the custom fields for auto-calculation."""
        auto_fields = []
        if self.table == 'contact':
            contact_table = CFieldTable.objects.filter(name='contact').first()
            cfileds = CField.objects.filter(company=self.company, cfield_table=contact_table).order_by('position')
        elif self.table == 'eventform' and self.contact_event_form:
            cfileds = EventFormCField.objects.filter(event_form=self.contact_event_form.event_form).order_by('position')
        elif self.table == 'opp':
            cfileds = OppFormCField.objects.filter(company=self.company).order_by('position')
        else:
            cfileds = []

        for filed in cfileds:
            auto_filed = CFieldAuto.objects.filter(company=self.company,
                                                   cfield=filed.cfield if hasattr(filed, 'cfield') else filed).first()
            if auto_filed:
                auto_fields.append(auto_filed)

        return auto_fields

    def _calculate_auto_field(self, auto_field):
        """Calculate and save an auto-calculated custom field value."""
        cfield_value = CFieldValue.objects.filter(cfield=auto_field.cfield,
                                                  entity_id=self.entity.id).order_by('-id').first()
        cfield_1_value = CFieldValue.objects.filter(cfield=auto_field.cfield_1,
                                                    entity_id=self.entity.id).order_by('-id').first()
        cfield_2_value = CFieldValue.objects.filter(cfield=auto_field.cfield_2,
                                                    entity_id=self.entity.id).order_by('-id').first()

        cf_value = 0
        if cfield_1_value and cfield_2_value:
            cf_value_1 = input_helper.try_parse_int(str(cfield_1_value.cf_value))
            cf_value_2 = input_helper.try_parse_int(str(cfield_2_value.cf_value))

            # Auto filed actions
            if auto_field.action.name == 'difference':
                cf_value = abs(cf_value_1 - cf_value_2)
            elif auto_field.action.name == 'add':
                cf_value = cf_value_1 + cf_value_2
            elif auto_field.action.name == 'subtract':
                cf_value = cf_value_1 - cf_value_2

        self.update_create_cfiled_value(auto_field.cfield, cfield_value, str(cf_value), False)

    @transaction.atomic
    def _process_image(self, cfield, cfield_value, key):
        """Process the custom image filed"""

        c_img_id = input_helper.try_parse_int(str(getattr(cfield_value, 'cf_value', None)))

        if cfield_value and c_img_id:
            contact_img = ContactImage.objects.filter(contact=self.contact, id=c_img_id).first()
            if contact_img:
                try:
                    os.remove(str(contact_img.image))
                except Exception:
                    pass

                contact_img.image = self.post.get('files', {}).get(key)
                contact_img.save()

            cfield_value.updated = self.now
            cfield_value.save()
        else:
            contact_img = ContactImage(company=self.company,
                                       contact=self.contact,
                                       cfield=cfield,
                                       user=self.post['user'],
                                       created=self.now)
            if self.contact_event_form and self.table == 'eventform':
                contact_img.contact_event_form = self.contact_event_form
            contact_img.save()

            if contact_img and contact_img.id:
                contact_img = ContactImage.objects.filter(id=contact_img.id).first()
                if contact_img:
                    contact_img.image = self.post.get('files', {}).get(key)
                    try:
                        contact_img.save()
                    except Exception:
                        pass
                    self._new_cfiled_value(cfield, contact_img.id)
