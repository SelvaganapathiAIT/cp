import os
import sys
import django
import argparse
import logging
import time
from django.db import IntegrityError, transaction
from datetime import datetime, date
from django.utils import timezone
from typing import Dict, Optional, List, Tuple
from dataclasses import dataclass, field
from django.core.files import File

# Setup Django
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../../")))
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "settings")
django.setup()

from django.conf import settings

# Setup logging
LOG_DIR = getattr(settings, "LOGS", os.path.join(settings.BASE_DIR, "logs"))
os.makedirs(LOG_DIR, exist_ok=True)
LOG_FILENAME = os.path.join(LOG_DIR, "01.copy_contact_data.log")

LOG_FORMAT = (
    "%(asctime)-15s "
    "[%(filename)s:%(lineno)s %(funcName)20s()] - "
    "%(levelname)-8s - "
    "%(message)s"
)

# Reset logging handlers
for handler in logging.root.handlers[:]:
    logging.root.removeHandler(handler)

logger = logging.getLogger()
logger.setLevel(logging.INFO)

console_handler = logging.StreamHandler(sys.stdout)
console_handler.setFormatter(logging.Formatter(LOG_FORMAT))
logger.addHandler(console_handler)

file_handler = logging.FileHandler(LOG_FILENAME, mode="a", encoding="utf-8")
file_handler.setFormatter(logging.Formatter(LOG_FORMAT))
logger.addHandler(file_handler)

start_time = time.time()
logger.info("=" * 80)
logger.info("Contact Data Copy Service Started")
logger.info(f"Started at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
logger.info("=" * 80)

# Import models
from cp.models import (
    Company, Contact, User, ContactNote, ContactPhone, CFieldValue, CField, 
    CFieldTable, CFieldMultiValue, CFieldOption, CFieldAuto,
    ContactType, ContactCompany, PhoneType, ContactImage, ContactLabel, 
    ContactPersonnel, ContactRep, ContactResearch, ContactStore, ContactUserFile, 
    ContactPhoneLabel, DealerStore, Label, PeopleRole, ContactPhonePersonnel, 
    ContactRegularFieldsStates, ContactListCust, ContactMenu, EventForm,
    ContactEventForm, EventFormCField, Appointment, Opp, OppStage, OppType, 
    OppContact, OppPersonnel, OppHistory, OppFormCField, ContactEventFormPersonnel,
    ContactInfoEmail,Followup, FollowupType, FollowupStage, FollowupPriority,
    FollowupCall, FollowupPersonnel, CalendarEventFollowups,
    UserFile,  EventFormContactType,EventFormEMail,ReportField,ReportFieldGroupBy
)

from cplib.cfield.custom_field_service import CustomFieldService

@dataclass
class ContactStats:
    """Statistics for contact copy operations"""
    contacts_copied: int = 0
    contacts_created: int = 0
    contacts_updated: int = 0
    contacts_skipped: int = 0
    contact_appointments_copied: int = 0
    contact_event_forms_copied: int = 0
    opps_copied:int = 0
    event_forms_copied: int = 0
    contact_types_copied: int = 0
    contact_companies_copied: int = 0
    phones_copied: int = 0
    notes_copied: int = 0
    images_copied: int = 0
    labels_copied: int = 0
    personnel_copied: int = 0
    reps_copied: int = 0
    research_copied: int = 0
    stores_copied: int = 0
    custom_fields_copied: int = 0
    opp_histories_copied: int = 0
    opp_contacts_copied: int = 0
    opp_personnels_copied: int = 0
    followups_copied: int = 0
    followup_types_copied: int = 0
    followup_stages_copied: int = 0
    followup_priorities_copied: int = 0
    followup_calls_copied: int = 0
    followup_personnels_copied: int = 0
    calendar_event_followups_copied: int = 0
    errors: List[str] = field(default_factory=list)


class CustomFieldHandler:
    """Common class for handling custom field operations with parameters"""
    
    def __init__(self, source_company, target_company, source_user, target_user, logger):
        self.source_company = source_company
        self.target_company = target_company
        self.source_user = source_user
        self.target_user = target_user
        self.logger = logger
        
        # Mapping dictionaries for custom field relationships
        self.cfield_index = {}
        self.cfield_option_index = {}
        self.cfield_table_cache = {}
        self.stats = {
            'custom_fields_copied': 0,
            'custom_field_values_copied': 0,
            'custom_field_multi_values_copied': 0,
            'custom_field_options_copied': 0,
            'custom_field_autos_copied': 0,
            'errors': []
        }

    def get_or_create_cfield_table(self, table_name):
        """Get or create CFieldTable by name"""
        if table_name not in self.cfield_table_cache:
            try:
                table = CFieldTable.objects.filter(name=table_name).first()
                if not table:
                    table = CFieldTable.objects.create(name=table_name)
                    self.logger.info(f"Created new CFieldTable: {table_name}")
                self.cfield_table_cache[table_name] = table
            except Exception as e:
                self.logger.error(f"Error getting/creating CFieldTable {table_name}: {e}")
                return None
        return self.cfield_table_cache[table_name]

    def get_or_create_cfield(self, source_cfield, table_name=None):
        """Get or create CField in target company with optional table override"""
        try:
            # Use provided table_name or source cfield's table
            if table_name:
                target_table = self.get_or_create_cfield_table(table_name)
            else:
                target_table = source_cfield.cfield_table
            
            if not target_table:
                self.logger.warning(f"No valid CFieldTable found for field {source_cfield.name}")
                return None

            # Check if already mapped
            cache_key = f"{source_cfield.id}_{table_name or 'original'}"
            if cache_key in self.cfield_index:
                try:
                    return CField.objects.get(pk=self.cfield_index[cache_key])
                except CField.DoesNotExist:
                    del self.cfield_index[cache_key]

            # Try to find existing CField
            target_cfield = CField.objects.filter(
                company=self.target_company,
                name=source_cfield.name,
                cfield_table=target_table
            ).first()
            
            # If not found and this is for event_form, also check if there's a field
            # with the same name but different table that we can use
            if not target_cfield and table_name == 'event_form':
                # Look for fields with same name in contact table (common for EventForms)
                fallback_cfield = CField.objects.filter(
                    company=self.target_company,
                    name=source_cfield.name
                ).first()
                
                if fallback_cfield:
                    self.logger.debug(f"Found fallback CField {fallback_cfield.name} with table {fallback_cfield.cfield_table.name}")
                    # Use the existing field but ensure it's properly cached
                    self.cfield_index[cache_key] = fallback_cfield.id
                    return fallback_cfield

            if target_cfield:
                self.logger.debug(f"Found existing CField: {target_cfield.name}")
                self.cfield_index[cache_key] = target_cfield.id
                return target_cfield

            # Handle parent cfield if exists
            parent_cfield = None
            if source_cfield.cfield:
                parent_cfield = self.get_or_create_cfield(source_cfield.cfield, table_name)

            # Create new CField
            target_cfield = CField.objects.create(
                company=self.target_company,
                name=source_cfield.name,
                cfield_table=target_table,
                cfield_type=source_cfield.cfield_type,
                rfield=source_cfield.rfield,
                cfield=parent_cfield,
                position=source_cfield.position,
                points=source_cfield.points,
                hide_on_checkout=source_cfield.hide_on_checkout,
                required=source_cfield.required,
                lock=source_cfield.lock
            )

            self.logger.info(f"Created CField: {target_cfield.name} for table {target_table.name}")
            self.cfield_index[cache_key] = target_cfield.id
            self.stats['custom_fields_copied'] += 1

            # Copy options for this field
            self._copy_cfield_options(source_cfield, target_cfield)

            return target_cfield

        except Exception as e:
            error_msg = f"Error creating CField {source_cfield.name}: {e}"
            self.logger.error(error_msg)
            self.stats['errors'].append(error_msg)
            return None

    def _copy_cfield_options(self, source_cfield, target_cfield):
        """Copy CFieldOption records for a given CField"""
        try:
            source_options = CFieldOption.objects.filter(cfield=source_cfield).order_by('position')
            default_option = None
            
            for source_option in source_options:
                # Check if option already exists
                existing_option = CFieldOption.objects.filter(
                    cfield=target_cfield,
                    name=source_option.name
                ).first()
                
                if not existing_option:
                    target_option = CFieldOption.objects.create(
                        cfield=target_cfield,
                        name=source_option.name,
                        position=source_option.position,
                        points=source_option.points or 0
                    )
                    self.cfield_option_index[source_option.id] = target_option.id
                    self.stats['custom_field_options_copied'] += 1
                    self.logger.debug(f"Created CFieldOption: {target_option.name}")
                else:
                    self.cfield_option_index[source_option.id] = existing_option.id
                    target_option = existing_option
                
                # Check if this was the default option in source
                if source_cfield.cfield_option_default and source_cfield.cfield_option_default.id == source_option.id:
                    default_option = target_option
            
            # Set the default option if we found one
            if default_option and not target_cfield.cfield_option_default:
                target_cfield.cfield_option_default = default_option
                target_cfield.save(update_fields=['cfield_option_default'])
                self.logger.debug(f"Set default option for {target_cfield.name}: {default_option.name}")

        except Exception as e:
            self.logger.error(f"Error copying CField options: {e}")

    def get_or_create_cfield_option(self, source_option, target_cfield):
        """
        Get or create a CFieldOption in the target company based on a source option
        
        Args:
            source_option: The source CFieldOption to copy
            target_cfield: The target CField to create the option for
            
        Returns:
            The target CFieldOption instance, or None if creation failed
        """
        try:
            # Check if option already exists by name
            existing_option = CFieldOption.objects.filter(
                cfield=target_cfield,
                name=source_option.name
            ).first()
            
            if existing_option:
                # Update the option index mapping
                self.cfield_option_index[source_option.id] = existing_option.id
                return existing_option
            
            # Create new option
            target_option = CFieldOption.objects.create(
                cfield=target_cfield,
                name=source_option.name,
                position=source_option.position or 0,
                points=source_option.points or 0
            )
            
            # Update mappings and stats
            self.cfield_option_index[source_option.id] = target_option.id
            self.stats['custom_field_options_copied'] += 1
            self.logger.debug(f"Created CFieldOption: {target_option.name} for field {target_cfield.name}")
            
            return target_option
            
        except Exception as e:
            self.logger.error(f"Error creating CFieldOption {source_option.name}: {e}")
            return None

    def copy_cfield_values(self, source_entity_id, target_entity_id, table_name, source_cfields=None):
        """
        Copy CFieldValue records for a specific entity
        
        Args:
            source_entity_id: ID of the source entity
            target_entity_id: ID of the target entity  
            table_name: Name of the CFieldTable (e.g., 'contact', 'event_form', 'opp')
            source_cfields: Optional list of specific CFields to copy, if None copies all
        """
        try:
            # Get source table to filter by
            source_table = self.get_or_create_cfield_table(table_name)
            if not source_table:
                return

            # Build query filters - filter by source company and table
            query_filters = {
                'entity_id': source_entity_id,
                'cfield__company': self.source_company,
                'cfield__cfield_table': source_table
            }
            
            # If specific cfields provided, filter by them
            if source_cfields:
                query_filters['cfield__in'] = source_cfields

            # Copy CFieldValue records
            source_values = CFieldValue.objects.filter(**query_filters)
            self.logger.debug(f"Found {source_values.count()} CFieldValue records for entity {source_entity_id} in table {table_name}")
            
            for source_value in source_values:
                try:
                    target_cfield = self.get_or_create_cfield(source_value.cfield, table_name)
                    if not target_cfield:
                        self.logger.warning(f"Could not create target cfield for {source_value.cfield.name}")
                        continue

                    # Check if value already exists
                    if not CFieldValue.objects.filter(
                        cfield=target_cfield,
                        entity_id=target_entity_id,
                        cf_value=source_value.cf_value
                    ).exists():
                        new_value = CFieldValue.objects.create(
                            cfield=target_cfield,
                            entity_id=target_entity_id,
                            cf_value=source_value.cf_value,
                            updated=source_value.updated or timezone.now()
                        )
                        self.stats['custom_field_values_copied'] += 1
                        self.logger.debug(f"Copied CFieldValue for field {target_cfield.name}: {source_value.cf_value}")
                    else:
                        self.logger.debug(f"CFieldValue already exists for field {target_cfield.name}")

                except Exception as e:
                    self.logger.error(f"Error copying CFieldValue for field {source_value.cfield.name}: {e}")

        except Exception as e:
            self.logger.error(f"Error copying CField values for {table_name}: {e}")

    def copy_cfield_multi_values(self, source_entity_id, target_entity_id, table_name, source_cfields=None):
        """
        Copy CFieldMultiValue records for a specific entity
        
        Args:
            source_entity_id: ID of the source entity
            target_entity_id: ID of the target entity
            table_name: Name of the CFieldTable (e.g., 'contact', 'event_form', 'opp')
            source_cfields: Optional list of specific CFields to copy, if None copies all
        """
        try:
            # Get source table to filter by
            source_table = self.get_or_create_cfield_table(table_name)
            if not source_table:
                return

            # Build query filters - filter by source company and table
            query_filters = {
                'entity_id': source_entity_id,
                'cfield__company': self.source_company,
                'cfield__cfield_table': source_table
            }
            
            # If specific cfields provided, filter by them
            if source_cfields:
                query_filters['cfield__in'] = source_cfields

            # Copy CFieldMultiValue records
            source_multi_values = CFieldMultiValue.objects.filter(**query_filters)
            self.logger.debug(f"Found {source_multi_values.count()} CFieldMultiValue records for entity {source_entity_id} in table {table_name}")
            
            for source_multi_value in source_multi_values:
                try:
                    target_cfield = self.get_or_create_cfield(source_multi_value.cfield, table_name)
                    if not target_cfield:
                        self.logger.warning(f"Could not create target cfield for {source_multi_value.cfield.name}")
                        continue

                    # Get or create target option using centralized method
                    target_option = self.get_or_create_cfield_option(source_multi_value.option, target_cfield)

                    # Check if multi-value already exists
                    if not CFieldMultiValue.objects.filter(
                        cfield=target_cfield,
                        entity_id=target_entity_id,
                        option=target_option
                    ).exists():
                        new_multi_value = CFieldMultiValue.objects.create(
                            cfield=target_cfield,
                            entity_id=target_entity_id,
                            option=target_option,
                            updated=source_multi_value.updated or timezone.now()
                        )
                        self.stats['custom_field_multi_values_copied'] += 1
                        self.logger.debug(f"Copied CFieldMultiValue for field {target_cfield.name}: option {target_option.name}")
                    else:
                        self.logger.debug(f"CFieldMultiValue already exists for field {target_cfield.name}")

                except Exception as e:
                    self.logger.error(f"Error copying CFieldMultiValue for field {source_multi_value.cfield.name}: {e}")

        except Exception as e:
            self.logger.error(f"Error copying CField multi values for {table_name}: {e}")

    def copy_event_form_cfields(self, source_event_form, target_event_form):
        """Copy EventFormCField relationships with improved field mapping"""
        try:
            source_form_fields = EventFormCField.objects.filter(event_form=source_event_form)
            self.logger.info(f"Found {source_form_fields.count()} EventFormCFields to copy from {source_event_form.name}")
            
            for source_form_field in source_form_fields:
                try:
                    source_cfield = source_form_field.cfield
                    self.logger.debug(f"Processing EventFormCField: {source_cfield.name} (ID: {source_cfield.id})")
                    self.logger.debug(f"  - Source cfield_table: {source_cfield.cfield_table.name if source_cfield.cfield_table else 'None'}")
                    self.logger.debug(f"  - Source cfield_type: {source_cfield.cfield_type.name if source_cfield.cfield_type else 'None'}")
                    self.logger.debug(f"  - Source rfield: {source_cfield.rfield.name if source_cfield.rfield else 'None'}")
                    
                    # Determine the correct table name for the field
                    table_name = 'event_form'
                    if source_cfield.cfield_table:
                        # Use the source field's table name if it exists
                        original_table_name = source_cfield.cfield_table.name
                        self.logger.debug(f"  - Original table name: {original_table_name}")
                        
                        # For EventForm fields, we want to ensure they use 'event_form' table
                        # but preserve the original mapping logic for other types
                        if original_table_name in ['contact', 'opp']:
                            table_name = original_table_name
                        else:
                            table_name = 'event_form'
                    
                    self.logger.debug(f"  - Using table name: {table_name}")
                    
                    target_cfield = self.get_or_create_cfield(source_cfield, table_name)
                    if not target_cfield:
                        self.logger.warning(f"Failed to create target CField for {source_cfield.name}")
                        continue

                    # Check if relationship already exists
                    if not EventFormCField.objects.filter(
                        event_form=target_event_form,
                        cfield=target_cfield
                    ).exists():
                        EventFormCField.objects.create(
                            event_form=target_event_form,
                            cfield=target_cfield,
                            position=source_form_field.position
                        )
                        self.logger.info(f"Created EventFormCField for {target_cfield.name} (table: {target_cfield.cfield_table.name})")
                    else:
                        self.logger.debug(f"EventFormCField already exists for {target_cfield.name}")

                except Exception as e:
                    self.logger.error(f"Error copying EventFormCField for field {source_form_field.cfield.name}: {e}")
                    import traceback
                    self.logger.error(f"Traceback: {traceback.format_exc()}")

        except Exception as e:
            self.logger.error(f"Error copying event form cfields: {e}")
            import traceback
            self.logger.error(f"Traceback: {traceback.format_exc()}")

    def copy_opp_form_cfields(self, source_company=None, target_company=None):
        """Copy OppFormCField relationships"""
        try:
            source_comp = source_company or self.source_company
            target_comp = target_company or self.target_company
            
            source_opp_fields = OppFormCField.objects.filter(company=source_comp)
            
            for source_opp_field in source_opp_fields:
                try:
                    target_cfield = self.get_or_create_cfield(source_opp_field.cfield, 'opp')
                    if not target_cfield:
                        continue

                    # Check if relationship already exists
                    if not OppFormCField.objects.filter(
                        company=target_comp,
                        cfield=target_cfield
                    ).exists():
                        OppFormCField.objects.create(
                            company=target_comp,
                            cfield=target_cfield,
                            position=source_opp_field.position
                        )
                        self.logger.debug(f"Created OppFormCField for {target_cfield.name}")

                except Exception as e:
                    self.logger.error(f"Error copying OppFormCField: {e}")

        except Exception as e:
            self.logger.error(f"Error copying opp form cfields: {e}")

    def copy_cfield_autos(self, table_name=None):
        """Copy CFieldAuto records"""
        try:
            query_filters = {'company': self.source_company}
            if table_name:
                target_table = self.get_or_create_cfield_table(table_name)
                if target_table:
                    query_filters['cfield__cfield_table'] = target_table

            source_autos = CFieldAuto.objects.filter(**query_filters)
            
            for source_auto in source_autos:
                try:
                    # Get target cfields
                    target_cfield = self.get_or_create_cfield(source_auto.cfield, table_name)
                    target_cfield_1 = self.get_or_create_cfield(source_auto.cfield_1, table_name)
                    target_cfield_2 = self.get_or_create_cfield(source_auto.cfield_2, table_name)
                    
                    if not all([target_cfield, target_cfield_1, target_cfield_2]):
                        continue

                    # Check if auto already exists
                    if not CFieldAuto.objects.filter(
                        company=self.target_company,
                        cfield=target_cfield,
                        cfield_1=target_cfield_1,
                        cfield_2=target_cfield_2
                    ).exists():
                        CFieldAuto.objects.create(
                            company=self.target_company,
                            cfield=target_cfield,
                            action=source_auto.action,
                            cfield_1=target_cfield_1,
                            cfield_2=target_cfield_2,
                            hide=source_auto.hide
                        )
                        self.stats['custom_field_autos_copied'] += 1
                        self.logger.debug(f"Created CFieldAuto for {target_cfield.name}")

                except Exception as e:
                    self.logger.error(f"Error copying CFieldAuto: {e}")

        except Exception as e:
            self.logger.error(f"Error copying CField autos: {e}")

    def copy_all_custom_fields_for_entity(self, source_entity_id, target_entity_id, table_name):
        """
        Convenience method to copy all custom field data for an entity
        
        Args:
            source_entity_id: ID of the source entity
            target_entity_id: ID of the target entity
            table_name: Name of the CFieldTable (e.g., 'contact', 'event_form', 'opp')
        """
        self.logger.info(f"Copying all custom fields for {table_name} entity {source_entity_id} -> {target_entity_id}")
        
        # For event_form entities, we need to check all possible table types since EventForm
        # fields might be associated with different CFieldTable types
        if table_name == 'event_form':
            # Copy from all relevant table types that might be used in event forms
            table_types_to_check = ['event_form', 'contact', 'opp']
            
            for table_type in table_types_to_check:
                self.logger.debug(f"Checking for custom fields with table type: {table_type}")
                
                # Count existing values before copying
                existing_values = CFieldValue.objects.filter(
                    entity_id=source_entity_id,
                    cfield__company=self.source_company,
                    cfield__cfield_table__name=table_type
                ).count()
                
                existing_multi_values = CFieldMultiValue.objects.filter(
                    entity_id=source_entity_id,
                    cfield__company=self.source_company,
                    cfield__cfield_table__name=table_type
                ).count()
                
                if existing_values > 0 or existing_multi_values > 0:
                    self.logger.info(f"Found {existing_values} CFieldValues and {existing_multi_values} CFieldMultiValues for table type {table_type}")
                    
                    # Copy field values and multi-values for this table type
                    self.copy_cfield_values(source_entity_id, target_entity_id, table_type)
                    self.copy_cfield_multi_values(source_entity_id, target_entity_id, table_type)
                else:
                    self.logger.debug(f"No custom field values found for table type {table_type}")
        else:
            # For other entity types, use the standard approach
            self.copy_cfield_values(source_entity_id, target_entity_id, table_name)
            self.copy_cfield_multi_values(source_entity_id, target_entity_id, table_name)
            
    def copy_custom_fields_by_type(self, source_entity_id, target_entity_id, table_name):
        """
        Enhanced method to copy custom fields with proper type handling
        This method ensures that each field type is handled correctly based on its storage mechanism
        
        Args:
            source_entity_id: ID of the source entity
            target_entity_id: ID of the target entity
            table_name: Name of the CFieldTable (e.g., 'contact', 'event_form', 'opp')
        """
        try:
            source_table = self.get_or_create_cfield_table(table_name)
            if not source_table:
                return
            
            # Get all CFields for this table and company
            source_cfields = CField.objects.filter(
                company=self.source_company,
                cfield_table=source_table
            ).select_related('cfield_type')
            
            self.logger.info(f"Processing {source_cfields.count()} custom fields for {table_name}")
            
            for source_cfield in source_cfields:
                self.logger.debug(f"Processing field: {source_cfield.name} (type: {source_cfield.cfield_type.name if source_cfield.cfield_type else 'None'})")
                
                # Ensure target field exists
                target_cfield = self.get_or_create_cfield(source_cfield, table_name)
                if not target_cfield:
                    self.logger.warning(f"Could not create target field for {source_cfield.name}")
                    continue
                
                # Handle field based on its type
                if self._uses_single_value_storage(source_cfield):
                    # Handle single value fields (text, integer, etc.)
                    self._copy_single_value_field(source_cfield, target_cfield, source_entity_id, target_entity_id)
                elif self._uses_multi_value_storage(source_cfield):
                    # Handle multi-value fields (select, radio, etc.)
                    self._copy_multi_value_field(source_cfield, target_cfield, source_entity_id, target_entity_id)
                else:
                    self.logger.warning(f"Unknown field type for {source_cfield.name}: {source_cfield.cfield_type.name if source_cfield.cfield_type else 'None'}")
                    
        except Exception as e:
            self.logger.error(f"Error copying custom fields by type for {table_name}: {e}")
            
    def _copy_single_value_field(self, source_cfield, target_cfield, source_entity_id, target_entity_id):
        """Copy a single-value field (text, integer, etc.)"""
        try:
            source_values = CFieldValue.objects.filter(
                cfield=source_cfield,
                entity_id=source_entity_id
            )
            
            for source_value in source_values:
                if not CFieldValue.objects.filter(
                    cfield=target_cfield,
                    entity_id=target_entity_id,
                    cf_value=source_value.cf_value
                ).exists():
                    CFieldValue.objects.create(
                        cfield=target_cfield,
                        entity_id=target_entity_id,
                        cf_value=source_value.cf_value,
                        updated=source_value.updated or timezone.now()
                    )
                    self.stats['custom_field_values_copied'] += 1
                    self.logger.debug(f"Copied single value for {target_cfield.name}: {source_value.cf_value}")
                    
        except Exception as e:
            self.logger.error(f"Error copying single value field {source_cfield.name}: {e}")
            
    def _copy_multi_value_field(self, source_cfield, target_cfield, source_entity_id, target_entity_id):
        """Copy a multi-value field (select, radio, etc.)"""
        try:
            source_multi_values = CFieldMultiValue.objects.filter(
                cfield=source_cfield,
                entity_id=source_entity_id
            )
            
            for source_multi_value in source_multi_values:
                # Get or create target option using centralized method
                target_option = self.get_or_create_cfield_option(source_multi_value.option, target_cfield)
                
                # Create multi-value entry
                if not CFieldMultiValue.objects.filter(
                    cfield=target_cfield,
                    entity_id=target_entity_id,
                    option=target_option
                ).exists():
                    CFieldMultiValue.objects.create(
                        cfield=target_cfield,
                        entity_id=target_entity_id,
                        option=target_option,
                        updated=source_multi_value.updated or timezone.now()
                    )
                    self.stats['custom_field_multi_values_copied'] += 1
                    self.logger.debug(f"Copied multi value for {target_cfield.name}: {target_option.name}")
                    
        except Exception as e:
            self.logger.error(f"Error copying multi value field {source_cfield.name}: {e}")

    def _uses_multi_value_storage(self, cfield):
        """
        Determine if a CField should use CFieldMultiValue storage based on its type
        
        Args:
            cfield: CField instance
            
        Returns:
            bool: True if field should use CFieldMultiValue, False for CFieldValue
        """
        if not cfield.cfield_type:
            return False
        
        # Field types that use CFieldMultiValue (option-based fields)
        multi_value_types = {
            'select', 'radio', 'checkbox', 'multiple_select', 'multi_select'
        }
        
        return cfield.cfield_type.name in multi_value_types
    
    def _uses_single_value_storage(self, cfield):
        """
        Determine if a CField should use CFieldValue storage based on its type
        
        Args:
            cfield: CField instance
            
        Returns:
            bool: True if field should use CFieldValue, False for CFieldMultiValue
        """
        if not cfield.cfield_type:
            return True  # Default to single value
        
        # Field types that use CFieldValue (direct value fields)
        single_value_types = {
            'text', 'integer', 'auto_integer', 'decimal', 'date', 'time', 'datetime', 'textarea'
        }
        
        return cfield.cfield_type.name in single_value_types

    def get_stats(self):
        """Return statistics about custom field copying"""
        return self.stats.copy()
    


    def copy_custom_fields_using_service(self, source_entity_id, target_entity_id, table_name, source_entity=None, target_entity=None):
        """
        Copy custom field values using the CustomFieldService for proper handling of all field types.
        This method leverages the business logic in CustomFieldService to ensure proper field processing.
        
        Args:
            source_entity_id: ID of the source entity
            target_entity_id: ID of the target entity  
            table_name: Name of the CFieldTable (e.g., 'contact', 'eventform', 'opp')
            source_entity: Optional source entity object (Contact, ContactEventForm, Opp)
            target_entity: Optional target entity object (Contact, ContactEventForm, Opp)
        """
        try:
            self.logger.info(f"Copying custom fields using CustomFieldService for {table_name} entity {source_entity_id} -> {target_entity_id}")
            
            # Get all custom field values for the source entity
            source_cfield_values = CFieldValue.objects.filter(
                entity_id=source_entity_id,
                cfield__company=self.source_company
            ).select_related('cfield', 'cfield__cfield_type', 'cfield__cfield_table')
            
            # Get all custom field multi-values for the source entity
            source_cfield_multi_values = CFieldMultiValue.objects.filter(
                entity_id=source_entity_id,
                cfield__company=self.source_company
            ).select_related('cfield', 'cfield__cfield_type', 'cfield__cfield_table', 'option')
            
            if not source_cfield_values.exists() and not source_cfield_multi_values.exists():
                self.logger.debug(f"No custom field data found for {table_name} entity {source_entity_id}")
                return
                
            self.logger.info(f"Found {source_cfield_values.count()} CFieldValues and {source_cfield_multi_values.count()} CFieldMultiValues to copy")

            
            # Process CFieldValue records (for single value fields including select/radio that store option IDs)
            for source_value in source_cfield_values:
                try:
                    self.logger.debug(f"Processing custom field {source_value.cfield} for entity {source_entity_id}")
                    # Get or create the corresponding target custom field
                    source_table_name = source_value.cfield.cfield_table.name if source_value.cfield.cfield_table else table_name
                    target_cfield = self.get_or_create_cfield(source_value.cfield, source_table_name)
                    if not target_cfield:
                        continue
                    
                    field_value = source_value.cf_value
                    self.logger.debug(f"Processing custom field  value {field_value} for entity {source_entity_id}")

                    
                    # Handle select/radio fields that store option IDs in CFieldValue
                    if (target_cfield.cfield_type and 
                        target_cfield.cfield_type.name in ['select', 'radio'] and 
                        field_value and str(field_value).isdigit()):
                        try:
                            source_option_id = int(field_value)
                            source_option = CFieldOption.objects.filter(
                                cfield=source_value.cfield, 
                                id=source_option_id
                            ).first()
                            if source_option:
                                target_option = self.get_or_create_cfield_option(source_option, target_cfield)
                                if target_option:
                                    field_value = str(target_option.id)
                                    self.logger.debug(f"Mapped select/radio option {source_option.name} from ID {source_option_id} to {target_option.id}")
                        except (ValueError, TypeError):
                            self.logger.warning(f"Invalid option ID for select/radio field: {field_value}")
                            continue
                    
                    # Create the target CFieldValue directly (bypassing CustomFieldService for reliability)
                    if not CFieldValue.objects.filter(
                        cfield=target_cfield,
                        entity_id=target_entity_id,
                        cf_value=field_value
                    ).exists():
                        CFieldValue.objects.create(
                            cfield=target_cfield,
                            entity_id=target_entity_id,
                            cf_value=field_value,
                            updated=source_value.updated or timezone.now()
                        )
                        self.stats['custom_field_values_copied'] += 1
                        self.logger.debug(f"Created CFieldValue for field {target_cfield.name} (ID: {target_cfield.id}) = {field_value}")
                    
                except Exception as e:
                    self.logger.error(f"Error processing CFieldValue {source_value.id}: {e}")
                    continue
            
            # Process CFieldMultiValue records (for multi-select fields)
            for source_multi_value in source_cfield_multi_values:
                try:
                    # Get or create the corresponding target custom field
                    source_table_name = source_multi_value.cfield.cfield_table.name if source_multi_value.cfield.cfield_table else table_name
                    target_cfield = self.get_or_create_cfield(source_multi_value.cfield, source_table_name)
                    if not target_cfield:
                        continue
                        
                    # Get or create the corresponding target option
                    target_option = self.get_or_create_cfield_option(source_multi_value.option, target_cfield)
                    if not target_option:
                        continue
                    
                    # Create the target CFieldMultiValue directly
                    if not CFieldMultiValue.objects.filter(
                        cfield=target_cfield,
                        entity_id=target_entity_id,
                        option=target_option
                    ).exists():
                        CFieldMultiValue.objects.create(
                            cfield=target_cfield,
                            entity_id=target_entity_id,
                            option=target_option,
                            updated=source_multi_value.updated or timezone.now()
                        )
                        self.stats['custom_field_multi_values_copied'] += 1
                        self.logger.debug(f"Created CFieldMultiValue for field {target_cfield.name} (ID: {target_cfield.id}) = option {target_option.name}")
                    
                except Exception as e:
                    self.logger.error(f"Error processing CFieldMultiValue {source_multi_value.id}: {e}")
                    continue
            
            # Update statistics
            self.logger.info(f"Successfully copied custom fields for {table_name} entity {target_entity_id}")
                
        except Exception as e:
            self.logger.error(f"Error copying custom fields using service for {table_name}: {e}")
            import traceback
            self.logger.error(f"Traceback: {traceback.format_exc()}")
            
            # Fallback to original method
            try:
                self.logger.info(f"Attempting fallback to original custom field copy method for {table_name} entity {target_entity_id}")
                self.copy_all_custom_fields_for_entity(source_entity_id, target_entity_id, table_name)
            except Exception as fallback_error:
                self.logger.error(f"Fallback method also failed for {table_name}: {fallback_error}")

    def debug_event_form_field_mapping(self, source_event_form, target_event_form):
        """
        Debug method to analyze EventForm field mapping issues
        This method will help identify why custom fields are not being mapped properly
        """
        self.logger.info("=" * 60)
        self.logger.info(f"DEBUGGING EventForm Field Mapping")
        self.logger.info(f"Source EventForm: {source_event_form.name} (ID: {source_event_form.id})")
        self.logger.info(f"Target EventForm: {target_event_form.name} (ID: {target_event_form.id})")
        self.logger.info("=" * 60)
        
        # Get fields using EventForm.get_cfields() method
        source_cfields = source_event_form.get_cfields()
        self.logger.info(f"EventForm.get_cfields() returned {len(source_cfields)} fields:")
        
        for i, cfield in enumerate(source_cfields):
            self.logger.info(f"  {i+1}. Field: {cfield.name} (ID: {cfield.id})")
            self.logger.info(f"     - Table: {cfield.cfield_table.name if cfield.cfield_table else 'None'}")
            self.logger.info(f"     - Type: {cfield.cfield_type.name if cfield.cfield_type else 'None'}")
            self.logger.info(f"     - RField: {cfield.rfield.name if cfield.rfield else 'None'}")
            self.logger.info(f"     - Parent CField: {cfield.cfield.name if cfield.cfield else 'None'}")
            
            # Check if this field has values in the source
            value_count = CFieldValue.objects.filter(cfield=cfield).count()
            multi_value_count = CFieldMultiValue.objects.filter(cfield=cfield).count()
            self.logger.info(f"     - Values in DB: {value_count} CFieldValues, {multi_value_count} CFieldMultiValues")
        
        # Check EventFormCField relationships
        self.logger.info("\nEventFormCField relationships:")
        source_form_fields = EventFormCField.objects.filter(event_form=source_event_form)
        self.logger.info(f"Found {source_form_fields.count()} EventFormCField relationships")
        
        for efc in source_form_fields:
            cfield = efc.cfield
            self.logger.info(f"  - {cfield.name} (pos: {efc.position})")
            self.logger.info(f"    Table: {cfield.cfield_table.name if cfield.cfield_table else 'None'}")
            
            # Check if this field is in the get_cfields() result
            in_get_cfields = cfield in source_cfields
            self.logger.info(f"    In get_cfields(): {in_get_cfields}")
            
            if not in_get_cfields:
                self.logger.warning(f"    *** Field {cfield.name} is in EventFormCField but NOT in get_cfields() result!")
        
        # Check target EventForm
        self.logger.info(f"\nTarget EventForm field relationships:")
        target_form_fields = EventFormCField.objects.filter(event_form=target_event_form)
        self.logger.info(f"Target has {target_form_fields.count()} EventFormCField relationships")
        
        for efc in target_form_fields:
            cfield = efc.cfield
            self.logger.info(f"  - {cfield.name} (table: {cfield.cfield_table.name})")
        
        self.logger.info("=" * 60)


class ContactDataCopier:
    """Main class for copying contact data between users"""
    
    def __init__(self, source_user_id: int, target_user_id: int):
        logger.info(f"Initializing ContactDataCopier for source user {source_user_id} -> target user {target_user_id}")
        
        try:
            self.source_user = User.objects.get(pk=source_user_id)
            self.target_user = User.objects.get(pk=target_user_id)
        except User.DoesNotExist as e:
            logger.error(f"User not found: {e}")
            sys.exit(1)
        
        try:
            self.source_company = self.source_user.userprofile.company
            self.target_company = self.target_user.userprofile.company
            logger.info(f"Source company: {self.source_company.name}")
            logger.info(f"Target company: {self.target_company.name}")
        except Exception as e:
            logger.error(f"Error getting company from user profile: {e}")
            sys.exit(1)
        
        self.stats = ContactStats()
        
        # Mapping dictionaries for foreign key relationships
        self.contact_index = {}
        self.contact_type_index = {}
        self.contact_company_index = {}
        self.phone_type_index = {}
        self.contact_phone_index = {}
        self.appointment_index = {}
        self.eform_appointment_index = {}
        self.opportunity_index = {}
        self.custom_field_index = {}
        self.event_form_index = {}
        
        # Initialize CustomFieldHandler
        self.custom_field_handler = CustomFieldHandler(
            self.source_company, 
            self.target_company, 
            self.source_user, 
            self.target_user, 
            logger
        )
        
        logger.info(f"Source User: {self.source_user.first_name} {self.source_user.last_name}")
        logger.info(f"Target User: {self.target_user.first_name} {self.target_user.last_name}")
        logger.info("-" * 80)

    def _get_field_value_safely(self, obj, field_name, default=None):
        """Safely get field value"""
        try:
            value = getattr(obj, field_name, default)
            if hasattr(value, 'pk'):
                return value
            return value
        except Exception:
            return default

    def _get_or_create_contact_company(self, original_contact_company) -> Optional[ContactCompany]:
        """Get or create ContactCompany for target company"""
        if not original_contact_company:
            return None
        
        try:
            # Check if already mapped
            if original_contact_company.id in self.contact_company_index:
                try:
                    return ContactCompany.objects.get(pk=self.contact_company_index[original_contact_company.id])
                except ContactCompany.DoesNotExist:
                    del self.contact_company_index[original_contact_company.id]
            
            # Try to find existing ContactCompany
            target_contact_company = ContactCompany.objects.filter(
                company=self.target_company,
                name=original_contact_company.name
            ).first()
            
            if target_contact_company:
                logger.info(f"Found existing ContactCompany: {target_contact_company.name}")
                self.contact_company_index[original_contact_company.id] = target_contact_company.id
                return target_contact_company
            
            # Create new one
            target_contact_company = ContactCompany.objects.create(
                company=self.target_company,
                name=original_contact_company.name,
                created=original_contact_company.created or timezone.now(),
                updated=original_contact_company.updated or timezone.now(),
                primary_contact=None
            )
            
            logger.info(f"Created ContactCompany: {target_contact_company.name}")
            self.contact_company_index[original_contact_company.id] = target_contact_company.id
            self.stats.contact_companies_copied += 1
            return target_contact_company
                
        except Exception as e:
            error_msg = f"Error handling ContactCompany '{original_contact_company.name}': {e}"
            logger.error(error_msg)
            self.stats.errors.append(error_msg)
            return None

    def _copy_contact_types(self):
        """Copy ContactType records from source to target company"""
        logger.info("Copying ContactType records...")
        
        for ct in ContactType.objects.filter(company=self.source_company):
            try:
                existing_ct = ContactType.objects.filter(
                    company=self.target_company, 
                    name=ct.name
                ).first()
                
                if not existing_ct:
                    new_ct = ContactType.objects.create(
                        company=self.target_company,
                        name=ct.name,
                        position=ct.position,
                        is_default=ct.is_default,
                        reference_contact_type_name=ct.reference_contact_type_name
                    )
                    self.contact_type_index[ct.id] = new_ct.id
                    self.stats.contact_types_copied += 1
                    logger.info(f'ContactType created: {new_ct.name}')
                    
                    # Copy image if exists
                    if ct.image and ct.image.name:
                        try:
                            img_name = ct.image.name.lstrip("/")
                            if img_name.startswith("callproof-static/"):
                                img_name = img_name.replace("callproof-static/", "", 1)
                            
                            src_path = os.path.join(settings.MEDIA_ROOT, img_name)
                            
                            if os.path.exists(src_path):
                                filename = os.path.basename(ct.image.name)
                                rel_path = f"images/contact_types/{self.target_company.id}/{filename}"
                                new_file_path = os.path.join(settings.MEDIA_ROOT, rel_path)
                                os.makedirs(os.path.dirname(new_file_path), exist_ok=True)
                                
                                with open(src_path, "rb") as f:
                                    new_ct.image.save(filename, File(f), save=False)
                                new_ct.save(update_fields=["image"])
                                
                                logger.info(f"Copied ContactType image: {new_ct.image.name}")
                        except Exception as e:
                            logger.error(f"Error copying ContactType image: {e}")
                else:
                    self.contact_type_index[ct.id] = existing_ct.id
                    
            except Exception as e:
                logger.error(f"Error copying ContactType {ct.name}: {e}")

    def _check_contact_exists(self, contact) -> Optional[Contact]:
        """Check if contact already exists in target company with multiple matching strategies"""
        base_filters = {'company': self.target_company}
        
        # Strategy 1: Exact email match (strongest indicator)
        if contact.email and contact.email.strip():
            email_match = Contact.objects.filter(
                **base_filters,
                email__iexact=contact.email.strip()
            ).first()
            if email_match:
                logger.info(f"Found existing contact by email: {email_match.first_name} {email_match.last_name}")
                return email_match
        
        # Strategy 2: Full name + optional additional data
        if contact.first_name and contact.last_name:
            name_filters = {
                **base_filters,
                'first_name__iexact': contact.first_name.strip(),
                'last_name__iexact': contact.last_name.strip()
            }
            
            # Try name + email first (if email exists but didn't match above, might be different emails)
            if contact.email and contact.email.strip():
                name_email_match = Contact.objects.filter(
                    **name_filters,
                    email__iexact=contact.email.strip()
                ).first()
                if name_email_match:
                    logger.info(f"Found existing contact by name+email: {name_email_match.first_name} {name_email_match.last_name}")
                    return name_email_match
            
            # Try just name match
            name_match = Contact.objects.filter(**name_filters).first()
            if name_match:
                # Additional validation for name-only matches to reduce false positives
                if self._validate_name_match(contact, name_match):
                    logger.info(f"Found existing contact by name: {name_match.first_name} {name_match.last_name}")
                    return name_match
        
        # Strategy 3: Strong address match (only if we have comprehensive address data)
        if self._has_strong_address_data(contact):
            address_match = self._find_by_address(contact, base_filters)
            if address_match:
                logger.info(f"Found existing contact by address: {address_match.first_name} {address_match.last_name}")
                return address_match
        
        logger.debug(f"No existing contact found for: {contact.first_name} {contact.last_name} - {contact.email}")
        return None

    def _validate_name_match(self, new_contact, existing_contact) -> bool:
        """Additional validation for name-only matches to reduce false positives"""
        
        # If we have email data for both, they should match
        if (new_contact.email and new_contact.email.strip() and 
            existing_contact.email and existing_contact.email.strip()):
            return new_contact.email.strip().lower() == existing_contact.email.strip().lower()
        
        # If we have strong address data for both, check for match
        if (self._has_strong_address_data(new_contact) and 
            self._has_strong_address_data(existing_contact)):
            return self._addresses_match(new_contact, existing_contact)
        
        # If we only have name data, accept the match (might want to make this configurable)
        return True

    def _has_strong_address_data(self, contact) -> bool:
        """Check if contact has enough address data for reliable matching"""
        address_components = [
            contact.address and contact.address.strip(),
            contact.city and contact.city.strip(),
            contact.state,
            contact.zip and contact.zip.strip()
        ]
        
        # Require at least address + city + (state or zip)
        has_address = bool(address_components[0])
        has_city = bool(address_components[1])
        has_location = bool(address_components[2] or address_components[3])
        
        return has_address and has_city and has_location

    def _find_by_address(self, contact, base_filters) -> Optional[Contact]:
        """Find contact by comprehensive address match"""
        address_filters = base_filters.copy()
        
        if contact.address and contact.address.strip():
            address_filters['address__iexact'] = contact.address.strip()
        
        if contact.city and contact.city.strip():
            address_filters['city__iexact'] = contact.city.strip()
        
        if contact.state:
            address_filters['state'] = contact.state
        
        if contact.zip and contact.zip.strip():
            address_filters['zip__iexact'] = contact.zip.strip()
        
        try:
            return Contact.objects.filter(**address_filters).first()
        except Exception as e:
            logger.error(f"Error checking for existing contact by address: {e}")
            return None

    def _addresses_match(self, contact1, contact2) -> bool:
        """Compare two contacts' addresses for similarity"""
        # Normalize and compare key address components
        def normalize_addr(addr):
            return addr.strip().lower() if addr else ""
        
        address_match = normalize_addr(contact1.address) == normalize_addr(contact2.address)
        city_match = normalize_addr(contact1.city) == normalize_addr(contact2.city)
        
        # State comparison (handle both ForeignKey and string cases)
        state_match = True
        if contact1.state and contact2.state:
            if hasattr(contact1.state, 'id') and hasattr(contact2.state, 'id'):
                state_match = contact1.state.id == contact2.state.id
            else:
                state_match = str(contact1.state).lower() == str(contact2.state).lower()
        
        zip_match = normalize_addr(contact1.zip) == normalize_addr(contact2.zip)
        
        # Require address + city match, plus either state or zip
        return address_match and city_match and (state_match or zip_match)

    @transaction.atomic
    def copy_contacts(self):
        """Copy contacts and all related data"""
        logger.info(f"Starting contact copy for user {self.source_user.id} -> {self.target_user.id}")
        
        # First copy ContactTypes
        self._copy_contact_types()
        
        # Get contacts created by source user
        user_contacts = Contact.objects.filter(
            company=self.source_company,
            created_by=self.source_user
        ).select_related('contact_company', 'contact_type', 'created_by')
        
        logger.info(f"Found {user_contacts.count()} contacts created by source user")
        
        for contact in user_contacts:
            try:
                # Check if contact already exists
                existing_contact = self._check_contact_exists(contact)
                if existing_contact:
                    logger.info(f"Contact already exists, updating: {existing_contact.id}")
                    target_contact = existing_contact
                    self.stats.contacts_updated += 1
                else:
                    # Create new contact
                    target_contact = self._create_new_contact(contact)
                    if not target_contact:
                        continue
                    self.stats.contacts_created += 1
                
                # Store mapping
                self.contact_index[contact.id] = target_contact.id
                self.stats.contacts_copied += 1
                
                # Copy all related data
                self._copy_contact_related_data(contact, target_contact)
                
            except Exception as e:
                error_msg = f"Error processing contact {contact.id}: {e}"
                logger.error(error_msg)
                self.stats.errors.append(error_msg)
                self.stats.contacts_skipped += 1
                continue
        
        logger.info(f"Contact copy completed. Created: {self.stats.contacts_created}, Updated: {self.stats.contacts_updated}")

    def _create_new_contact(self, contact) -> Optional[Contact]:
        """Create a new contact in target company"""
        try:
            target_contact_company = self._get_or_create_contact_company(getattr(contact, 'contact_company', None))
            target_contact_type = self._get_target_contact_type(contact)
            if not target_contact_type:
                logger.warning(f"No valid contact_type found for contact {getattr(contact, 'id', 'unknown')}")
                return None

            contact_fields = self._get_contact_fields_with_defaults(contact)
            contact_fields.update({
                'company': self.target_company,
                'created_by': self.target_user,
                'contact_type': target_contact_type,
                'contact_company': target_contact_company,
                'created': timezone.now(),
                'updated': timezone.now(),
            })

            new_contact = Contact.objects.create(**contact_fields)
            #update the contact company's primary contact if not set
            if target_contact_company and not target_contact_company.primary_contact:
                target_contact_company.primary_contact = new_contact
                target_contact_company.save(update_fields=['primary_contact'])
                
            self._copy_contact_image(contact, new_contact)
            logger.info(f"Created new contact: {getattr(new_contact, 'first_name', '')} {getattr(new_contact, 'last_name', '')}")
            return new_contact

        except Exception as e:
            logger.error(f"Error creating new contact: {e}")
            return None

    def _get_target_contact_type(self, contact):
        """Get the target contact type for the new contact"""
        target_contact_type = None
        contact_type = getattr(contact, 'contact_type', None)
        if contact_type:
            target_contact_type_id = self.contact_type_index.get(contact_type.id)
            if target_contact_type_id:
                try:
                    target_contact_type = ContactType.objects.get(pk=target_contact_type_id)
                except ContactType.DoesNotExist:
                    target_contact_type = None
        if not target_contact_type:
            target_contact_type = ContactType.objects.filter(
                company=self.target_company,
                is_default=True
            ).first() or ContactType.objects.filter(
                company=self.target_company
            ).order_by('position').first()
        return target_contact_type

    def _get_contact_fields_with_defaults(self, contact):
        """Return a dict of contact fields with safe defaults if missing"""
        fields = [
            'first_name', 'last_name', 'email', 'title', 'city', 'state', 'zip', 'country',
            'address', 'address2', 'website', 'latitude', 'longitude', 'last_contacted',
            'account', 'invoice', 'last_geocode', 'geocode_count', 'unknown', 'assigned',
            'do_not_sms', 'place', 'district', 'sales_type', 'related_esn', 'related_product',
            'handset_type', 'sync_with_ac', 'zap_facebook_lead', 'business_type',
            'employee_count', 'annual_sales', 'county', 'is_pinned', 'position'
        ]
        defaults = {
            'first_name': '', 'last_name': '', 'email': '', 'title': '', 'city': '', 'state': '', 'zip': '', 'country': '',
            'address': '', 'address2': '', 'website': '', 'latitude': None, 'longitude': None, 'last_contacted': None,
            'account': '', 'invoice': '', 'last_geocode': None, 'geocode_count': 0, 'unknown': False, 'assigned': False,
            'do_not_sms': False, 'place': None, 'district': '', 'sales_type': '', 'related_esn': '', 'related_product': '',
            'handset_type': '', 'sync_with_ac': False, 'zap_facebook_lead': False, 'business_type': '',
            'employee_count': '', 'annual_sales': '', 'county': '', 'is_pinned': False, 'position': 0
        }
        result = {}
        for field in fields:
            result[field] = getattr(contact, field, defaults[field])
        return result

    def _copy_contact_image(self, contact, new_contact):
        """Copy the contact image if it exists"""
        image = getattr(contact, 'image', None)
        if image and getattr(image, 'name', None):
            try:
                filename = os.path.basename(image.name)
                src_path = getattr(image, 'path', None)
                if src_path and os.path.exists(src_path):
                    with open(src_path, 'rb') as f:
                        new_contact.image.save(filename, File(f), save=True)
                    logger.info(f"Copied contact image: {filename}")
            except Exception as e:
                logger.error(f"Error copying contact image: {e}")

    def _copy_contact_related_data(self, source_contact, target_contact):
        """Copy all contact-related data"""
        try:
            self._copy_contact_phones(source_contact, target_contact)
            self._copy_contact_notes(source_contact, target_contact)
            self._copy_contact_images(source_contact, target_contact)
            self._copy_contact_labels(source_contact, target_contact)
            self._copy_info_email(source_contact, target_contact)
            self._copy_contact_regular_fields_states()   
            self._copy_contact_list_cust()
            self._copy_contact_personnel(source_contact, target_contact)
            self._copy_contact_reps(source_contact, target_contact)
            self._copy_contact_research(source_contact, target_contact)
            self._copy_contact_stores(source_contact, target_contact)
            self._copy_contact_user_files(source_contact, target_contact)
            self._copy_contact_custom_fields(source_contact, target_contact)
           
            try:
                self._copy_event_forms(self.source_company, self.target_company, source_contact, target_contact)
                logger.info("Event form data copy completed successfully!")
            except Exception as e:
                error_msg = f"Error copying event forms: {e}"
                logger.error(error_msg)
                self.stats.errors.append(error_msg)

            try:
                self._copy_appointments(self.source_company, self.target_company, source_contact, target_contact)
                logger.info("Appointment data copy completed successfully!")
            except Exception as e:
                error_msg = f"Error copying appointments: {e}"
                logger.error(error_msg)
                self.stats.errors.append(error_msg)
            logger.info(f"Successfully copied all related data for contact {source_contact.id}")
        except Exception as e:
            logger.error(f"Error copying contact related data: {e}")

    def _copy_contact_list_cust(self):
        for clc in ContactListCust.objects.filter(company=self.source_company):
            # This model doesn't have a direct contact FK, copying by company
            try:
                existing = ContactListCust.objects.filter(
                    company=self.target_company,
                    contact_name=clc.contact_name,
                    company_name=clc.company_name
                ).exists()
                
                if not existing:
                    ContactListCust.objects.create(
                        company=self.target_company,
                        contact_name=clc.contact_name,
                        company_name=clc.company_name,
                        address=clc.address,
                        phone_distance=clc.phone_distance,
                        contacted=clc.contacted,
                        sales_rep=clc.sales_rep,
                        last_appointment=clc.last_appointment
                    )
            except Exception as e:
                logger.error(f"Error copying ContactListCust: {e}")

    def _copy_contact_phones(self, source_contact, target_contact):
        """Copy ContactPhone records"""
        phones = ContactPhone.objects.filter(contact=source_contact)
        for phone in phones:
            try:
                # Safely get phone number with better handling
                phone_number_raw = getattr(phone, 'phone_number', '')
                
                # Handle None and convert to string safely
                if phone_number_raw is None:
                    phone_number_str = ''
                else:
                    # Convert to string, handling various types
                    phone_number_str = str(phone_number_raw) if phone_number_raw is not None else ''
                
                # Clean the phone number - remove non-digit characters except optional '+' prefix
                if phone_number_str:
                    # Keep + if present at start, then remove all non-digits
                    if phone_number_str.startswith('+'):
                        cleaned = '+' + ''.join(filter(str.isdigit, phone_number_str[1:]))
                    else:
                        cleaned = ''.join(filter(str.isdigit, phone_number_str))
                    phone_number = self._safe_str_slice(cleaned, 15)
                else:
                    phone_number = ''
                
                # Safely handle extension
                ext_raw = getattr(phone, 'ext', '')
                print(f"Raw extension value: {repr(ext_raw)} (type: {type(ext_raw)})")
                if ext_raw is None:
                    ext_str = ''
                else:
                    ext_str = str(ext_raw) if ext_raw is not None else ''
                ext = self._safe_str_slice(ext_str, 15)
                print(f"Processed extension value: {repr(ext)} (type: {type(ext)})")
                # Skip if no phone number or if it already exists
                if not phone_number or self._phone_exists(target_contact, phone_number):
                    continue
                    
                phone_type = self._get_phone_type(phone)
                new_phone = self._create_contact_phone(phone, target_contact, phone_number, ext, phone_type)
                self.contact_phone_index[phone.id] = new_phone.id
                is_default_contact_phone = Contact.objects.filter(default_phone=phone, id=source_contact.id).exists()
                if is_default_contact_phone:
                    target_contact.default_phone = new_phone
                    target_contact.save(update_fields=['default_phone'])
                self.stats.phones_copied += 1
                self._copy_contact_phone_labels(phone, new_phone)
                
            except Exception as e:
                logger.exception(f"Full exception trace: {e}")
                logger.error(f"Error copying phone {getattr(phone, 'phone_number', 'unknown')}: {e}")
                # Log more details about the problematic phone object
                logger.debug(f"Phone object details: id={getattr(phone, 'id', 'unknown')}, "
                            f"phone_number type={type(getattr(phone, 'phone_number', None))}, "
                            f"phone_number value={repr(getattr(phone, 'phone_number', None))}")
    
    def _safe_str_slice(self, value, length):
        """Safely slice a string value if it's a string, else return empty string"""
        if value is None:
            return ''
        
        try:
            if isinstance(value, (str, int, float)):
                return str(value)[:length]
            else:
                return ''
        except Exception:
            return ''

    def _phone_exists(self, target_contact, phone_number):
        """Check if phone already exists for the target contact"""
        if not phone_number:  # Skip check if phone number is empty
            return True
            
        try:
            return ContactPhone.objects.filter(
                contact=target_contact,
                phone_number=phone_number,
                company=self.target_company
            ).exists()
        except Exception as e:
            logger.error(f"Error checking phone existence: {e}")
            return True  # Return True to skip creation if there's an error

    def _get_phone_type(self, phone):
        """Get the phone type object for the target company"""
        if getattr(phone, 'phone_type', None) and getattr(phone.phone_type, 'name', None):
            return PhoneType.objects.filter(name=phone.phone_type.name).first()
        return None

    def _create_contact_phone(self, phone, target_contact, phone_number, ext, phone_type):
        """Create a new ContactPhone record, with detailed logging for all fields."""
        def get_field(phone, field, default=None):
            return getattr(phone, field, default) or default

        def get_bool_field(phone, field):
            return bool(getattr(phone, field, False))

        def get_datetime_field(phone, field):
            """Safely get datetime field from phone object"""
            value = getattr(phone, field, None)
            return self._normalize_datetime(value)

        # Gather all field values and types for logging
        field_values = {
            "company": self.target_company,
            "contact": target_contact,
            "phone_number": phone_number,
            "phone_type": phone_type,
            "country_code": get_field(phone, 'country_code', ''),
            "ext": ext,
            # Properly normalize DateFields
            "activated": get_datetime_field(phone, 'activated'),
            "eligible": get_datetime_field(phone, 'eligible'),
            "lookup_updated_on": get_datetime_field(phone, 'lookup_updated_on'),
            "last_contacted": get_datetime_field(phone, 'last_contacted'),
            "hidden": get_bool_field(phone, 'hidden'),
            "carrier_name": get_field(phone, 'carrier_name', ''),
            "caller_name": get_field(phone, 'caller_name', ''),
            "do_not_call": get_bool_field(phone, 'do_not_call'),
            "model": get_field(phone, 'model', ''),
            "unknown": get_bool_field(phone, 'unknown'),
            "created": get_datetime_field(phone, 'created') or timezone.now(),
            "updated": get_datetime_field(phone, 'updated') or timezone.now(),
            "call_count": getattr(phone, 'call_count', 0) or 0,
            "is_dealer_imported": get_bool_field(phone, 'is_dealer_imported'),
            "imported_date": get_datetime_field(phone, 'imported_date'),
            "description": get_field(phone, 'description', ''),
            "is_active_lead": get_bool_field(phone, 'is_active_lead'),
            "is_in_dnd": get_bool_field(phone, 'is_in_dnd'),
            "is_in_dnc": get_bool_field(phone, 'is_in_dnc'),
            "user": self.target_user,
            "forward_incoming_to": get_field(phone, 'forward_incoming_to', ''),
            "fcc_complain": get_bool_field(phone, 'fcc_complain'),
        }

        # Log all field values and their types
        for k, v in field_values.items():
            logger.info(f"_create_contact_phone: {k} = {repr(v)} (type: {type(v)})")

        return ContactPhone.objects.create(**field_values)

    def _normalize_datetime(self, value):
        """Normalize datetime values for database insertion, with robust type checking and logging."""
        if value is None:
            return None
        if isinstance(value, (datetime, date)):
            return value
        if isinstance(value, str) and value.strip():
            # Try to parse string datetime
            try:
                from django.utils.dateparse import parse_datetime, parse_date
                parsed = parse_datetime(value) or parse_date(value)
                return parsed
            except (ValueError, TypeError):
                logger.warning(f"_normalize_datetime: Failed to parse string value: {repr(value)}")
                return None
        # If value is not a string, datetime, or date, log and return None
        logger.warning(f"_normalize_datetime: Unexpected type {type(value)} for value: {repr(value)}. Returning None.")
        return None

    def _copy_contact_phone_labels(self, source_phone, target_phone):
        """Copy ContactPhoneLabel records"""
        phone_labels = ContactPhoneLabel.objects.filter(contact_phone=source_phone)
        
        for pl in phone_labels:
            try:
                if not pl.label:
                    continue
                    
                # Get or create label in target company
                target_label = Label.objects.filter(
                    company=self.target_company,
                    name=pl.label.name
                ).first()
                
                if not target_label:
                    target_label = Label.objects.create(
                        company=self.target_company,
                        name=pl.label.name
                    )
                
                if not ContactPhoneLabel.objects.filter(
                    contact_phone=target_phone,
                    label=target_label
                ).exists():
                    ContactPhoneLabel.objects.create(
                        contact_phone=target_phone,
                        label=target_label
                    )
            except Exception as e:
                logger.error(f"Error copying phone label: {e}")

    def _copy_contact_notes(self, source_contact, target_contact):
        """Copy ContactNote records"""
        notes = ContactNote.objects.filter(contact=source_contact, user=self.source_user)
        
        for note in notes:
            try:
                if not ContactNote.objects.filter(
                    company=self.target_company,
                    contact=target_contact,
                    user=self.target_user,
                    note=note.note,
                    created=note.created
                ).exists():
                    ContactNote.objects.create(
                        company=self.target_company,
                        contact=target_contact,
                        note=note.note,
                        user=self.target_user,
                        created=note.created or timezone.now()
                    )
                    self.stats.notes_copied += 1
            except Exception as e:
                logger.error(f"Error copying contact note: {e}")

    def _copy_contact_images(self, source_contact, target_contact):
        """Copy ContactImage records"""
        images = ContactImage.objects.filter(contact=source_contact)
        
        for img in images:
            try:
                if not ContactImage.objects.filter(
                    contact=target_contact,
                    image=img.image
                ).exists():
                    ContactImage.objects.create(
                        company=self.target_company,
                        user=self.target_user,
                        contact=target_contact,
                        business_card=img.business_card if img.business_card else None,
                        image=img.image,
                        created=img.created or timezone.now()
                    )
                    self.stats.images_copied += 1
            except Exception as e:
                logger.error(f"Error copying contact image: {e}")

    def _copy_contact_labels(self, source_contact, target_contact):
        """Copy ContactLabel records"""
        labels = ContactLabel.objects.filter(contact=source_contact)
        
        for cl in labels:
            try:
                if not cl.label:
                    continue
                    
                # Get or create label in target company
                target_label = Label.objects.filter(
                    company=self.target_company,
                    name=cl.label.name
                ).first()
                
                if not target_label:
                    target_label = Label.objects.create(
                        company=self.target_company,
                        name=cl.label.name
                    )
                
                if not ContactLabel.objects.filter(
                    contact=target_contact,
                    label=target_label
                ).exists():
                    ContactLabel.objects.create(
                        contact=target_contact,
                        label=target_label
                    )
                    self.stats.labels_copied += 1
            except Exception as e:
                logger.error(f"Error copying contact label: {e}")

    def _copy_contact_personnel(self, source_contact, target_contact):
        """Copy ContactPersonnel records"""
        personnels = ContactPersonnel.objects.filter(contact=source_contact)

        for cp in personnels:
            try:
                peoplerole = self._get_or_create_peoplerole(cp)
                if not self._personnel_exists(target_contact, cp):
                    new_personnel = self._create_personnel(target_contact, cp, peoplerole)
                    self._copy_personnel_image(cp, new_personnel)
                    self.stats.personnel_copied += 1
                    reverse_index = {v: k for k, v in self.contact_index.items()}
                    source_contact_id = reverse_index.get(target_contact.id)
                    for cpp in ContactPhonePersonnel.objects.filter(contactphone__contact=source_contact_id):
                        try:
                            # Find corresponding target contact phone
                            target_contact_phone = ContactPhone.objects.filter(
                                contact=target_contact,
                                phone_number=cpp.contactphone.phone_number
                            ).first()
                            
                            # Find corresponding target personnel
                            target_personnel = ContactPersonnel.objects.filter(
                                contact=target_contact,
                                first_name=cpp.personnel.first_name,
                                last_name=cpp.personnel.last_name
                            ).first()
                            
                            if target_contact_phone and target_personnel:
                                if not ContactPhonePersonnel.objects.filter(
                                    contactphone=target_contact_phone,
                                    personnel=target_personnel
                                ).exists():
                                    ContactPhonePersonnel.objects.create(
                                        contactphone=target_contact_phone,
                                        personnel=target_personnel,
                                        extension=cpp.extension
                                    )
                        except Exception as e:
                            logger.error(f"Error copying ContactPhonePersonnel: {e}")
                            continue
            except Exception as e:
                logger.error(f"Error copying contact personnel: {e}")

    def _get_or_create_peoplerole(self, cp):
        """Get or create PeopleRole for personnel"""
        if not getattr(cp, 'peoplerole', None):
            return None
        peoplerole = PeopleRole.objects.filter(
            company=self.target_company,
            name=cp.peoplerole.name
        ).first()
        if not peoplerole:
            peoplerole = PeopleRole.objects.create(
                company=self.target_company,
                name=cp.peoplerole.name
            )
        return peoplerole

    def _personnel_exists(self, target_contact, cp):
        """Check if personnel already exists for target contact"""
        return ContactPersonnel.objects.filter(
            contact=target_contact,
            first_name=cp.first_name,
            last_name=cp.last_name
        ).exists()

    def _create_personnel(self, target_contact, cp, peoplerole):
        """Create a new ContactPersonnel record, handling moved_to field properly"""
        # Fix for moved_to: set to None if empty or not a valid int
        moved_to_value = getattr(cp, 'moved_to', None)
        if moved_to_value in [None, '', 0]:
            moved_to = None
        else:
            try:
                moved_to = int(moved_to_value)
            except (ValueError, TypeError):
                moved_to = None

        return ContactPersonnel.objects.create(
            company=self.target_company,
            contact=target_contact,
            first_name=cp.first_name or '',
            last_name=cp.last_name or '',
            email=cp.email or '',
            personnel_notes=cp.personnel_notes or '',
            cell_phone=cp.cell_phone or '',
            title=cp.title or '',
            peoplerole=peoplerole,
            last_contacted=cp.last_contacted,
            is_disabled=cp.is_disabled or False,
            moved_to=moved_to,
            created=cp.created or timezone.now(),
            updated=cp.updated or timezone.now()
        )

    def _copy_personnel_image(self, cp, new_personnel):
        """Copy personnel image if exists"""
        if getattr(cp, 'image', None) and getattr(cp.image, 'name', None):
            try:
                filename = os.path.basename(cp.image.name)
                src_path = cp.image.path
                with open(src_path, 'rb') as f:
                    new_personnel.image.save(filename, File(f), save=True)
            except Exception as e:
                logger.error(f"Error copying personnel image: {e}")

    def _copy_contact_reps(self, source_contact, target_contact):
        """Copy ContactRep records"""
        reps = ContactRep.objects.filter(contact=source_contact)
        
        for cr in reps:
            try:
                # Map user - if it's source user, use target user
                target_user_obj = self.target_user if cr.user == self.source_user else cr.user
                
                if not ContactRep.objects.filter(
                    contact=target_contact,
                    user=target_user_obj
                ).exists():
                    ContactRep.objects.create(
                        contact=target_contact,
                        user=target_user_obj,
                        created=cr.created or timezone.now()
                    )
                    self.stats.reps_copied += 1
            except Exception as e:
                logger.error(f"Error copying contact rep: {e}")

    def _copy_contact_research(self, source_contact, target_contact):
        """Copy ContactResearch records"""
        researches = ContactResearch.objects.filter(contact=source_contact)
        
        for cres in researches:
            try:
                # Map user
                target_user_obj = self.target_user if cres.user == self.source_user else cres.user
                
                # Map store if exists
                target_store = None
                if cres.store:
                    target_store = DealerStore.objects.filter(
                        company=self.target_company,
                        name=cres.store.name
                    ).first()
                
                if not ContactResearch.objects.filter(
                    contact=target_contact,
                    user=target_user_obj,
                    first_name=cres.first_name,
                    last_name=cres.last_name
                ).exists():
                    ContactResearch.objects.create(
                        user=target_user_obj,
                        contact=target_contact,
                        store=target_store,
                        company=self.target_company,
                        first_name=cres.first_name or '',
                        last_name=cres.last_name or '',
                        email=cres.email or '',
                        phone_number=cres.phone_number or '',
                        eligible=cres.eligible or False,
                        created=cres.created or timezone.now()
                    )
                    self.stats.research_copied += 1
            except Exception as e:
                logger.error(f"Error copying contact research: {e}")

    def _copy_contact_stores(self, source_contact, target_contact):
        """Copy ContactStore records"""
        stores = ContactStore.objects.filter(contact=source_contact)
        
        for cs in stores:
            try:
                # Get or create store in target company
                target_store = DealerStore.objects.filter(
                    company=self.target_company,
                    name=cs.store.name
                ).first()
                
                if not target_store:
                    target_store = DealerStore.objects.create(
                        company=self.target_company,
                        name=cs.store.name,
                        address=cs.store.address or '',
                        city=cs.store.city or '',
                        state=cs.store.state or '',
                        zip=cs.store.zip or '',
                        country=cs.store.country or '',
                        latitude=cs.store.latitude,
                        longitude=cs.store.longitude
                    )
                
                if not ContactStore.objects.filter(
                    contact=target_contact,
                    store=target_store
                ).exists():
                    ContactStore.objects.create(
                        contact=target_contact,
                        store=target_store,
                        created=cs.created or timezone.now()
                    )
                    self.stats.stores_copied += 1
            except Exception as e:
                logger.error(f"Error copying contact store: {e}")

    def _copy_contact_user_files(self, source_contact, target_contact):
        """Copy ContactUserFile records"""
        user_files = ContactUserFile.objects.filter(contact=source_contact)
        
        for cuf in user_files:
            try:
                if not ContactUserFile.objects.filter(
                    contact=target_contact,
                    user_file=cuf.user_file
                ).exists():
                    old_user_file = cuf.user_file
                    if old_user_file:
                        user_file = UserFile(company=self.target_company,
                                    user=self.target_user,
                                    filename=str(old_user_file.filename),
                                    filepath=old_user_file.filepath,
                                    created=timezone.now(),
                                    updated=timezone.now())
                        user_file.save()
                        ContactUserFile.objects.create(
                            company=self.target_company,
                            contact=target_contact,
                            user_file=user_file,
                            account=cuf.account if cuf.account else None,
                            email_msg=cuf.email_msg if getattr(cuf, 'email_msg', None) else None
                        )
            except Exception as e:
                logger.error(f"Error copying contact user file: {e}")

    def _copy_contact_custom_fields(self, source_contact, target_contact):
        """Copy custom fields (CFieldValue and CFieldMultiValue) for contacts using CustomFieldService"""
        try:
            # Use the enhanced CustomFieldService-based approach for proper field handling
            self.custom_field_handler.copy_custom_fields_using_service(
                source_contact.id, 
                target_contact.id, 
                'contact',
                source_entity=source_contact,
                target_entity=target_contact
            )
            
            # Update our stats from the handler's stats
            handler_stats = self.custom_field_handler.get_stats()
            self.stats.custom_fields_copied += (
                handler_stats['custom_fields_copied'] + 
                handler_stats.get('custom_field_values_copied', 0) + 
                handler_stats.get('custom_field_multi_values_copied', 0)
            )
            
        except Exception as e:
            logger.error(f"Error copying contact custom fields: {e}")
            import traceback
            logger.error(f"Traceback: {traceback.format_exc()}")

    def copy_all_contact_data(self) -> ContactStats:
        """Execute the complete contact copy process"""
        logger.info(f"Starting contact data copy:")
        logger.info(f"From: {self.source_company.name} (User: {self.source_user.first_name} {self.source_user.last_name})")
        logger.info(f"To: {self.target_company.name} (User: {self.target_user.first_name} {self.target_user.last_name})")
        logger.info("-" * 80)
        
        try:
            # First copy company-level custom field configurations
            self._copy_company_custom_field_configs()
            logger.info("Company custom field configurations copied successfully!")
            
            self.copy_contacts()
            logger.info("Contact data copy completed successfully!")

            try:
                self.copy_user_opportunities()
                logger.info("Opportunity copy completed successfully!")
            except Exception as e:
                error_msg = f"Error copying opportunities: {e}"
                logger.error(error_msg)
                self.stats.errors.append(error_msg)
            
            try:
                self.copy_user_followups()
                logger.info("Followup copy completed successfully!")
            except Exception as e:
                error_msg = f"Error copying followups: {e}"
                logger.error(error_msg)
                self.stats.errors.append(error_msg)
                
        except Exception as e:
            error_msg = f"Error during contact copy process: {e}"
            logger.error(error_msg)
            self.stats.errors.append(error_msg)
        
        return self.stats

    def _copy_company_custom_field_configs(self):
        """Copy company-level custom field configurations"""
        try:
            logger.info("Copying company-level custom field configurations...")
            
            # Copy OppFormCField configurations
            self.custom_field_handler.copy_opp_form_cfields()
            
            # Copy CFieldAuto configurations for all table types
            self.custom_field_handler.copy_cfield_autos('contact')
            self.custom_field_handler.copy_cfield_autos('event_form') 
            self.custom_field_handler.copy_cfield_autos('opp')
            
            # Get updated stats
            handler_stats = self.custom_field_handler.get_stats()
            logger.info(f"Copied {handler_stats['custom_field_autos_copied']} CFieldAuto configurations")
            
        except Exception as e:
            logger.error(f"Error copying company custom field configurations: {e}")
    
    def _copy_info_email(self,source_contact, target_contact):
        try:
            for cie in ContactInfoEmail.objects.filter(contact=source_contact):
                try:
                    if not ContactInfoEmail.objects.filter(
                        contact=target_contact,
                        email=cie.email
                    ).exists():
                        ContactInfoEmail.objects.create(
                            company=self.target_company,
                            contact=target_contact,
                            email=cie.email,
                            created=cie.created or timezone.now(),
                            updated=cie.updated or timezone.now()
                        )
                except Exception as e:
                    logger.error(f"Error copying ContactInfoEmail: {e}")
        except Exception as e:
            logger.error('Error Copying ContactInfoEmail')

    def _copy_contact_regular_fields_states(self):
        for crfs in ContactRegularFieldsStates.objects.filter(company_id=self.source_company.id):
            try:
                if not ContactRegularFieldsStates.objects.filter(
                    crfield=crfs.crfield,
                    c_rfield_id=crfs.c_rfield_id,
                                company_id=self.target_company.id
                            ).exists():
                                ContactRegularFieldsStates.objects.create(
                                    crfield=crfs.crfield,
                                    c_rfield_id=crfs.c_rfield_id,
                                    c_state=crfs.c_state,
                                    company_id=self.target_company.id
                                )
            except Exception as e:
                logger.error(f"Error copying ContactRegularFieldsStates: {e}")

    @transaction.atomic
    def copy_user_opportunities(self):
        """Copy opportunities created by the source user"""
        logger.info(f"[{datetime.now()}] Copying opportunities for user {self.source_user.id} -> {self.target_user.id}")
        
        user_opps = Opp.objects.filter(
            company=self.source_company,
            user=self.source_user
        ).select_related('contact', 'opp_stage', 'opp_type')
        
        logger.info(f"Found {user_opps.count()} opportunities by user {self.source_user.id}")
        
        for opp in user_opps:
            try:
                # Check if contact was copied
                target_contact_id = self.contact_index.get(opp.contact.id)
                if not target_contact_id:
                    logger.info(f"Skipping opportunity {opp.id} - contact {opp.contact.id} not found in mapping")
                    continue
                
                target_contact = Contact.objects.get(pk=target_contact_id)
                
                # Map stage and type
                target_stage = OppStage.objects.filter(
                    company=self.target_company,
                    name=opp.opp_stage.name
                ).first()
                logger.info('Oppstage is filter by company and name')
                target_type = None
                if opp.opp_type:
                    target_type = OppType.objects.filter(
                        company=self.target_company,
                        name=opp.opp_type.name
                    ).first()
                    
                if Opp.objects.filter(
                    company=self.target_company,
                    contact=target_contact,
                    user=self.target_user,
                    opp_name=opp.opp_name,
                    opp_stage=target_stage,
                    opp_type=target_type,
                    probability=opp.probability,
                    notes=opp.notes,
                ).exists():
                    logger.info(f"Opp already exists for contact {target_contact.id} with name {opp.opp_name}, skipping.")
                    continue  


                new_opp = Opp.objects.create(
                    company=self.target_company,
                    user=self.target_user,
                    contact=target_contact,
                    opp_stage=target_stage,
                    opp_type=target_type,
                    probability=opp.probability,
                    value=opp.value,
                    close_date=opp.close_date,
                    notes=opp.notes,
                    opp_name=opp.opp_name,
                    created=opp.created or timezone.now(),
                    updated=opp.updated or timezone.now(),
                )
                logger.info(f'opportunities Related tables copied {new_opp} daata')
                self.stats.opps_copied += 1
                self._copy_opp_related_data(opp, new_opp)
                
                # Copy opportunity custom fields
                self._copy_opp_custom_fields(opp, new_opp)
                
            except Exception as e:
                error_msg = f"Error creating opportunity {opp.id}: {e}"
                logger.error(error_msg)
                if hasattr(self.stats, 'errors') and self.stats.errors is not None:
                    self.stats.errors.append(error_msg)
                continue
    
    def _copy_opp_related_data(self, original_opp, target_opp):
        """Copy opportunity-related data"""
        
        # Copy OppHistory
        try:
            logger.info('OppHistory Table coping...')
            for history in OppHistory.objects.filter(opp=original_opp):
                target_stage = OppStage.objects.filter(
                    company=self.target_company,
                    name=history.opp_stage.name
                ).first()
                
                target_type = None
                if history.opp_type:
                    target_type = OppType.objects.filter(
                        company=self.target_company,
                        name=history.opp_type.name
                    ).first()
                
                new_opp = OppHistory.objects.create(
                    opp=target_opp,
                    opp_stage=target_stage,
                    opp_type=target_type,
                    probability=history.probability,
                    value=history.value,
                    close_date=history.close_date,
                    created=history.created or timezone.now(),
                    notes=history.notes,
                    opp_name=history.opp_name
                )
                logger.info(f'OppHistory table coped  {new_opp}')
                self.stats.opp_histories_copied += 1
        except Exception as e:
            logger.error(f"Error copying OppHistory: {e}")
        
        # Copy OppContact
        try:
            for opp_contact in OppContact.objects.filter(opp=original_opp):
                target_contact_id = self.contact_index.get(opp_contact.contact.id)
                if target_contact_id:
                    target_contact = Contact.objects.get(pk=target_contact_id)
                    
                    if not OppContact.objects.filter(
                        opp=target_opp,
                        contact=target_contact
                    ).exists():
                        OppContact.objects.create(
                            company=self.target_company,
                            opp=target_opp,
                            contact=target_contact,
                            created=opp_contact.created or timezone.now()
                        )
                        self.stats.opp_contacts_copied += 1
        except Exception as e:
            logger.error(f"Error copying OppContact: {e}")
        
        # Copy OppPersonnel
        try:
            for opp_personnel in OppPersonnel.objects.filter(opp=original_opp):
                # Find corresponding personnel in target
                target_personnel = ContactPersonnel.objects.filter(
                    contact__company=self.target_company,
                    first_name=opp_personnel.personnel.first_name,
                    last_name=opp_personnel.personnel.last_name
                ).first()
                
                if target_personnel:
                    OppPersonnel.objects.create(
                        opp=target_opp,
                        personnel=target_personnel
                    )
                    self.stats.opp_personnels_copied += 1
        except Exception as e:
            logger.error(f"Error copying OppPersonnel: {e}")

    def _copy_opp_custom_fields(self, source_opp, target_opp):
        """Copy custom fields for opportunities using CustomFieldService"""
        try:
            # Use the enhanced CustomFieldService-based approach for proper field handling
            self.custom_field_handler.copy_custom_fields_using_service(
                source_opp.id, 
                target_opp.id, 
                'opp',
                source_entity=source_opp,
                target_entity=target_opp
            )
            
            # Update our stats from the handler's stats
            handler_stats = self.custom_field_handler.get_stats()
            self.stats.custom_fields_copied += (
                handler_stats['custom_fields_copied'] + 
                handler_stats.get('custom_field_values_copied', 0) + 
                handler_stats.get('custom_field_multi_values_copied', 0)
            )
            
        except Exception as e:
            logger.error(f"Error copying opportunity custom fields: {e}")

    def print_summary(self):
        """Print summary of copied data"""
        logger.info("=" * 80)
        logger.info("CONTACT DATA COPY SUMMARY")
        logger.info("=" * 80)
        
        logger.info("CONTACT DATA:")
        logger.info(f"  • Contacts: {self.stats.contacts_copied}")
        logger.info(f"  • Contacts Created: {self.stats.contacts_created}")
        logger.info(f"  • Contacts Updated: {self.stats.contacts_updated}")
        logger.info(f"  • Contacts Skipped: {self.stats.contacts_skipped}")
        logger.info(f"  • Contact Types: {self.stats.contact_types_copied}")
        logger.info(f"  • Contact Companies: {self.stats.contact_companies_copied}")
        
        logger.info("\nRELATED DATA:")
        logger.info(f"  • Phone Numbers: {self.stats.phones_copied}")
        logger.info(f"  • Contact Notes: {self.stats.notes_copied}")
        logger.info(f"  • Contact Images: {self.stats.images_copied}")
        logger.info(f"  • Contact Labels: {self.stats.labels_copied}")
        logger.info(f"  • Contact Personnel: {self.stats.personnel_copied}")
        logger.info(f"  • Contact Reps: {self.stats.reps_copied}")
        logger.info(f"  • Contact Research: {self.stats.research_copied}")
        logger.info(f"  • Contact Stores: {self.stats.stores_copied}")
        logger.info(f"  • Custom Fields: {self.stats.custom_fields_copied}")
        logger.info(f"  • Contact Appointments: {self.stats.contact_appointments_copied}")
        logger.info(f"  • Event Forms: {self.stats.event_forms_copied}")
        logger.info(f"  • Contact Event Forms: {self.stats.contact_event_forms_copied}")
        logger.info(f"  • Opportunities: {self.stats.opps_copied}")
        
        # Add custom field handler stats
        handler_stats = self.custom_field_handler.get_stats()
        logger.info("\nCUSTOM FIELD DATA:")
        logger.info(f"  • Custom Fields Created: {handler_stats['custom_fields_copied']}")
        logger.info(f"  • Custom Field Values: {handler_stats['custom_field_values_copied']}")
        logger.info(f"  • Custom Field Multi Values: {handler_stats['custom_field_multi_values_copied']}")
        logger.info(f"  • Custom Field Options: {handler_stats['custom_field_options_copied']}")
        logger.info(f"  • Custom Field Autos: {handler_stats['custom_field_autos_copied']}")
        
        if self.stats.errors:
            logger.info(f"\nERRORS ENCOUNTERED: {len(self.stats.errors)}")
            for error in self.stats.errors[-5:]:  # Show last 5 errors
                logger.info(f"  • {error}")
        
        end_time = time.time()
        total_time = end_time - start_time
        logger.info("=" * 80)
        logger.info(f"Total execution time: {total_time:.2f} seconds")
        logger.info(f"Contact copy service finished at: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        logger.info("=" * 80)

    def _copy_appointments(self, source_company, target_company, source_contact, target_contact):
        self.appointment_index = {}
        self.eform_appointment_index = {}
        source_appointments = Appointment.objects.filter(company=source_company, contact=source_contact)
        logger.info(f"Found {source_appointments.count()} appointments for contact {source_contact.id}")
        for source_appointment in source_appointments:
            try:
                # Check if contact exists in mapping before proceeding
                if source_appointment.contact.id not in self.contact_index:
                    logger.debug(f"Skipping appointment {source_appointment.id} - contact {source_appointment.contact.id} not in mapping")
                    continue

                target_user = self.target_user

                target_event_form = None
                if source_appointment.event_form:
                    try:
                        target_event_form = EventForm.objects.get(
                            company=target_company,
                            name=source_appointment.event_form.name
                        )
                    except EventForm.DoesNotExist:
                        logger.debug(f"EventForm {source_appointment.event_form.name} not found in target company")

                try:
                    new_appointment = Appointment.objects.create(
                        company=target_company,
                        user=target_user,
                        contact=target_contact,
                        start=source_appointment.start,
                        stop=source_appointment.stop,
                        latitude=source_appointment.latitude,
                        longitude=source_appointment.longitude,
                        duration=source_appointment.duration,
                        notes=source_appointment.notes,
                        title=source_appointment.title,
                        address=source_appointment.address,
                        scheduled=source_appointment.scheduled,
                        item_id=source_appointment.item_id,
                        html_link=source_appointment.html_link,
                        event_form=target_event_form,
                        updated=source_appointment.updated,
                        created=source_appointment.created,
                        apt_end_latitude=source_appointment.apt_end_latitude,
                        apt_end_longitude=source_appointment.apt_end_longitude,
                        started_with_plus=source_appointment.started_with_plus,
                        ended_with_plus=source_appointment.ended_with_plus
                    )
                    self.appointment_index[source_appointment.id] = new_appointment.id
                    self.eform_appointment_index[source_appointment.id] = new_appointment.id
                    self.stats.contact_appointments_copied += 1

                except Exception as e:
                    logger.error(f"Error copying appointment {source_appointment.id}: {e}")
                    continue

            except Exception as e:
                logger.error(f"Error processing appointment {source_appointment.id}: {e}")
                continue

    def _copy_event_forms(self, source_company, target_company, source_contact, target_contact):
        """Copy Event Forms and related data from source company to target company"""
        source_contact_event_forms = ContactEventForm.objects.filter(company=source_company, contact=source_contact)
        self.event_form_index = {}
        logger.info(f"Found {source_contact_event_forms.count()} event forms for contact {source_contact.id}")
        for source_contact_event_form in source_contact_event_forms:
            try:
                # Check if contact exists in mapping before proceeding
                if source_contact_event_form.contact.id not in self.contact_index:
                    logger.error(f"Skipping ContactEventForm {source_contact_event_form.id} - contact {source_contact_event_form.contact.id} not in mapping")
                    continue

                target_user = self.target_user

                # Get or create target EventForm
                target_event_form = None
                try:
                    target_event_form = EventForm.objects.filter(
                        name=source_contact_event_form.event_form.name,
                        company=target_company
                    ).first()
                except Exception as e:
                    logger.error(f"Error looking up EventForm: {e}")

                if not target_event_form:
                    try:
                        original_event_form = source_contact_event_form.event_form
                        target_event_form = EventForm.objects.create(
                            company=target_company,
                            name=original_event_form.name,
                            position=original_event_form.position,
                            post_back_url=original_event_form.post_back_url,
                            post_back_secret=original_event_form.post_back_secret,
                            points=original_event_form.points,
                            is_schedule_followup=original_event_form.is_schedule_followup,
                            send_email_to_rep=original_event_form.send_email_to_rep,
                            event_form_treat_as=original_event_form.event_form_treat_as,
                            prefill_data=original_event_form.prefill_data,
                            is_after_call_form=original_event_form.is_after_call_form,
                            hide=original_event_form.hide,
                            post_back_method=original_event_form.post_back_method,
                            is_clickable=original_event_form.is_clickable
                        )
                        self.stats.event_forms_copied += 1

                        # Copy EventFormCFields using CustomFieldHandler
                        self.custom_field_handler.copy_event_form_cfields(
                            source_contact_event_form.event_form, 
                            target_event_form
                        )
                        
                        # Debug the field mapping if there are issues
                        if logger.level <= logging.DEBUG:
                            self.custom_field_handler.debug_event_form_field_mapping(
                                source_contact_event_form.event_form, 
                                target_event_form
                            )
                    except Exception as e:
                        logger.error(f"Error copying EventForm: {e}")
                        continue

                self.event_form_index[source_contact_event_form.event_form.id] = target_event_form.id
                # Handle source event form appointment mapping
                eform_appointment = Appointment.objects.filter(
                    event_form=source_contact_event_form.event_form, 
                    company=source_company
                ).first()
                
                if eform_appointment and eform_appointment.id in self.appointment_index:
                    target_appointment_id = self.appointment_index.get(eform_appointment.id)
                    if target_appointment_id:
                        try:
                            target_appointment = Appointment.objects.get(pk=target_appointment_id)
                            target_appointment.event_form = target_event_form
                            target_appointment.save(update_fields=['event_form_id'])
                            logger.info('Mapped event form appointment with new appointment')
                        except Appointment.DoesNotExist:
                            logger.warning(f'Target appointment {target_appointment_id} not found, skipping event form mapping')
                        except Exception as e:
                            logger.error(f'Error mapping event form appointment: {e}')

                # Copy ContactEventForm
                try:
                    target_contact_event_form = ContactEventForm(
                        company=target_company,
                        user=target_user,
                        contact=target_contact,
                        event_form=target_event_form,
                        created=source_contact_event_form.created,
                        points=source_contact_event_form.points,
                        latitude=source_contact_event_form.latitude,
                        longitude=source_contact_event_form.longitude,
                        completed=source_contact_event_form.completed,
                        completed_date=source_contact_event_form.completed_date,
                    )
                    
                    # Handle appointment mapping for ContactEventForm
                    if source_contact_event_form.appointment:
                        target_appointment_id = self.appointment_index.get(source_contact_event_form.appointment.id)
                        if target_appointment_id:
                            target_contact_event_form.appointment_id = target_appointment_id
                    
                    target_contact_event_form.save()
                    self.stats.contact_event_forms_copied += 1
                    
                    # Copy ContactEventFormPersonnel
                    try:
                        for cefp in ContactEventFormPersonnel.objects.filter(contacteventform=source_contact_event_form):
                            try:
                                if not cefp.personnel:
                                    continue
                                    
                                # Map personnel to target by first/last name on target contact
                                target_personnel = ContactPersonnel.objects.filter(
                                    contact=target_contact,
                                    first_name=cefp.personnel.first_name,
                                    last_name=cefp.personnel.last_name,
                                ).first()
                                
                                if target_personnel and not ContactEventFormPersonnel.objects.filter(
                                    contacteventform=target_contact_event_form,
                                    personnel=target_personnel
                                ).exists():
                                    ContactEventFormPersonnel.objects.create(
                                        contacteventform=target_contact_event_form,
                                        personnel=target_personnel,
                                    )
                                    logger.info('Copied ContactEventFormPersonnel data')
                            except Exception as e:
                                logger.error(f"Error copying ContactEventFormPersonnel: {e}")
                                
                    except Exception as e:
                        logger.error(f"Error copying ContactEventFormPersonnel records: {e}")
                    
                    # Additional appointment mapping check
                    if (
                        source_contact_event_form.appointment is not None and
                        getattr(source_contact_event_form.appointment, "id", None) is not None and
                        source_contact_event_form.appointment.id in self.eform_appointment_index
                    ):
                        try:
                            target_contact_event_form.appointment.id = self.eform_appointment_index[source_contact_event_form.appointment.id]
                            target_contact_event_form.save(update_fields=['appointment_id'])
                            logger.info('Mapped eform appointment with new appointment')
                        except Exception as e:
                            logger.error(f'Error mapping eform appointment: {e}')
                            logger.exception(e)

                    # Copy CFieldValue and CFieldMultiValue entries using CustomFieldService
                    try:
                        self.custom_field_handler.copy_custom_fields_using_service(
                            source_contact_event_form.id,
                            target_contact_event_form.id,
                            'eventform',  # Use 'eventform' as expected by CustomFieldService
                            source_entity=source_contact_event_form,
                            target_entity=target_contact_event_form
                        )
                    except Exception as e:
                        logger.error(f"Error copying custom fields for ContactEventForm {source_contact_event_form.id}: {e}")
                        
                except Exception as e:
                    logger.error(f"Error copying ContactEventForm {source_contact_event_form.id}: {e}")
                    continue
                    
            except Exception as e:
                logger.error(f"Error processing ContactEventForm {source_contact_event_form.id}: {e}")
                continue
        try:
            self._copy_event_form_contact_types()
        except Exception as e:
            logger.error(f"Error in _copy_event_form_contact_types: {e}")

        try:
            self._copy_event_form_contact_types()
        except Exception as e:
            logger.error(f"Error in _copy_event_form_contact_types (second call): {e}")

        try:
            self._copy_event_form_emails()
        except Exception as e:
            logger.error(f"Error in _copy_event_form_emails: {e}")

        try:
            self._copy_report_fields()
        except Exception as e:
            logger.error(f"Error in _copy_report_fields: {e}")

        try:
            self._copy_report_field_group_by()
        except Exception as e:
            logger.error(f"Error in _copy_report_field_group_by: {e}")

    def _copy_event_form_emails(self):
        """Copy EventFormEMail notification settings"""
        try:
            if not hasattr(self, 'event_form_index'):
                logger.error("Event form index not found, skipping email copy")
                return
                
            for source_form_id, target_form_id in self.event_form_index.items():
                source_emails = EventFormEMail.objects.filter(event_form_id=source_form_id)
                target_form = EventForm.objects.get(id=target_form_id)
                
                for efe in source_emails:
                    try:
                        # Check if email already exists
                        existing_email = EventFormEMail.objects.filter(
                            event_form=target_form,
                            email=efe.email
                        ).first()
                        
                        if not existing_email:
                            EventFormEMail.objects.create(
                                event_form=target_form,
                                email=efe.email
                            )
                            logger.info(f"Created EventFormEMail: {efe.email}")
                            
                    except Exception as e:
                        logger.error(f"Error copying EventFormEMail: {e}")
                        
        except Exception as e:
            logger.error(f"Error copying EventForm emails: {e}")

    def _copy_report_fields(self):
        """Copy ReportField records"""
        try:
            if not hasattr(self, 'event_form_index'):
                logger.error("Event form index not found, skipping email copy")
                return
                
            source_report_fields = ReportField.objects.filter(company=self.source_company)
            for report_field in source_report_fields:
                try:
                    # Map EventForm FK
                    target_event_form_id = self.event_form_index.get(report_field.event_form.id)
                    if target_event_form_id:
                        target_event_form = EventForm.objects.get(id=target_event_form_id)
                        
                        # Map EventFormCField FK if exists
                        target_event_form_cfield = None
                        if report_field.event_form_cfield:
                            target_event_form_cfield = EventFormCField.objects.filter(
                                event_form=target_event_form,
                                cfield__name=report_field.event_form_cfield.cfield.name
                            ).first()
                        
                        # Check if ReportField already exists
                        existing_report_field = ReportField.objects.filter(
                            company=self.target_company,
                            event_form=target_event_form,
                            position=report_field.position
                        ).first()
                        
                        if not existing_report_field:
                            ReportField.objects.create(
                                company=self.target_company,
                                report=report_field.report, 
                                event_form=target_event_form,
                                event_form_cfield=target_event_form_cfield,
                                count_entries=report_field.count_entries,
                                report_field_action=report_field.report_field_action,
                                group_by=report_field.group_by,
                                position=report_field.position
                            )
                            logger.info(f"Created ReportField for {target_event_form.name}")
                except Exception as e:
                    logger.error(f"Error copying ReportField: {e}")
        except Exception as e:
            logger.error(f"Error copying ReportFields: {e}")

    def _copy_report_field_group_by(self):
        """Copy ReportFieldGroupBy records"""
        try:
            source_group_bys = ReportFieldGroupBy.objects.filter(company=self.source_company)
            for group_by in source_group_bys:
                try:
                    # Find target ReportField by matching event_form and position
                    target_report_field = ReportField.objects.filter(
                        company=self.target_company,
                        event_form__name=group_by.report_field.event_form.name,
                        position=group_by.report_field.position
                    ).first()
                    
                    if target_report_field:
                        # Find target CFieldOption by name
                        target_cfield_option = CFieldOption.objects.filter(
                            cfield__company=self.target_company,
                            cfield__name=group_by.cfield_option.cfield.name,
                            name=group_by.cfield_option.name
                        ).first()
                        
                        if target_cfield_option:
                            # Check if ReportFieldGroupBy already exists
                            existing_group_by = ReportFieldGroupBy.objects.filter(
                                company=self.target_company,
                                report_field=target_report_field,
                                cfield_option=target_cfield_option
                            ).first()
                            
                            if not existing_group_by:
                                ReportFieldGroupBy.objects.create(
                                    company=self.target_company,
                                    report_field=target_report_field,
                                    cfield_option=target_cfield_option
                                )
                                logger.info(f"Created ReportFieldGroupBy")
                                
                except Exception as e:
                    logger.error(f"Error copying ReportFieldGroupBy: {e}")
                    
        except Exception as e:
            logger.error(f"Error copying ReportFieldGroupBys: {e}")

    def _copy_event_form_contact_types(self):
        """Copy EventFormContactType associations"""
        try:
            if not hasattr(self, 'event_form_index'):
                logger.error("Event form index not found, skipping email copy")
                return
                
            for source_form_id, target_form_id in self.event_form_index.items():
                source_contact_types = EventFormContactType.objects.filter(event_form_id=source_form_id)
                target_form = EventForm.objects.get(id=target_form_id)
                
                for efct in source_contact_types:
                    try:
                        # Find equivalent contact type in target company
                        target_contact_type = ContactType.objects.filter(
                            company=self.target_company,
                            name=efct.contact_type.name
                        ).first()
                        
                        if target_contact_type:
                            # Check if association already exists
                            existing_assoc = EventFormContactType.objects.filter(
                                company=self.target_company,
                                event_form=target_form,
                                contact_type=target_contact_type
                            ).first()
                            
                            if not existing_assoc:
                                EventFormContactType.objects.create(
                                    company=self.target_company,
                                    event_form=target_form,
                                    contact_type=target_contact_type
                                )
                                logger.info("Created EventFormContactType association")
                                
                    except Exception as e:
                        logger.error(f"Error copying EventFormContactType: {e}")
                        
        except Exception as e:
            logger.error(f"Error copying EventForm contact types: {e}")

    @transaction.atomic
    def copy_user_followups(self):
        """Copy followup data for the user's contacts"""
        logger.info(f"[{datetime.now()}] Copying followups for user {self.source_user.id} -> {self.target_user.id}")
        
        # First copy company-level followup configuration
        self._copy_followup_configuration()
        
        # Get followups for contacts that were copied
        copied_contact_ids = list(self.contact_index.keys())
        
        if not copied_contact_ids:
            logger.info("No contacts copied, skipping followups")
            return
        
        user_followups = Followup.objects.filter(
            user=self.source_user,
            contact_id__in=copied_contact_ids
        ).select_related('followup_type', 'stage', 'priority', 'appointment', 'contacteventform', 'contact_phone', 'calendar_event')
        
        logger.info(f"Found {user_followups.count()} followups for user {self.source_user.id}")
        
        for followup in user_followups:
            try:
                target_contact_id = self.contact_index.get(followup.contact_id)
                if not target_contact_id:
                    logger.warning(f"Skipping Followup {followup.id} - contact {followup.contact_id} not found in mapping (required FK)")
                    continue
                
                target_contact = Contact.objects.get(pk=target_contact_id)
                
                # Map related objects
                target_appointment = None
                if followup.appointment:
                    target_appointment_id = self.appointment_index.get(followup.appointment.id)
                    if target_appointment_id:
                        target_appointment = Appointment.objects.get(pk=target_appointment_id)
                
                target_contact_event_form = None
                if followup.contacteventform:
                    target_contact_event_form = ContactEventForm.objects.filter(
                        company=self.target_company,
                        contact=target_contact,
                        event_form__name=followup.contacteventform.event_form.name
                    ).first()
                
                target_contact_phone = None
                if followup.contact_phone:
                    target_contact_phone = ContactPhone.objects.filter(
                        contact=target_contact,
                        phone_number=followup.contact_phone.phone_number
                    ).first()
                
                # Map followup configuration
                target_followup_type = None
                if followup.followup_type:
                    target_followup_type = FollowupType.objects.filter(
                        company=self.target_company,
                        name=followup.followup_type.name
                    ).first()
                    if not target_followup_type:
                        #create new followup type if not exists
                        target_followup_type = FollowupType.objects.create(
                            company=self.target_company,
                            name=followup.followup_type.name,
                            position=followup.followup_type.position,
                            is_default=followup.followup_type.is_default
                        )                       

                target_stage = None
                if followup.stage:
                    target_stage = FollowupStage.objects.filter(
                        company=self.target_company,
                        name=followup.stage.name
                    ).first()
                    if not target_stage:
                        # create new followup stage if not exists
                        target_stage = FollowupStage.objects.create(
                            company=self.target_company,
                            name=followup.stage.name,
                            fg_color=followup.stage.fg_color,
                            bg_color=followup.stage.bg_color,
                            position=followup.stage.position,
                            map_with_not_completed=followup.stage.map_with_not_completed,
                            map_with_completed=followup.stage.map_with_completed,
                            created=followup.stage.created or timezone.now(),
                            updated=followup.stage.updated or timezone.now()
                        )
                
                target_priority = None
                if followup.priority:
                    target_priority = FollowupPriority.objects.filter(
                        name=followup.priority.name
                    ).first()
                
                # CalendarEventFollowups: create or link equivalent
                target_calendar_event = None
                if followup.calendar_event:
                    cef = followup.calendar_event
                    target_calendar_event = CalendarEventFollowups.objects.filter(
                        event_type=cef.event_type,
                        range_type=cef.range_type,
                        number_of_occurrences=cef.number_of_occurrences,
                        days_of_week=cef.days_of_week,
                        days_of_month=cef.days_of_month,
                        interval=cef.interval,
                        index=cef.index,
                        start_date=cef.start_date,
                        end_date=cef.end_date,
                        month=cef.month
                    ).first()
                    if not target_calendar_event:
                        target_calendar_event = CalendarEventFollowups.objects.create(
                            event_type=cef.event_type,
                            range_type=cef.range_type,
                            number_of_occurrences=cef.number_of_occurrences,
                            days_of_week=cef.days_of_week,
                            days_of_month=cef.days_of_month,
                            interval=cef.interval,
                            index=cef.index,
                            start_date=cef.start_date,
                            end_date=cef.end_date,
                            month=cef.month,
                            created=cef.created or timezone.now(),
                            updated=cef.updated or timezone.now()
                        )
                        self.stats.calendar_event_followups_copied += 1
                        logger.info(f'CalendarEventFollowups Table copied for {CalendarEventFollowups}')
                
                # Check if followup already exists
                existing_followup = Followup.objects.filter(
                    user=self.target_user,
                    contact=target_contact,
                    start=followup.start,
                    notes=followup.notes
                ).first()
                
                if existing_followup:
                    continue
                
                new_followup = Followup.objects.create(
                    user=self.target_user,
                    contact=target_contact,
                    start=followup.start,
                    appointment=target_appointment,
                    contacteventform=target_contact_event_form,
                    duration=followup.duration,
                    notes=followup.notes,
                    completed=followup.completed,
                    contact_phone=target_contact_phone,
                    send_google_cal=followup.send_google_cal,
                    send_office_cal=followup.send_office_cal,
                    item_id=followup.item_id,
                    html_link=followup.html_link,
                    office_item_id=followup.office_item_id,
                    office_html_link=followup.office_html_link,
                    updated=followup.updated or timezone.now(),
                    created=followup.created or timezone.now(),
                    followup_type=target_followup_type,
                    stage=target_stage,
                    priority=target_priority,
                    calendar_event=target_calendar_event
                )
                logger.info(f'Follow up data Copied for {self.target_user} - Contact{target_contact}')
                
                # Copy followup call data if exists
                self._copy_followup_call_data(followup, new_followup)
                
                # Copy followup personnel if exists
                self._copy_followup_personnel_data(followup, new_followup,target_contact)
                
                self.stats.followups_copied += 1
                
            except Exception as e:
                error_msg = f"Error creating followup {followup.id}: {e}"
                logger.error(error_msg)
                self.stats.errors.append(error_msg)
                continue
        
        logger.info(f"[{datetime.now()}] Followups copied: {self.stats.followups_copied}")
    
    def _copy_followup_configuration(self):
        """Copy company-level followup configuration tables"""
        logger.info("Copying followup configuration...")
        
        # Copy FollowupType
        try:
            for ft in FollowupType.objects.filter(company=self.source_company):
                if not FollowupType.objects.filter(company=self.target_company, name=ft.name).exists():
                    FollowupType.objects.create(
                        company=self.target_company,
                        name=ft.name,
                        position=ft.position,
                        is_default=ft.is_default
                    )
                    self.stats.followup_types_copied += 1
        except Exception as e:
            logger.error(f"Error copying FollowupType: {e}")
        
        # Copy FollowupStage
        try:
            for fs in FollowupStage.objects.filter(company=self.source_company):
                if not FollowupStage.objects.filter(company=self.target_company, name=fs.name).exists():
                    FollowupStage.objects.create(
                        company=self.target_company,
                        name=fs.name,
                        fg_color=fs.fg_color,
                        bg_color=fs.bg_color,
                        position=fs.position,
                        map_with_not_completed=fs.map_with_not_completed,
                        map_with_completed=fs.map_with_completed,
                        created=fs.created or timezone.now(),
                        updated=fs.updated or timezone.now()
                    )
                    self.stats.followup_stages_copied += 1
                    logger.info('Create FollowupStage table for {self.target_company} User {fs.name}')
        except Exception as e:
            logger.error(f"Error copying FollowupStage: {e}")
        
        # Copy FollowupPriority (global table)
        try:
            for fp in FollowupPriority.objects.all():
                if not FollowupPriority.objects.filter(name=fp.name).exists():
                    FollowupPriority.objects.create(
                        name=fp.name,
                        created=fp.created or timezone.now(),
                        updated=fp.updated or timezone.now()
                    )
                    self.stats.followup_priorities_copied += 1
                    logger.ingo('FollowupPriority table data copied')
        except Exception as e:
            logger.error(f"Error copying FollowupPriority: {e}")
    
    def _copy_followup_call_data(self, original_followup, target_followup):
        """Copy FollowupCall data for a followup"""
        try:
            followup_calls = FollowupCall.objects.filter(followup=original_followup)
            for fc in followup_calls:
                try:
                    # Map store
                    target_store = None
                    if fc.store:
                        target_store = DealerStore.objects.filter(
                            company=self.target_company,
                            name=fc.store.name
                        ).first()
                    
                    # Map contact phone
                    target_contact_phone = None
                    if fc.contact_phone:
                        target_contact_phone = ContactPhone.objects.filter(
                            contact=target_followup.contact,
                            phone_number=fc.contact_phone.phone_number
                        ).first()
                    
                    # Map call if exists
                    target_call = None
                    if fc.call:
                        target_call_id = self.call_index.get(fc.call.id)
                        if target_call_id:
                            target_call = Call.objects.get(pk=target_call_id)
                    
                    # Check if already exists
                    if not FollowupCall.objects.filter(
                        company=self.target_company,
                        followup=target_followup,
                        user=self.target_user,
                        contact=target_followup.contact,
                        contact_phone=target_contact_phone
                    ).exists():
                        FollowupCall.objects.create(
                            company=self.target_company,
                            followup=target_followup,
                            user=self.target_user,
                            store=target_store,
                            contact=target_followup.contact,
                            contact_phone=target_contact_phone,
                            call=target_call,
                            response_time=fc.response_time,
                            new_upgrade=fc.new_upgrade,
                            upgrade_time=fc.upgrade_time,
                            created=fc.created or timezone.now(),
                            is_followup_call=fc.is_followup_call
                        )
                        self.stats.followup_calls_copied += 1
                        logger.info('FollowupCall tabled data copied ')
                        
                except Exception as e:
                    logger.error(f"Error copying FollowupCall {fc.id}: {e}")
                    continue
                    
        except Exception as e:
            logger.error(f"Error copying FollowupCall data: {e}")
    
    def _copy_followup_personnel_data(self, original_followup, target_followup, target_contact):
        """Copy FollowupPersonnel data for a followup"""
        try:
            followup_personnels = FollowupPersonnel.objects.filter(followup=original_followup)
            for fp in followup_personnels:
                try:
                    # Find equivalent ContactPersonnel in target company
                    original_personnel = fp.personnel
                    target_personnel = None
                    

                    # Try to find matching personnel by email in target company
                    if original_personnel.email:
                        target_personnel = ContactPersonnel.objects.filter(
                            company=self.target_company,
                            email=original_personnel.email
                        ).first()
                        

                    # If not found by email, try by name
                    if not target_personnel:
                        target_personnel = ContactPersonnel.objects.filter(
                            company=self.target_company,
                            first_name=original_personnel.first_name,
                            contact=target_contact,
                            last_name=original_personnel.last_name
                        ).first()

                        

                    # If still not found, create new personnel in target company
                    if not target_personnel:
                        target_personnel = ContactPersonnel.objects.create(
                            company=self.target_company,
                            contact=target_contact,
                            first_name=original_personnel.first_name,
                            last_name=original_personnel.last_name,
                            email=original_personnel.email,
                            title=original_personnel.title,
                            created_by=self.target_user,
                            updated_by=self.target_user,
                            created=original_personnel.created or timezone.now(),
                            updated=original_personnel.updated or timezone.now()
                        )
                        logger.info(f"Created new ContactPersonnel: {target_personnel.first_name} {target_personnel.last_name}")
                    
                    # Check if FollowupPersonnel already exists
                    if not FollowupPersonnel.objects.filter(
                        followup=target_followup,
                        personnel=target_personnel
                    ).exists():
                        FollowupPersonnel.objects.create(
                            followup=target_followup,
                            personnel=target_personnel
                        )
                        self.stats.followup_personnels_copied += 1
                        logger.info(f"Copied FollowupPersonnel for {target_personnel.first_name} {target_personnel.last_name}")
                        
                except Exception as e:
                    logger.error(f"Error copying FollowupPersonnel {fp.id}: {e}")
                    continue
                    
        except Exception as e:
            logger.error(f"Error copying FollowupPersonnel data: {e}")
    
def parse_arguments() -> Tuple[int, int]:
    """Parse and validate command line arguments"""
    parser = argparse.ArgumentParser(description='Copy contact data between users')
    parser.add_argument('--source_user', '--source_user_id', metavar='SU', type=int, required=True, help='Source User ID')
    parser.add_argument('--target_user', '--target_user_id', metavar='TU', type=int, required=True, help='Target User ID')
    args = parser.parse_args()
    
    source_user = args.source_user
    target_user = args.target_user
    
    if not source_user or not target_user:
        logger.error('Both source_user and target_user are required')
        sys.exit(1)
    
    return source_user, target_user


def setup_process_lock():
    """Setup process lock to prevent multiple instances"""
    pid_file = 'contact_copy.pid'
    fp = open(pid_file, 'w')

    if sys.platform.startswith('win'):  # Windows
        import msvcrt
        try:
            msvcrt.locking(fp.fileno(), msvcrt.LK_NBLCK, 1)
            fp.write(str(os.getpid()))
            fp.flush()
        except OSError:
            logger.info("Contact copy script already running.")
            sys.exit(0)
    else:  # Linux / Mac
        import fcntl
        try:
            fcntl.lockf(fp, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except IOError:
            logger.info("Contact copy script already running.")
            sys.exit(0)
    
    return pid_file


def cleanup_process_lock(pid_file: str):
    """Clean up the process lock file"""
    try:
        os.remove(pid_file)
    except Exception:
        pass


def main():
    """Main entry point"""
    pid_file = setup_process_lock()
    
    try:
        source_user_id = 19934
        target_user_id = 19962

        # Create copier and execute
        copier = ContactDataCopier(source_user_id, target_user_id)
        stats = copier.copy_all_contact_data()
        
        # Print summary
        copier.print_summary()
        
        # Exit with appropriate code
        if stats.errors:
            logger.warning(f"Script completed with {len(stats.errors)} errors")
            sys.exit(1)
        else:
            logger.info("Script completed successfully")
            sys.exit(0)
            
    except Exception as e:
        logger.error(f"Critical error: {e}")
        sys.exit(1)
    finally:
        cleanup_process_lock(pid_file)


if __name__ == "__main__":
    main()
