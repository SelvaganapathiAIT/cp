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
    CFieldTable, CFieldMultiValue, CFieldOption, CFieldType, CFieldAuto, AutoAction,
    ContactType, ContactCompany, PhoneType, ContactImage, ContactLabel, 
    ContactPersonnel, ContactRep, ContactResearch, ContactStore, ContactUserFile, 
    ContactPhoneLabel, DealerStore, Label, PeopleRole, ContactPhonePersonnel, 
    ContactRegularFieldsStates, ContactListCust, ContactMenu, EventForm,
    ContactEventForm, EventFormCField, Appointment, Opp, OppStage, OppType, 
    OppContact, OppPersonnel, OppHistory, OppFormCField
)


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

                    # Get or create target option - ensure we're mapping the option correctly
                    target_option = CFieldOption.objects.filter(
                        cfield=target_cfield,
                        name=source_multi_value.option.name
                    ).first()

                    if not target_option:
                        target_option = CFieldOption.objects.create(
                            cfield=target_cfield,
                            name=source_multi_value.option.name,
                            position=source_multi_value.option.position or 0,
                            points=source_multi_value.option.points or 0
                        )
                        self.stats['custom_field_options_copied'] += 1
                        self.logger.debug(f"Created CFieldOption: {target_option.name} for field {target_cfield.name}")

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
                # Get or create target option
                target_option = CFieldOption.objects.filter(
                    cfield=target_cfield,
                    name=source_multi_value.option.name
                ).first()
                
                if not target_option:
                    target_option = CFieldOption.objects.create(
                        cfield=target_cfield,
                        name=source_multi_value.option.name,
                        position=source_multi_value.option.position or 0,
                        points=source_multi_value.option.points or 0
                    )
                    self.stats['custom_field_options_copied'] += 1
                
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
        self.opportunity_index = {}
        self.custom_field_index = {}
        
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
            self._copy_contact_personnel(source_contact, target_contact)
            self._copy_contact_reps(source_contact, target_contact)
            self._copy_contact_research(source_contact, target_contact)
            self._copy_contact_stores(source_contact, target_contact)
            self._copy_contact_user_files(source_contact, target_contact)
            self._copy_contact_custom_fields(source_contact, target_contact)
            logger.info(f"Successfully copied all related data for contact {source_contact.id}")
        except Exception as e:
            logger.error(f"Error copying contact related data: {e}")

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
                if ext_raw is None:
                    ext_str = ''
                else:
                    ext_str = str(ext_raw) if ext_raw is not None else ''
                ext = self._safe_str_slice(ext_str, 15)
                
                # Skip if no phone number or if it already exists
                if not phone_number or self._phone_exists(target_contact, phone_number):
                    continue
                    
                phone_type = self._get_phone_type(phone)
                new_phone = self._create_contact_phone(phone, target_contact, phone_number, ext, phone_type)
                self.contact_phone_index[phone.id] = new_phone.id
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
                        business_card=img.business_card or False,
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
                    ContactUserFile.objects.create(
                        company=self.target_company,
                        contact=target_contact,
                        user_file=cuf.user_file,
                        account=cuf.account or '',
                        email_msg=cuf.email_msg or ''
                    )
            except Exception as e:
                logger.error(f"Error copying contact user file: {e}")

    def _copy_contact_custom_fields(self, source_contact, target_contact):
        """Copy custom fields (CFieldValue and CFieldMultiValue) for contacts using CustomFieldHandler"""
        try:
            # Use the common CustomFieldHandler to copy all custom field data
            self.custom_field_handler.copy_all_custom_fields_for_entity(
                source_contact.id, 
                target_contact.id, 
                'contact'
            )
            
            # Update our stats from the handler's stats
            handler_stats = self.custom_field_handler.get_stats()
            self.stats.custom_fields_copied += (
                handler_stats['custom_fields_copied'] + 
                handler_stats['custom_field_values_copied'] + 
                handler_stats['custom_field_multi_values_copied']
            )
            
        except Exception as e:
            logger.error(f"Error copying contact custom fields: {e}")

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
            self._copy_appointments(self.source_company, self.target_company)
            logger.info("Appointment data copy completed successfully!")
            self._copy_event_forms(self.source_company, self.target_company)
            logger.info("Event form data copy completed successfully!")
            self.copy_user_opportunities()
            logger.info("Oppotunity copy completed successfully!")
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
        """Copy custom fields for opportunities using CustomFieldHandler"""
        try:
            # Use the common CustomFieldHandler to copy all custom field data
            self.custom_field_handler.copy_all_custom_fields_for_entity(
                source_opp.id, 
                target_opp.id, 
                'opp'
            )
            
            # Update our stats from the handler's stats
            handler_stats = self.custom_field_handler.get_stats()
            self.stats.custom_fields_copied += (
                handler_stats['custom_fields_copied'] + 
                handler_stats['custom_field_values_copied'] + 
                handler_stats['custom_field_multi_values_copied']
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

    def _copy_appointments(self, source_company, target_company):
        self.appointment_index = {}
        source_appointments = Appointment.objects.filter(company=source_company)

        for source_appointment in source_appointments:
            try:
                target_contact = Contact.objects.get(
                    id=self.contact_index[source_appointment.contact.id],
                    company=target_company
                )
            except Contact.DoesNotExist:
                continue

            target_user = self.target_user

            try:
                target_event_form = EventForm.objects.get(
                    company=target_company,
                    name=source_appointment.event_form.name
                )
            except EventForm.DoesNotExist:
                target_event_form = None

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
                    apt_end_latitude = source_appointment.apt_end_latitude,
                    apt_end_longitude = source_appointment.apt_end_longitude,
                    started_with_plus = source_appointment.started_with_plus,
                    ended_with_plus = source_appointment.ended_with_plus
                )
                self.appointment_index[source_appointment.id] = new_appointment.id
                self.stats.contact_appointments_copied += 1

            except Exception:
                logger.error(f"Error copying appointment {source_appointment.id}")
                pass

    def _copy_event_forms(self, source_company, target_company):
        """Copy Event Forms and related data from source company to target company"""
        source_contact_event_forms = ContactEventForm.objects.filter(company=source_company)

        for source_contact_event_form in source_contact_event_forms:
            try:
                target_contact = Contact.objects.get(
                    id=self.contact_index[source_contact_event_form.contact.id],
                    company=target_company
                )
            except Contact.DoesNotExist:
                continue

            target_user = self.target_user

            # Get or create target EventForm
            try:
                target_event_form = EventForm.objects.filter(
                    name=source_contact_event_form.event_form.name,
                    company=target_company
                ).first()
            except EventForm.DoesNotExist:
                target_event_form = None

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
                if source_contact_event_form.appointment:
                    target_contact_event_form.appointment_id = self.appointment_index.get(
                        source_contact_event_form.appointment.id
                    )
                target_contact_event_form.save()
                self.stats.contact_event_forms_copied += 1
            except Exception as e:
                logger.error(f"Error copying ContactEventForm: {e}")
                continue

            # Copy CFieldValue and CFieldMultiValue entries using CustomFieldHandler
            self.custom_field_handler.copy_all_custom_fields_for_entity(
                source_contact_event_form.id,
                target_contact_event_form.id,
                'event_form'
            )

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
        target_user_id = 19950

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
