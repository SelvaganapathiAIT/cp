#!/usr/bin/env python3
"""
Test script to debug EventForm custom field mapping issues
"""
import os
import sys
import django

# Setup Django
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../../")))
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "settings")
django.setup()

from cp.models import EventForm, ContactEventForm, CField, CFieldValue, CFieldMultiValue, EventFormCField
import logging

# Setup basic logging
logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)

def analyze_eventform_fields(event_form_id):
    """Analyze an EventForm's custom fields and their mappings"""
    try:
        event_form = EventForm.objects.get(id=event_form_id)
        logger.info(f"Analyzing EventForm: {event_form.name} (ID: {event_form.id})")
        logger.info(f"Company: {event_form.company.name}")
        
        # Get fields using get_cfields() method
        cfields = event_form.get_cfields()
        logger.info(f"\nEventForm.get_cfields() returned {len(cfields)} fields:")
        
        for i, cfield in enumerate(cfields):
            logger.info(f"  {i+1}. {cfield.name} (ID: {cfield.id})")
            logger.info(f"     - Table: {cfield.cfield_table.name if cfield.cfield_table else 'None'}")
            logger.info(f"     - Type: {cfield.cfield_type.name if cfield.cfield_type else 'None'}")
            logger.info(f"     - RField: {cfield.rfield.name if cfield.rfield else 'None'}")
            logger.info(f"     - Parent: {cfield.cfield.name if cfield.cfield else 'None'}")
            
            # Count values for this field
            value_count = CFieldValue.objects.filter(cfield=cfield).count()
            multi_value_count = CFieldMultiValue.objects.filter(cfield=cfield).count()
            logger.info(f"     - Total Values: {value_count} CFieldValues, {multi_value_count} CFieldMultiValues")
        
        # Check EventFormCField relationships
        logger.info(f"\nEventFormCField relationships:")
        form_cfields = EventFormCField.objects.filter(event_form=event_form).order_by('position')
        logger.info(f"Found {form_cfields.count()} EventFormCField relationships:")
        
        for efc in form_cfields:
            cfield = efc.cfield
            logger.info(f"  - {cfield.name} (pos: {efc.position})")
            logger.info(f"    Table: {cfield.cfield_table.name if cfield.cfield_table else 'None'}")
            logger.info(f"    In get_cfields(): {cfield in cfields}")
        
        # Check ContactEventForm entries
        logger.info(f"\nContactEventForm entries for this form:")
        contact_forms = ContactEventForm.objects.filter(event_form=event_form)[:5]  # Limit to first 5
        logger.info(f"Found {ContactEventForm.objects.filter(event_form=event_form).count()} total entries (showing first 5):")
        
        for cf in contact_forms:
            logger.info(f"  ContactEventForm ID: {cf.id}")
            logger.info(f"    Contact: {cf.contact.first_name} {cf.contact.last_name}")
            logger.info(f"    Created: {cf.created}")
            
            # Check custom field values for this ContactEventForm
            for table_name in ['event_form', 'contact', 'opp']:
                values = CFieldValue.objects.filter(
                    entity_id=cf.id,
                    cfield__cfield_table__name=table_name
                )
                multi_values = CFieldMultiValue.objects.filter(
                    entity_id=cf.id,
                    cfield__cfield_table__name=table_name
                )
                
                if values.exists() or multi_values.exists():
                    logger.info(f"    Table '{table_name}': {values.count()} values, {multi_values.count()} multi-values")
                    for val in values[:3]:  # Show first 3 values
                        logger.info(f"      - {val.cfield.name}: {val.cf_value}")
        
    except EventForm.DoesNotExist:
        logger.error(f"EventForm with ID {event_form_id} not found")
    except Exception as e:
        logger.error(f"Error analyzing EventForm: {e}")
        import traceback
        logger.error(traceback.format_exc())

def find_eventforms_with_issues():
    """Find EventForms that might have mapping issues"""
    logger.info("Searching for EventForms with potential mapping issues...")
    
    # Find EventForms that have ContactEventForm entries with custom field values
    eventforms_with_data = EventForm.objects.filter(
        contacteventform__isnull=False
    ).distinct()
    
    logger.info(f"Found {eventforms_with_data.count()} EventForms with ContactEventForm entries")
    
    for ef in eventforms_with_data[:10]:  # Limit to first 10
        # Check if this EventForm has custom field values
        contact_forms = ContactEventForm.objects.filter(event_form=ef)
        
        total_values = 0
        for cf in contact_forms:
            values_count = CFieldValue.objects.filter(entity_id=cf.id).count()
            multi_values_count = CFieldMultiValue.objects.filter(entity_id=cf.id).count()
            total_values += values_count + multi_values_count
        
        if total_values > 0:
            logger.info(f"EventForm '{ef.name}' (ID: {ef.id}) has {total_values} total custom field values")
            logger.info(f"  Company: {ef.company.name}")
            logger.info(f"  ContactEventForm entries: {contact_forms.count()}")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        # Analyze specific EventForm ID
        try:
            event_form_id = int(sys.argv[1])
            analyze_eventform_fields(event_form_id)
        except ValueError:
            logger.error("Please provide a valid EventForm ID")
    else:
        # Find EventForms with potential issues
        find_eventforms_with_issues()
        logger.info("\nTo analyze a specific EventForm, run:")
        logger.info("python test_eventform_mapping.py <event_form_id>")