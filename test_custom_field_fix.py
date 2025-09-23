#!/usr/bin/env python3
"""
Test script to validate the custom field mapping fixes
"""
import os
import sys
import django

# Setup Django
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../../")))
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "settings")
django.setup()

from cp.models import (
    Company, User, Contact, EventForm, ContactEventForm, 
    CField, CFieldValue, CFieldMultiValue, CFieldOption, CFieldType, CFieldTable
)
import logging

# Setup basic logging
logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger(__name__)

def test_field_type_classification():
    """Test the field type classification logic"""
    logger.info("Testing field type classification...")
    
    # Test data for different field types
    test_cases = [
        ('text', True, False),          # Should use CFieldValue
        ('integer', True, False),       # Should use CFieldValue
        ('auto_integer', True, False),  # Should use CFieldValue
        ('decimal', True, False),       # Should use CFieldValue
        ('date', True, False),          # Should use CFieldValue
        ('time', True, False),          # Should use CFieldValue
        ('datetime', True, False),      # Should use CFieldValue
        ('textarea', True, False),      # Should use CFieldValue
        ('select', False, True),        # Should use CFieldMultiValue
        ('radio', False, True),         # Should use CFieldMultiValue
        ('checkbox', False, True),      # Should use CFieldMultiValue
        ('multiple_select', False, True), # Should use CFieldMultiValue
        ('multi_select', False, True),  # Should use CFieldMultiValue
    ]
    
    # Import the CustomFieldHandler to test its methods
    from copy_contact_data import CustomFieldHandler
    
    # Create a dummy handler for testing
    try:
        source_company = Company.objects.first()
        target_company = Company.objects.first()
        source_user = User.objects.first()
        target_user = User.objects.first()
        
        if not all([source_company, target_company, source_user, target_user]):
            logger.error("Could not find required test data (Company/User objects)")
            return
        
        handler = CustomFieldHandler(
            source_company, target_company, source_user, target_user, logger
        )
        
        # Create mock CField objects for testing
        for field_type_name, should_use_single, should_use_multi in test_cases:
            # Create a mock CField with the specified type
            field_type = CFieldType(name=field_type_name)
            cfield = CField(cfield_type=field_type, name=f"test_{field_type_name}")
            
            uses_single = handler._uses_single_value_storage(cfield)
            uses_multi = handler._uses_multi_value_storage(cfield)
            
            logger.info(f"Field type '{field_type_name}': single={uses_single}, multi={uses_multi}")
            
            if uses_single != should_use_single:
                logger.error(f"FAIL: {field_type_name} single value storage - expected {should_use_single}, got {uses_single}")
            
            if uses_multi != should_use_multi:
                logger.error(f"FAIL: {field_type_name} multi value storage - expected {should_use_multi}, got {uses_multi}")
        
        logger.info("Field type classification test completed")
        
    except Exception as e:
        logger.error(f"Error testing field type classification: {e}")

def analyze_existing_field_mappings():
    """Analyze existing field mappings to understand the issues"""
    logger.info("Analyzing existing field mappings...")
    
    try:
        # Find fields that might have mapping issues
        problematic_fields = []
        
        # Look for integer fields that have CFieldMultiValue entries (should be CFieldValue)
        integer_types = CFieldType.objects.filter(name__in=['integer', 'auto_integer'])
        for field_type in integer_types:
            fields_with_multi_values = CField.objects.filter(
                cfield_type=field_type
            ).filter(
                cfieldmultivalue__isnull=False
            ).distinct()
            
            for field in fields_with_multi_values:
                multi_value_count = CFieldMultiValue.objects.filter(cfield=field).count()
                single_value_count = CFieldValue.objects.filter(cfield=field).count()
                
                logger.warning(f"Integer field '{field.name}' has {multi_value_count} multi-values and {single_value_count} single-values")
                problematic_fields.append({
                    'field': field,
                    'type': field.cfield_type.name,
                    'issue': 'integer_with_multi_values',
                    'multi_count': multi_value_count,
                    'single_count': single_value_count
                })
        
        # Look for select fields that have CFieldValue entries (should be CFieldMultiValue)
        select_types = CFieldType.objects.filter(name__in=['select', 'radio', 'multiple_select'])
        for field_type in select_types:
            fields_with_single_values = CField.objects.filter(
                cfield_type=field_type
            ).filter(
                cfieldvalue__isnull=False
            ).distinct()
            
            for field in fields_with_single_values:
                multi_value_count = CFieldMultiValue.objects.filter(cfield=field).count()
                single_value_count = CFieldValue.objects.filter(cfield=field).count()
                
                logger.warning(f"Select field '{field.name}' has {single_value_count} single-values and {multi_value_count} multi-values")
                problematic_fields.append({
                    'field': field,
                    'type': field.cfield_type.name,
                    'issue': 'select_with_single_values',
                    'multi_count': multi_value_count,
                    'single_count': single_value_count
                })
        
        logger.info(f"Found {len(problematic_fields)} potentially problematic fields")
        
        return problematic_fields
        
    except Exception as e:
        logger.error(f"Error analyzing field mappings: {e}")
        return []

def suggest_field_fixes(problematic_fields):
    """Suggest fixes for problematic field mappings"""
    logger.info("Suggesting fixes for problematic fields...")
    
    for field_info in problematic_fields:
        field = field_info['field']
        issue = field_info['issue']
        
        if issue == 'integer_with_multi_values':
            logger.info(f"Fix for '{field.name}' (integer): Convert CFieldMultiValue entries to CFieldValue")
            
            # Show sample multi-values that should be converted
            sample_multi_values = CFieldMultiValue.objects.filter(cfield=field)[:3]
            for mv in sample_multi_values:
                logger.info(f"  Multi-value to convert: entity_id={mv.entity_id}, option='{mv.option.name}'")
        
        elif issue == 'select_with_single_values':
            logger.info(f"Fix for '{field.name}' (select): Convert CFieldValue entries to CFieldMultiValue")
            
            # Show sample single-values that should be converted
            sample_single_values = CFieldValue.objects.filter(cfield=field)[:3]
            for sv in sample_single_values:
                logger.info(f"  Single-value to convert: entity_id={sv.entity_id}, value='{sv.cf_value}'")

if __name__ == "__main__":
    logger.info("Starting custom field mapping validation...")
    
    # Test field type classification
    test_field_type_classification()
    
    # Analyze existing mappings
    problematic_fields = analyze_existing_field_mappings()
    
    # Suggest fixes
    if problematic_fields:
        suggest_field_fixes(problematic_fields)
    else:
        logger.info("No problematic field mappings found")
    
    logger.info("Custom field mapping validation completed")