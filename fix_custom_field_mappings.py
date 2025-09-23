#!/usr/bin/env python3
"""
Script to fix existing custom field mapping issues
This script will correct the storage of custom field values based on their types
"""
import os
import sys
import django
from django.db import transaction

# Setup Django
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../../")))
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "settings")
django.setup()

from cp.models import (
    Company, User, Contact, EventForm, ContactEventForm, 
    CField, CFieldValue, CFieldMultiValue, CFieldOption, CFieldType, CFieldTable
)
from django.utils import timezone
import logging

# Setup logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class CustomFieldMappingFixer:
    """Fix custom field mapping issues"""
    
    def __init__(self, dry_run=True):
        self.dry_run = dry_run
        self.stats = {
            'fields_analyzed': 0,
            'integer_fields_fixed': 0,
            'select_fields_fixed': 0,
            'values_converted': 0,
            'options_created': 0,
            'errors': []
        }
    
    def _uses_single_value_storage(self, cfield):
        """Determine if a CField should use CFieldValue storage"""
        if not cfield.cfield_type:
            return True
        
        single_value_types = {
            'text', 'integer', 'auto_integer', 'decimal', 'date', 'time', 'datetime', 'textarea'
        }
        return cfield.cfield_type.name in single_value_types
    
    def _uses_multi_value_storage(self, cfield):
        """Determine if a CField should use CFieldMultiValue storage"""
        if not cfield.cfield_type:
            return False
        
        multi_value_types = {
            'select', 'radio', 'checkbox', 'multiple_select', 'multi_select'
        }
        return cfield.cfield_type.name in multi_value_types
    
    def analyze_field_mappings(self):
        """Analyze all custom fields for mapping issues"""
        logger.info("Analyzing custom field mappings...")
        
        problematic_fields = []
        all_fields = CField.objects.select_related('cfield_type').all()
        
        for field in all_fields:
            self.stats['fields_analyzed'] += 1
            
            if not field.cfield_type:
                continue
            
            single_value_count = CFieldValue.objects.filter(cfield=field).count()
            multi_value_count = CFieldMultiValue.objects.filter(cfield=field).count()
            
            field_type = field.cfield_type.name
            should_use_single = self._uses_single_value_storage(field)
            should_use_multi = self._uses_multi_value_storage(field)
            
            # Check for mismatched storage
            if should_use_single and multi_value_count > 0:
                problematic_fields.append({
                    'field': field,
                    'type': field_type,
                    'issue': 'single_value_field_with_multi_values',
                    'single_count': single_value_count,
                    'multi_count': multi_value_count
                })
                logger.warning(f"Field '{field.name}' ({field_type}) should use single values but has {multi_value_count} multi-values")
            
            elif should_use_multi and single_value_count > 0:
                problematic_fields.append({
                    'field': field,
                    'type': field_type,
                    'issue': 'multi_value_field_with_single_values',
                    'single_count': single_value_count,
                    'multi_count': multi_value_count
                })
                logger.warning(f"Field '{field.name}' ({field_type}) should use multi values but has {single_value_count} single-values")
        
        logger.info(f"Found {len(problematic_fields)} fields with mapping issues")
        return problematic_fields
    
    @transaction.atomic
    def fix_single_value_field_with_multi_values(self, field):
        """Fix a single-value field that incorrectly has multi-values"""
        logger.info(f"Fixing single-value field: {field.name} ({field.cfield_type.name})")
        
        multi_values = CFieldMultiValue.objects.filter(cfield=field)
        converted_count = 0
        
        for mv in multi_values:
            try:
                # Convert the option name to a single value
                value_to_store = mv.option.name
                
                # Check if single value already exists
                if not CFieldValue.objects.filter(
                    cfield=field,
                    entity_id=mv.entity_id,
                    cf_value=value_to_store
                ).exists():
                    
                    if not self.dry_run:
                        CFieldValue.objects.create(
                            cfield=field,
                            entity_id=mv.entity_id,
                            cf_value=value_to_store,
                            updated=mv.updated or timezone.now()
                        )
                    
                    converted_count += 1
                    logger.debug(f"Converted multi-value to single-value: entity_id={mv.entity_id}, value='{value_to_store}'")
                
                # Remove the multi-value entry
                if not self.dry_run:
                    mv.delete()
                
            except Exception as e:
                error_msg = f"Error converting multi-value for field {field.name}: {e}"
                logger.error(error_msg)
                self.stats['errors'].append(error_msg)
        
        self.stats['values_converted'] += converted_count
        self.stats['integer_fields_fixed'] += 1
        logger.info(f"Converted {converted_count} multi-values to single-values for field '{field.name}'")
    
    @transaction.atomic
    def fix_multi_value_field_with_single_values(self, field):
        """Fix a multi-value field that incorrectly has single-values"""
        logger.info(f"Fixing multi-value field: {field.name} ({field.cfield_type.name})")
        
        single_values = CFieldValue.objects.filter(cfield=field)
        converted_count = 0
        
        for sv in single_values:
            try:
                # Get or create option for this value
                option_name = sv.cf_value
                
                option = CFieldOption.objects.filter(
                    cfield=field,
                    name=option_name
                ).first()
                
                if not option:
                    if not self.dry_run:
                        option = CFieldOption.objects.create(
                            cfield=field,
                            name=option_name,
                            position=0,
                            points=0
                        )
                        self.stats['options_created'] += 1
                        logger.debug(f"Created option '{option_name}' for field '{field.name}'")
                    else:
                        # In dry run mode, create a mock option for testing
                        option = CFieldOption(name=option_name)
                
                # Check if multi-value already exists
                if option and not CFieldMultiValue.objects.filter(
                    cfield=field,
                    entity_id=sv.entity_id,
                    option=option
                ).exists():
                    
                    if not self.dry_run:
                        CFieldMultiValue.objects.create(
                            cfield=field,
                            entity_id=sv.entity_id,
                            option=option,
                            updated=sv.updated or timezone.now()
                        )
                    
                    converted_count += 1
                    logger.debug(f"Converted single-value to multi-value: entity_id={sv.entity_id}, option='{option_name}'")
                
                # Remove the single-value entry
                if not self.dry_run:
                    sv.delete()
                
            except Exception as e:
                error_msg = f"Error converting single-value for field {field.name}: {e}"
                logger.error(error_msg)
                self.stats['errors'].append(error_msg)
        
        self.stats['values_converted'] += converted_count
        self.stats['select_fields_fixed'] += 1
        logger.info(f"Converted {converted_count} single-values to multi-values for field '{field.name}'")
    
    def fix_all_mapping_issues(self):
        """Fix all identified mapping issues"""
        logger.info("Starting custom field mapping fix...")
        
        if self.dry_run:
            logger.info("Running in DRY RUN mode - no changes will be made")
        
        problematic_fields = self.analyze_field_mappings()
        
        for field_info in problematic_fields:
            field = field_info['field']
            issue = field_info['issue']
            
            try:
                if issue == 'single_value_field_with_multi_values':
                    self.fix_single_value_field_with_multi_values(field)
                elif issue == 'multi_value_field_with_single_values':
                    self.fix_multi_value_field_with_single_values(field)
            except Exception as e:
                error_msg = f"Error fixing field {field.name}: {e}"
                logger.error(error_msg)
                self.stats['errors'].append(error_msg)
        
        self.print_summary()
    
    def print_summary(self):
        """Print summary of fixes applied"""
        logger.info("=" * 60)
        logger.info("CUSTOM FIELD MAPPING FIX SUMMARY")
        logger.info("=" * 60)
        logger.info(f"Mode: {'DRY RUN' if self.dry_run else 'LIVE EXECUTION'}")
        logger.info(f"Fields analyzed: {self.stats['fields_analyzed']}")
        logger.info(f"Integer fields fixed: {self.stats['integer_fields_fixed']}")
        logger.info(f"Select fields fixed: {self.stats['select_fields_fixed']}")
        logger.info(f"Values converted: {self.stats['values_converted']}")
        logger.info(f"Options created: {self.stats['options_created']}")
        
        if self.stats['errors']:
            logger.info(f"Errors encountered: {len(self.stats['errors'])}")
            for error in self.stats['errors'][-5:]:  # Show last 5 errors
                logger.error(f"  • {error}")
        
        logger.info("=" * 60)

def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Fix custom field mapping issues')
    parser.add_argument('--execute', action='store_true', 
                       help='Actually execute the fixes (default is dry run)')
    parser.add_argument('--analyze-only', action='store_true',
                       help='Only analyze the issues without fixing')
    
    args = parser.parse_args()
    
    dry_run = not args.execute
    
    fixer = CustomFieldMappingFixer(dry_run=dry_run)
    
    if args.analyze_only:
        fixer.analyze_field_mappings()
    else:
        fixer.fix_all_mapping_issues()

if __name__ == "__main__":
    main()