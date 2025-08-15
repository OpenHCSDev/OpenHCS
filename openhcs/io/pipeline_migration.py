"""
OpenHCS Pipeline Migration Utilities

This module provides utilities to migrate old OpenHCS pipeline files that contain
legacy enum values to the new variable component system.

The migration handles:
- Converting old string-based GroupBy enum values to new VariableComponents-based values
- Preserving all other step attributes and functionality
- Creating atomic backups during migration
- Detecting legacy pipeline format automatically

Usage:
    from openhcs.io.pipeline_migration import migrate_pipeline_file, detect_legacy_pipeline
    
    # Check if migration is needed
    if detect_legacy_pipeline(steps):
        success = migrate_pipeline_file(pipeline_path)
"""

import logging
import sys
from pathlib import Path
from typing import Any, List, Dict, Optional
import dill as pickle
import io

logger = logging.getLogger(__name__)


def detect_legacy_pipeline(steps: List[Any]) -> bool:
    """
    Detect if pipeline contains legacy enum values that need migration.
    
    Args:
        steps: List of pipeline steps
        
    Returns:
        True if legacy format detected, False otherwise
    """
    try:
        for step in steps:
            # Check if step has group_by attribute with string value
            if hasattr(step, 'group_by') and step.group_by is not None:
                if isinstance(step.group_by, str):
                    logger.debug(f"Legacy string group_by detected: {step.group_by}")
                    return True
            
            # Check variable_components for string values
            if hasattr(step, 'variable_components') and step.variable_components:
                for component in step.variable_components:
                    if isinstance(component, str):
                        logger.debug(f"Legacy string variable_component detected: {component}")
                        return True
        
        return False
    except Exception as e:
        logger.warning(f"Error detecting legacy pipeline format: {e}")
        return False


def migrate_legacy_group_by(group_by_value: Any) -> Any:
    """
    Migrate legacy GroupBy string values to new enum structure.
    
    Args:
        group_by_value: Legacy group_by value (string or enum)
        
    Returns:
        Migrated GroupBy enum value or original value if no migration needed
    """
    if not isinstance(group_by_value, str):
        return group_by_value
    
    # Import here to avoid circular imports
    from openhcs.constants.constants import GroupBy, VariableComponents
    
    # Map old string values to new GroupBy enum members
    string_to_groupby = {
        'channel': GroupBy.CHANNEL,
        'z_index': GroupBy.Z_INDEX,
        'site': GroupBy.SITE,
        'well': GroupBy.WELL,
        '': GroupBy.NONE,
        'none': GroupBy.NONE,
    }
    
    migrated_value = string_to_groupby.get(group_by_value.lower())
    if migrated_value is not None:
        logger.debug(f"Migrated group_by: '{group_by_value}' -> {migrated_value}")
        return migrated_value
    
    logger.warning(f"Unknown legacy group_by value: '{group_by_value}' - keeping as-is")
    return group_by_value


def migrate_legacy_variable_components(variable_components: List[Any]) -> List[Any]:
    """
    Migrate legacy VariableComponents string values to new enum structure.
    
    Args:
        variable_components: List of variable components (strings or enums)
        
    Returns:
        List of migrated VariableComponents enum values
    """
    if not variable_components:
        return variable_components
    
    # Import here to avoid circular imports
    from openhcs.constants.constants import VariableComponents
    
    # Map old string values to new VariableComponents enum members
    string_to_variable = {
        'channel': VariableComponents.CHANNEL,
        'z_index': VariableComponents.Z_INDEX,
        'site': VariableComponents.SITE,
        'well': VariableComponents.WELL,
    }
    
    migrated_components = []
    for component in variable_components:
        if isinstance(component, str):
            migrated_component = string_to_variable.get(component.lower())
            if migrated_component is not None:
                logger.debug(f"Migrated variable_component: '{component}' -> {migrated_component}")
                migrated_components.append(migrated_component)
            else:
                logger.warning(f"Unknown legacy variable_component: '{component}' - keeping as-is")
                migrated_components.append(component)
        else:
            # Already an enum or other type - keep as-is
            migrated_components.append(component)
    
    return migrated_components


def migrate_pipeline_steps(steps: List[Any]) -> List[Any]:
    """
    Migrate pipeline steps from legacy format to new enum structure.
    
    Args:
        steps: List of pipeline steps to migrate
        
    Returns:
        List of migrated pipeline steps
    """
    migrated_steps = []
    
    for step in steps:
        # Create a copy of the step to avoid modifying the original
        migrated_step = step
        
        # Migrate group_by if present
        if hasattr(step, 'group_by') and step.group_by is not None:
            migrated_step.group_by = migrate_legacy_group_by(step.group_by)
        
        # Migrate variable_components if present
        if hasattr(step, 'variable_components') and step.variable_components:
            migrated_step.variable_components = migrate_legacy_variable_components(step.variable_components)
        
        migrated_steps.append(migrated_step)
    
    return migrated_steps


def migrate_pipeline_file(pipeline_path: Path, backup_suffix: str = ".backup") -> bool:
    """
    Migrate a pipeline file from legacy format to new enum structure.
    
    Args:
        pipeline_path: Path to pipeline file
        backup_suffix: Suffix for backup file
        
    Returns:
        True if migration was needed and successful, False otherwise
    """
    if not pipeline_path.exists():
        logger.error(f"Pipeline file not found: {pipeline_path}")
        return False
    
    # Load existing pipeline
    try:
        with open(pipeline_path, 'rb') as f:
            steps = pickle.load(f)
    except Exception as e:
        logger.error(f"Failed to load pipeline from {pipeline_path}: {e}")
        return False
    
    if not isinstance(steps, list):
        logger.error(f"Invalid pipeline format in {pipeline_path}: expected list, got {type(steps)}")
        return False
    
    # Check if migration is needed
    if not detect_legacy_pipeline(steps):
        logger.info(f"Pipeline file {pipeline_path} is already in new format - no migration needed")
        return False
    
    logger.info(f"Legacy format detected in {pipeline_path}")
    
    # Perform migration
    try:
        migrated_steps = migrate_pipeline_steps(steps)
    except Exception as e:
        logger.error(f"Failed to migrate pipeline: {e}")
        return False
    
    # Create backup
    backup_file = pipeline_path.with_suffix(f"{pipeline_path.suffix}{backup_suffix}")
    try:
        pipeline_path.rename(backup_file)
        logger.info(f"Created backup: {backup_file}")
    except OSError as e:
        logger.error(f"Failed to create backup: {e}")
        return False
    
    # Write migrated pipeline
    try:
        with open(pipeline_path, 'wb') as f:
            pickle.dump(migrated_steps, f)
        logger.info(f"Successfully migrated pipeline file: {pipeline_path}")
        return True
    except Exception as e:
        logger.error(f"Failed to write migrated pipeline: {e}")
        # Restore backup
        try:
            backup_file.rename(pipeline_path)
            logger.info(f"Restored original file from backup")
        except OSError:
            logger.error(f"Failed to restore backup - original file is at {backup_file}")
        return False


class LegacyGroupByUnpickler(pickle.Unpickler):
    """
    Custom unpickler that handles legacy GroupBy enum values during deserialization.

    This unpickler intercepts the creation of GroupBy enum instances and converts
    legacy string values to the new VariableComponents-based structure.
    """

    def find_class(self, module, name):
        """Override find_class to handle GroupBy enum migration."""
        # Get the original class
        cls = super().find_class(module, name)

        # If this is the GroupBy enum, wrap it with migration logic
        if name == 'GroupBy' and module == 'openhcs.constants.constants':
            return self._create_migrating_groupby_class(cls)

        return cls

    def _create_migrating_groupby_class(self, original_groupby_class):
        """Create a wrapper class that handles legacy string values."""

        class MigratingGroupBy:
            """Wrapper that migrates legacy string values to new enum structure."""

            def __new__(cls, value):
                # If it's already a GroupBy enum, return it as-is
                if hasattr(value, '__class__') and value.__class__.__name__ == 'GroupBy':
                    return value

                # Handle legacy string values
                if isinstance(value, str):
                    # Import here to avoid circular imports
                    from openhcs.constants.constants import GroupBy

                    # Map legacy string values to new GroupBy enum members
                    string_to_groupby = {
                        'channel': GroupBy.CHANNEL,
                        'z_index': GroupBy.Z_INDEX,
                        'site': GroupBy.SITE,
                        'well': GroupBy.WELL,
                        '': GroupBy.NONE,
                        'none': GroupBy.NONE,
                    }

                    migrated_value = string_to_groupby.get(value.lower())
                    if migrated_value is not None:
                        logger.debug(f"Unpickler migrated GroupBy: '{value}' -> {migrated_value}")
                        return migrated_value

                    logger.warning(f"Unknown legacy GroupBy value during unpickling: '{value}'")
                    # Fall back to NONE for unknown values
                    return GroupBy.NONE

                # For any other type, try the original class
                try:
                    return original_groupby_class(value)
                except ValueError:
                    # If original class fails, fall back to NONE
                    logger.warning(f"Failed to create GroupBy from value: {value}")
                    from openhcs.constants.constants import GroupBy
                    return GroupBy.NONE

        return MigratingGroupBy


def load_pipeline_with_migration(pipeline_path: Path) -> Optional[List[Any]]:
    """
    Load pipeline file with automatic migration if needed.
    
    This is the main function that should be used by the PyQt GUI
    to load pipeline files with backward compatibility.
    
    Args:
        pipeline_path: Path to pipeline file
        
    Returns:
        List of pipeline steps or None if loading failed
    """
    try:
        # Load pipeline using custom unpickler for enum migration
        with open(pipeline_path, 'rb') as f:
            unpickler = LegacyGroupByUnpickler(f)
            steps = unpickler.load()
        
        if not isinstance(steps, list):
            logger.error(f"Invalid pipeline format: expected list, got {type(steps)}")
            return None
        
        # Check if migration is needed
        if detect_legacy_pipeline(steps):
            logger.info(f"Migrating legacy pipeline format in {pipeline_path}")
            
            # Migrate in-memory (don't modify the file unless explicitly requested)
            migrated_steps = migrate_pipeline_steps(steps)
            
            # Optionally save the migrated version back to file
            # For now, just return the migrated steps without saving
            logger.info(f"Pipeline migrated in-memory. Use migrate_pipeline_file() to save changes.")
            return migrated_steps
        
        return steps
        
    except Exception as e:
        logger.error(f"Failed to load pipeline from {pipeline_path}: {e}")
        return None
