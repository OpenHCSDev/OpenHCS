"""
Pattern File Service - TUI-specific version with external editor support.

This service extends the framework-agnostic PatternFileService with
Textual TUI-specific external editor integration.
"""

import logging
from typing import Union, List, Dict, Optional, Any

from openhcs.ui.shared.pattern_file_service import PatternFileService as PatternFileServiceCore
from openhcs.textual_tui.services.external_editor_service import ExternalEditorService

logger = logging.getLogger(__name__)


class PatternFileService(PatternFileServiceCore):
    """
    TUI-specific pattern file service with external editor integration.

    Extends the framework-agnostic core with prompt_toolkit-based external editor.
    """

    def __init__(self, state: Any):
        """
        Initialize the TUI pattern file service.

        Args:
            state: TUIState instance for external editor integration
        """
        super().__init__()
        self.state = state
        self.external_editor_service = ExternalEditorService(state)

    # Core file I/O methods inherited from PatternFileServiceCore:
    # - load_pattern_from_file()
    # - save_pattern_to_file()
    # - validate_pattern_file()
    # - get_default_save_path()
    # - ensure_func_extension()
    # - backup_pattern_file()

    async def edit_pattern_externally(self, pattern: Union[List, Dict]) -> tuple[bool, Union[List, Dict], Optional[str]]:
        """
        Edit pattern in external editor (Vim) via ExternalEditorService.

        TUI-specific method using prompt_toolkit-based external editor.

        Args:
            pattern: Pattern to edit

        Returns:
            Tuple of (success, new_pattern, error_message)
        """
        try:
            # Format pattern for external editing
            initial_content = f"pattern = {repr(pattern)}"

            # Use existing ExternalEditorService (TUI-specific)
            success, new_pattern, error_message = await self.external_editor_service.edit_pattern_in_external_editor(initial_content)

            return success, new_pattern, error_message

        except Exception as e:
            logger.error(f"External editor integration failed: {e}")
            return False, pattern, f"External editor failed: {e}"
