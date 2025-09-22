"""Unified clickable help components using consolidated help system."""

from typing import Union, Callable, Optional
from textual.widgets import Static
from textual.events import Click
from textual.message import Message


class ClickableHelpLabel(Static):
    """A clickable label that shows help information when clicked."""

    def __init__(self, text: str, help_target: Union[Callable, type] = None, 
                 param_name: str = None, param_description: str = None, 
                 param_type: type = None, **kwargs):
        """Initialize clickable help label.
        
        Args:
            text: Display text for the label
            help_target: Function or class to show help for (for function help)
            param_name: Parameter name (for parameter help)
            param_description: Parameter description (for parameter help)
            param_type: Parameter type (for parameter help)
        """
        # Add help indicator to text
        display_text = f"{text} [dim](?)[/dim]"
        super().__init__(display_text, **kwargs)
        
        self.help_target = help_target
        self.param_name = param_name
        self.param_description = param_description
        self.param_type = param_type
        
        # Add CSS classes for styling
        self.add_class("clickable-help")
        
    async def on_click(self, event: Click) -> None:
        """Handle click events to show help window using unified manager."""
        event.stop()  # Prevent event bubbling

        from openhcs.textual_tui.windows.help_windows import HelpWindowManager

        if self.help_target:
            # Show function/class help using unified manager
            await HelpWindowManager.show_docstring_help(self.app, self.help_target)
        elif self.param_name:
            # ENHANCEMENT: Try to extract field documentation dynamically if description is missing
            description = self.param_description
            if not description or description == "No description available":
                # Try to extract field documentation from the parent dataclass
                description = self._extract_field_documentation()

            # Show parameter help using unified manager
            await HelpWindowManager.show_parameter_help(
                self.app, self.param_name, description or "No description available", self.param_type
            )

    def _extract_field_documentation(self) -> Optional[str]:
        """Try to extract field documentation from the parent dataclass context."""
        try:
            # Try to find the parent dataclass from the widget hierarchy
            parent_dataclass_type = self._find_parent_dataclass_type()
            if parent_dataclass_type and self.param_name:
                from openhcs.textual_tui.widgets.shared.signature_analyzer import SignatureAnalyzer
                return SignatureAnalyzer.extract_field_documentation(parent_dataclass_type, self.param_name)
        except Exception:
            pass
        return None

    def _find_parent_dataclass_type(self) -> Optional[type]:
        """Try to find the dataclass type from the parent widget hierarchy."""
        try:
            # Walk up the widget hierarchy looking for parameter form managers
            current = self.parent
            while current:
                # Check if this widget has dataclass type information
                if hasattr(current, 'dataclass_type'):
                    return current.dataclass_type
                elif hasattr(current, 'config') and hasattr(current.config, 'dataclass_type'):
                    return current.config.dataclass_type
                current = getattr(current, 'parent', None)
        except Exception:
            pass
        return None


class ClickableFunctionTitle(ClickableHelpLabel):
    """Clickable function title that shows function documentation."""
    
    def __init__(self, func: Callable, index: int = None, **kwargs):
        func_name = getattr(func, '__name__', 'Unknown Function')
        module_name = getattr(func, '__module__', '').split('.')[-1] if func else ''
        
        # Build title text
        title = f"{index + 1}: {func_name}" if index is not None else func_name
        if module_name:
            title += f" ({module_name})"
            
        super().__init__(
            text=f"[bold]{title}[/bold]",
            help_target=func,
            **kwargs
        )


class ClickableParameterLabel(ClickableHelpLabel):
    """Clickable parameter label that shows parameter documentation."""
    
    def __init__(self, param_name: str, param_description: str = None, 
                 param_type: type = None, **kwargs):
        # Format parameter name nicely
        display_name = param_name.replace('_', ' ').title()
        
        super().__init__(
            text=display_name,
            param_name=param_name,
            param_description=param_description or "No description available",
            param_type=param_type,
            **kwargs
        )


class HelpIndicator(Static):
    """Simple help indicator that can be added next to any widget."""
    
    def __init__(self, help_target: Union[Callable, type] = None,
                 param_name: str = None, param_description: str = None,
                 param_type: type = None, **kwargs):
        super().__init__("[dim](?)[/dim]", **kwargs)
        
        self.help_target = help_target
        self.param_name = param_name
        self.param_description = param_description
        self.param_type = param_type
        
        self.add_class("help-indicator")
        
    async def on_click(self, event: Click) -> None:
        """Handle click events to show help window using unified manager."""
        event.stop()

        from openhcs.textual_tui.windows.help_windows import HelpWindowManager

        if self.help_target:
            # Show function/class help using unified manager
            await HelpWindowManager.show_docstring_help(self.app, self.help_target)
        elif self.param_name:
            # ENHANCEMENT: Try to extract field documentation dynamically if description is missing
            description = self.param_description
            if not description or description == "No description available":
                # Try to extract field documentation from the parent dataclass
                description = self._extract_field_documentation()

            # Show parameter help using unified manager
            await HelpWindowManager.show_parameter_help(
                self.app, self.param_name, description or "No description available", self.param_type
            )

    def _extract_field_documentation(self) -> Optional[str]:
        """Try to extract field documentation from the parent dataclass context."""
        try:
            # Try to find the parent dataclass from the widget hierarchy
            parent_dataclass_type = self._find_parent_dataclass_type()
            if parent_dataclass_type and self.param_name:
                from openhcs.textual_tui.widgets.shared.signature_analyzer import SignatureAnalyzer
                return SignatureAnalyzer.extract_field_documentation(parent_dataclass_type, self.param_name)
        except Exception:
            pass
        return None

    def _find_parent_dataclass_type(self) -> Optional[type]:
        """Try to find the dataclass type from the parent widget hierarchy."""
        try:
            # Walk up the widget hierarchy looking for parameter form managers
            current = self.parent
            while current:
                # Check if this widget has dataclass type information
                if hasattr(current, 'dataclass_type'):
                    return current.dataclass_type
                elif hasattr(current, 'config') and hasattr(current.config, 'dataclass_type'):
                    return current.config.dataclass_type
                current = getattr(current, 'parent', None)
        except Exception:
            pass
        return None
