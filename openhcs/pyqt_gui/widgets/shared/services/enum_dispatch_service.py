"""
Abstract base class for enum-driven polymorphic dispatch services.

This ABC eliminates duplication across services that use the same pattern:
1. Define an enum for strategies/types
2. Create a dispatch table mapping enum values to handler methods
3. Determine which strategy to use based on input
4. Dispatch to the appropriate handler

Services using this pattern:
- ParameterResetService (ResetStrategy enum)
- NestedValueCollectionService (ValueCollectionStrategy enum)
- Widget creation (WidgetCreationType enum)

Benefits:
- Single source of truth for dispatch pattern
- Enforces consistent structure across services
- Reduces boilerplate in service implementations
- Makes adding new services trivial

Example:
    class MyStrategy(Enum):
        TYPE_A = "type_a"
        TYPE_B = "type_b"
    
    class MyService(EnumDispatchService[MyStrategy]):
        def __init__(self):
            super().__init__()
            self._register_handlers({
                MyStrategy.TYPE_A: self._handle_type_a,
                MyStrategy.TYPE_B: self._handle_type_b,
            })
        
        def _determine_strategy(self, context, **kwargs) -> MyStrategy:
            # Logic to determine which strategy to use
            return MyStrategy.TYPE_A if some_condition else MyStrategy.TYPE_B
        
        def _handle_type_a(self, context, **kwargs):
            # Handler implementation
            pass
        
        def _handle_type_b(self, context, **kwargs):
            # Handler implementation
            pass
        
        def process(self, context, **kwargs):
            # Public API - uses dispatch
            return self.dispatch(context, **kwargs)
"""

from abc import ABC, abstractmethod
from enum import Enum
from typing import TypeVar, Generic, Dict, Callable, Any
import logging

logger = logging.getLogger(__name__)

# Type variable for the strategy enum
StrategyEnum = TypeVar('StrategyEnum', bound=Enum)


class EnumDispatchService(ABC, Generic[StrategyEnum]):
    """
    Abstract base class for services using enum-driven polymorphic dispatch.
    
    Subclasses must:
    1. Define a strategy enum (e.g., ResetStrategy, ValueCollectionStrategy)
    2. Implement _determine_strategy() to select the appropriate strategy
    3. Register handlers in __init__() using _register_handlers()
    4. Implement handler methods for each strategy
    
    The dispatch() method handles the actual dispatching logic.
    """
    
    def __init__(self):
        """Initialize the service with an empty handler registry."""
        self._handlers: Dict[StrategyEnum, Callable] = {}
    
    def _register_handlers(self, handlers: Dict[StrategyEnum, Callable]) -> None:
        """
        Register strategy handlers.
        
        Args:
            handlers: Dictionary mapping strategy enum values to handler methods
        
        Raises:
            ValueError: If handlers dict is empty or contains invalid strategies
        """
        if not handlers:
            raise ValueError(f"{self.__class__.__name__}: Handler registry cannot be empty")
        
        self._handlers = handlers
        logger.debug(f"{self.__class__.__name__}: Registered {len(handlers)} handlers")
    
    @abstractmethod
    def _determine_strategy(self, *args, **kwargs) -> StrategyEnum:
        """
        Determine which strategy to use based on input.
        
        This method must be implemented by subclasses to analyze the input
        and return the appropriate strategy enum value.
        
        Returns:
            Strategy enum value indicating which handler to use
        """
        pass
    
    def dispatch(self, *args, **kwargs) -> Any:
        """
        Dispatch to the appropriate handler based on determined strategy.
        
        This is the core dispatch logic that:
        1. Determines the strategy using _determine_strategy()
        2. Looks up the handler in the registry
        3. Calls the handler with the provided arguments
        
        Args:
            *args: Positional arguments to pass to the handler
            **kwargs: Keyword arguments to pass to the handler
        
        Returns:
            Result from the handler method
        
        Raises:
            KeyError: If strategy is not registered in handlers
        """
        # Determine which strategy to use
        strategy = self._determine_strategy(*args, **kwargs)
        
        # Look up handler
        if strategy not in self._handlers:
            raise KeyError(
                f"{self.__class__.__name__}: No handler registered for strategy {strategy}. "
                f"Available strategies: {list(self._handlers.keys())}"
            )
        # Dispatch to handler
        handler = self._handlers[strategy]
        logger.debug(f"{self.__class__.__name__}: Dispatching to {strategy.value} handler")

        # Handler call convention: the first positional argument is the
        # primary context (e.g., manager/context object). Additional
        # positional arguments passed to dispatch are used only for
        # determining the strategy (for example a pre-computed 'mode') and
        # should NOT be forwarded to the handler. Forward only the
        # primary context and keyword arguments to the handler to avoid
        # accidental "takes X positional arguments but Y were given"
        # errors when handlers are bound instance methods.
        handler_args = args[:1] if args else ()
        return handler(*handler_args, **kwargs)
    
    def get_registered_strategies(self) -> list[StrategyEnum]:
        """
        Get list of all registered strategies.
        
        Returns:
            List of strategy enum values that have registered handlers
        """
        return list(self._handlers.keys())
    
    def has_strategy(self, strategy: StrategyEnum) -> bool:
        """
        Check if a strategy has a registered handler.
        
        Args:
            strategy: Strategy enum value to check
        
        Returns:
            True if strategy has a registered handler, False otherwise
        """
        return strategy in self._handlers

