"""
Shared search service for UI components.

This module provides a framework-agnostic search service that can be used
by both PyQt and Textual implementations to ensure consistent search behavior
across the application.
"""

from typing import Dict, Callable, TypeVar, Generic
import logging

logger = logging.getLogger(__name__)

T = TypeVar('T')


class SearchService(Generic[T]):
    """
    Framework-agnostic search service with minimum character trigger.
    
    This service provides consistent search behavior across PyQt and Textual
    implementations, ensuring the same code path is used for all search operations.
    
    Key features:
    - Minimum character threshold (default: 2)
    - Customizable searchable text extraction
    - Performance optimization for short searches
    """
    
    # Class constant for minimum search characters
    MIN_SEARCH_CHARS = 2
    
    def __init__(self, 
                 all_items: Dict[str, T],
                 searchable_text_extractor: Callable[[T], str],
                 min_chars: int = MIN_SEARCH_CHARS):
        """
        Initialize search service.
        
        Args:
            all_items: Dictionary of all searchable items (key -> item)
            searchable_text_extractor: Function to extract searchable text from an item
            min_chars: Minimum characters required to trigger search (default: 2)
        """
        self.all_items = all_items
        self.searchable_text_extractor = searchable_text_extractor
        self.min_chars = min_chars
        self.filtered_items = all_items.copy()
    
    def filter(self, search_term: str) -> Dict[str, T]:
        """
        Filter items based on search term.
        
        This is the canonical search implementation used across all UI frameworks.
        
        Args:
            search_term: Search string to filter by
            
        Returns:
            Dictionary of filtered items
        """
        search_term = search_term.strip()
        
        # Performance optimization: skip expensive filtering for short searches
        if not search_term or len(search_term) < self.min_chars:
            if len(search_term) == 0:
                # Only update if completely empty (to reset from previous filter)
                if self.filtered_items != self.all_items:
                    self.filtered_items = self.all_items.copy()
                    return self.filtered_items
            # For searches below min_chars, keep current state
            return self.filtered_items
        
        # Perform search
        search_lower = search_term.lower()
        
        filtered = {
            key: item for key, item in self.all_items.items()
            if search_lower in self.searchable_text_extractor(item).lower()
        }
        
        self.filtered_items = filtered
        return filtered
    
    def reset(self):
        """Reset filter to show all items."""
        self.filtered_items = self.all_items.copy()
        return self.filtered_items
    
    def update_items(self, new_items: Dict[str, T]):
        """Update the items being searched."""
        self.all_items = new_items
        self.filtered_items = new_items.copy()

