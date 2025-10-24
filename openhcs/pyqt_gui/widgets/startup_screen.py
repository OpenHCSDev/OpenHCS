"""
Startup screen widget for PyQt6 GUI.

Shows a progress bar and live log output during application initialization.
Replaced by system monitor once startup is complete.
"""

import logging
from pathlib import Path
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QProgressBar, QTextEdit, QLabel
)
from PyQt6.QtCore import Qt, QTimer
from PyQt6.QtGui import QFont

logger = logging.getLogger(__name__)


class StartupScreenWidget(QWidget):
    """
    Startup screen showing progress bar and live log output.
    
    This widget displays during application initialization and is replaced
    by the system monitor once startup is complete.
    """
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.log_file_path = None
        self.log_position = 0
        self.update_timer = None
        self.waiting_dots = 0
        self.waiting_timer = None
        self._setup_ui()
        
    def _setup_ui(self):
        """Setup the startup screen UI."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(10)
        
        # Title
        title = QLabel("OpenHCS Starting...")
        title_font = QFont()
        title_font.setPointSize(16)
        title_font.setBold(True)
        title.setFont(title_font)
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(title)
        
        # Progress bar
        self.progress_bar = QProgressBar()
        self.progress_bar.setMinimum(0)
        self.progress_bar.setMaximum(100)
        self.progress_bar.setValue(0)
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setFormat("Initializing... %p%")
        layout.addWidget(self.progress_bar)
        
        # Status label
        self.status_label = QLabel("Loading application...")
        self.status_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(self.status_label)
        
        # Log viewer
        log_label = QLabel("Startup Log:")
        layout.addWidget(log_label)
        
        self.log_viewer = QTextEdit()
        self.log_viewer.setReadOnly(True)
        self.log_viewer.setFont(QFont("Monospace", 9))
        self.log_viewer.setMaximumHeight(300)
        layout.addWidget(self.log_viewer)
        
        layout.addStretch()
        
    def start_monitoring(self, log_file_path: Path):
        """
        Start monitoring the log file for updates.
        
        Args:
            log_file_path: Path to the log file to monitor
        """
        self.log_file_path = log_file_path
        self.log_position = 0
        
        # Start timer to update log viewer
        self.update_timer = QTimer()
        self.update_timer.timeout.connect(self._update_log_viewer)
        self.update_timer.start(100)  # Update every 100ms
        
        logger.info("Startup screen monitoring log file")
        
    def _update_log_viewer(self):
        """Update the log viewer with new log entries."""
        if not self.log_file_path or not self.log_file_path.exists():
            return
            
        try:
            with open(self.log_file_path, 'r') as f:
                # Seek to last position
                f.seek(self.log_position)
                
                # Read new content
                new_content = f.read()
                
                if new_content:
                    # Update position
                    self.log_position = f.tell()
                    
                    # Append to log viewer
                    self.log_viewer.append(new_content.rstrip())
                    
                    # Auto-scroll to bottom
                    scrollbar = self.log_viewer.verticalScrollBar()
                    scrollbar.setValue(scrollbar.maximum())
                    
                    # Update progress based on log content
                    self._update_progress_from_log(new_content)
                    
        except Exception as e:
            logger.warning(f"Failed to update log viewer: {e}")
            
    def _update_progress_from_log(self, log_content: str):
        """
        Update progress bar based on log content.

        Args:
            log_content: New log content to analyze
        """
        # Define progress milestones
        milestones = {
            "Starting OpenHCS PyQt6 GUI": (10, "Starting GUI..."),
            "Initializing PyQt6 application": (20, "Initializing application..."),
            "OpenHCS PyQt6 application initialized": (40, "Application initialized"),
            "OpenHCS PyQt6 main window initialized": (60, "Main window created"),
            "System monitor created": (70, "Loading system monitor..."),
            "Log Viewer initialized": (75, "Initializing log viewer..."),
            "Deferred initialization complete": (80, "UI ready - preparing GPU libraries..."),
            "PyQtGraph will load in 10 seconds": (82, "Waiting for GPU libraries (10s delay)"),
            "⏳ Loading PyQtGraph": (85, "Loading PyQtGraph..."),
            "📦 Importing pyqtgraph module": (87, "Importing pyqtgraph module..."),
            "📦 PyQtGraph module imported": (90, "PyQtGraph module imported"),
            "🔧 Initializing PyQtGraph": (92, "Loading GPU libraries (cupy, numpy)..."),
            "✅ PyQtGraph loaded successfully": (95, "GPU libraries loaded successfully"),
            "Switched to PyQtGraph UI": (100, "Ready ✅"),
        }

        for milestone, (progress, status) in milestones.items():
            if milestone in log_content:
                self.progress_bar.setValue(progress)
                self.status_label.setText(status)

                # Start waiting animation when we hit the 10 second delay
                if "PyQtGraph will load in 10 seconds" in milestone:
                    self._start_waiting_animation()
                # Stop waiting animation when loading actually starts
                elif "⏳ Loading PyQtGraph" in milestone:
                    self._stop_waiting_animation()

    def _start_waiting_animation(self):
        """Start animated dots to show we're waiting (not frozen)."""
        if self.waiting_timer is None:
            self.waiting_timer = QTimer()
            self.waiting_timer.timeout.connect(self._update_waiting_animation)
            self.waiting_timer.start(500)  # Update every 500ms

    def _update_waiting_animation(self):
        """Update the waiting animation (animated dots)."""
        self.waiting_dots = (self.waiting_dots + 1) % 4
        dots = "." * self.waiting_dots
        base_text = "Waiting for GPU libraries (10s delay)"
        self.status_label.setText(f"{base_text}{dots}")

    def _stop_waiting_animation(self):
        """Stop the waiting animation."""
        if self.waiting_timer:
            self.waiting_timer.stop()
            self.waiting_timer = None
                
    def set_progress(self, value: int, status: str = None):
        """
        Manually set progress value and status.
        
        Args:
            value: Progress value (0-100)
            status: Optional status message
        """
        self.progress_bar.setValue(value)
        if status:
            self.status_label.setText(status)
            
    def stop_monitoring(self):
        """Stop monitoring the log file."""
        if self.update_timer:
            self.update_timer.stop()
            self.update_timer = None
        self._stop_waiting_animation()
        logger.info("Startup screen stopped monitoring")

