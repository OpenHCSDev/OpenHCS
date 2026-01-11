"""
System Monitor Core - Framework-agnostic metrics collection.

This module provides pure system metrics collection without any visualization dependencies.
Can be used by any UI framework (PyQt, Textual, etc.) for system monitoring.
"""

import platform
import psutil
import subprocess
import time
from datetime import datetime
from collections import deque
from typing import Dict, Any, Optional

# Try to import GPU monitoring libraries
try:
    import GPUtil
    GPU_AVAILABLE = True
except ImportError:
    GPU_AVAILABLE = False


def is_wsl():
    """Check if running in Windows Subsystem for Linux."""
    return 'microsoft' in platform.uname().release.lower()


def get_cpu_freq_mhz():
    """Get CPU frequency in MHz, with WSL compatibility."""
    if is_wsl():
        try:
            output = subprocess.check_output(
                ['powershell.exe', '-Command',
                 'Get-CimInstance -ClassName Win32_Processor | Select-Object -ExpandProperty CurrentClockSpeed'],
                stderr=subprocess.DEVNULL
            )
            return int(output.strip())
        except Exception:
            return 0
    try:
        freq = psutil.cpu_freq()
        return int(freq.current) if freq else 0
    except Exception:
        return 0


class SystemMonitorCore:
    """
    Framework-agnostic system monitoring core.
    
    Collects CPU, RAM, GPU, and VRAM metrics without any visualization dependencies.
    Maintains historical data in deques for efficient time-series tracking.
    """
    
    def __init__(self, history_length: int = 60):
        """
        Initialize the system monitor core.
        
        Args:
            history_length: Number of historical data points to keep
        """
        self.history_length = history_length

        # Initialize data storage
        self.cpu_history = deque(maxlen=history_length)
        self.ram_history = deque(maxlen=history_length)
        self.gpu_history = deque(maxlen=history_length)
        self.vram_history = deque(maxlen=history_length)
        self.time_stamps = deque(maxlen=history_length)

        # Cache current metrics to avoid duplicate system calls
        self._current_metrics = {}
        
        # Initialize with zeros
        for _ in range(history_length):
            self.cpu_history.append(0)
            self.ram_history.append(0)
            self.gpu_history.append(0)
            self.vram_history.append(0)
            self.time_stamps.append(0)
    
    def update_metrics(self) -> None:
        """
        Update system metrics and cache current values.
        
        Collects CPU, RAM, GPU, and VRAM usage and appends to history.
        Updates internal cache for efficient access via get_metrics_dict().
        """
        # CPU usage
        cpu_percent = psutil.cpu_percent(interval=None)
        self.cpu_history.append(cpu_percent)

        # RAM usage
        ram = psutil.virtual_memory()
        ram_percent = ram.percent
        self.ram_history.append(ram_percent)

        # Cache current metrics to avoid duplicate calls in get_metrics_dict()
        self._current_metrics = {
            'cpu_percent': cpu_percent,
            'ram_percent': ram_percent,
            'ram_used_gb': ram.used / (1024**3),
            'ram_total_gb': ram.total / (1024**3),
            'cpu_cores': psutil.cpu_count(),
            'cpu_freq_mhz': get_cpu_freq_mhz(),
        }

        # GPU usage (if available)
        if GPU_AVAILABLE:
            try:
                gpus = GPUtil.getGPUs()
                if gpus:
                    gpu = gpus[0]  # Use first GPU
                    gpu_load = gpu.load * 100
                    vram_util = gpu.memoryUtil * 100
                    self.gpu_history.append(gpu_load)
                    self.vram_history.append(vram_util)

                    # Cache GPU metrics
                    self._current_metrics.update({
                        'gpu_percent': gpu_load,
                        'vram_percent': vram_util,
                        'gpu_name': gpu.name,
                        'gpu_temp': gpu.temperature,
                        'vram_used_mb': gpu.memoryUsed,
                        'vram_total_mb': gpu.memoryTotal,
                    })
                else:
                    self.gpu_history.append(0)
                    self.vram_history.append(0)
            except:
                self.gpu_history.append(0)
                self.vram_history.append(0)
        else:
            self.gpu_history.append(0)
            self.vram_history.append(0)

        # Update timestamps
        self.time_stamps.append(time.time())
    
    def get_metrics_dict(self) -> Dict[str, Any]:
        """
        Get current metrics as a dictionary.
        
        Uses cached data from update_metrics() to avoid duplicate system calls.
        
        Returns:
            Dictionary containing current system metrics
        """
        # Return cached metrics to avoid duplicate system calls
        # If no cached data exists (first call), return defaults
        if not self._current_metrics:
            return {
                'cpu_percent': 0,
                'ram_percent': 0,
                'ram_used_gb': 0,
                'ram_total_gb': 0,
                'cpu_cores': 0,
                'cpu_freq_mhz': 0,
            }

        return self._current_metrics.copy()
    
    def get_system_info(self) -> Dict[str, Any]:
        """
        Get static system information.
        
        Returns:
            Dictionary containing system information (OS, CPU, RAM, GPU)
        """
        info = {
            'os': platform.system(),
            'os_version': platform.version(),
            'cpu_cores': psutil.cpu_count(),
            'ram_total_gb': psutil.virtual_memory().total / (1024**3),
        }
        
        # Add GPU info if available
        if GPU_AVAILABLE:
            try:
                gpus = GPUtil.getGPUs()
                if gpus:
                    gpu = gpus[0]
                    info['gpu_name'] = gpu.name
                    info['vram_total_mb'] = gpu.memoryTotal
            except:
                pass
        
        return info
    
    def reset_history(self) -> None:
        """Reset all historical data to zeros."""
        self.cpu_history.clear()
        self.ram_history.clear()
        self.gpu_history.clear()
        self.vram_history.clear()
        self.time_stamps.clear()
        
        # Re-initialize with zeros
        for _ in range(self.history_length):
            self.cpu_history.append(0)
            self.ram_history.append(0)
            self.gpu_history.append(0)
            self.vram_history.append(0)
            self.time_stamps.append(0)
        
        self._current_metrics = {}

