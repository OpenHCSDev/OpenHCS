"""
System Monitor with Plotext Visualization
Real-time system monitoring with plotext visualization for Textual TUI.

This module extends SystemMonitorCore with plotext-specific visualization.
"""

import plotext as plt
import platform
import psutil
import time
from datetime import datetime
import io
import sys

from openhcs.ui.shared.system_monitor_core import SystemMonitorCore, GPU_AVAILABLE, get_cpu_freq_mhz


class SystemMonitor(SystemMonitorCore):
    """System monitoring with plotext visualization (TUI-specific)."""

    def __init__(self, history_length=60):
        """Initialize with plotext visualization support."""
        super().__init__(history_length)
    
    def get_ascii_title(self):
        """Return the OpenHCS ASCII art title"""
        return """
╔═══════════════════════════════════════════════════════════════════════╗
║  ██████╗ ██████╗ ███████╗███╗   ██╗██╗  ██╗ ██████╗███████╗         ║
║ ██╔═══██╗██╔══██╗██╔════╝████╗  ██║██║  ██║██╔════╝██╔════╝         ║
║ ██║   ██║██████╔╝█████╗  ██╔██╗ ██║███████║██║     ███████╗         ║
║ ██║   ██║██╔═══╝ ██╔══╝  ██║╚██╗██║██╔══██║██║     ╚════██║         ║
║ ╚██████╔╝██║     ███████╗██║ ╚████║██║  ██║╚██████╗███████║         ║
║  ╚═════╝ ╚═╝     ╚══════╝╚═╝  ╚═══╝╚═╝  ╚═╝ ╚═════╝╚══════╝         ║
╚═══════════════════════════════════════════════════════════════════════╝"""
    
    def create_monitor_view(self, width=80, height=30):
        """Create the system monitor visualization"""
        plt.clear_figure()
        
        # Create subplots
        plt.subplots(2, 2)
        plt.plot_size(width=width, height=height)
        
        # Get current metrics for display
        current_cpu = self.cpu_history[-1] if self.cpu_history else 0
        current_ram = self.ram_history[-1] if self.ram_history else 0
        current_gpu = self.gpu_history[-1] if self.gpu_history else 0
        current_vram = self.vram_history[-1] if self.vram_history else 0
        
        # Get system info
        ram_info = psutil.virtual_memory()
        ram_used_gb = ram_info.used / (1024**3)
        ram_total_gb = ram_info.total / (1024**3)
        
        x_range = list(range(len(self.cpu_history)))
        
        # CPU Usage Plot (Top Left)
        plt.subplot(1, 1)
        plt.theme('dark')
        plt.plot(x_range, list(self.cpu_history), color='cyan')
        plt.ylim(0, 100)
        plt.title(f"CPU Usage: {current_cpu:.1f}%")
        plt.xlabel("Time (seconds)")
        plt.ylabel("Usage %")
        
        # RAM Usage Plot (Top Right)
        plt.subplot(1, 2)
        plt.theme('dark')
        plt.plot(x_range, list(self.ram_history), color='green')
        plt.ylim(0, 100)
        plt.title(f"RAM: {ram_used_gb:.1f}/{ram_total_gb:.1f} GB ({current_ram:.1f}%)")
        plt.xlabel("Time (seconds)")
        plt.ylabel("Usage %")
        
        # GPU Usage Plot (Bottom Left)
        plt.subplot(2, 1)
        plt.theme('dark')
        if GPU_AVAILABLE and any(self.gpu_history):
            plt.plot(x_range, list(self.gpu_history), color='yellow')
            plt.ylim(0, 100)
            plt.title(f"GPU Usage: {current_gpu:.1f}%")
        else:
            plt.plot([0, 1], [0, 0], color='red')
            plt.title("GPU: Not Available")
        plt.xlabel("Time (seconds)")
        plt.ylabel("Usage %")
        
        # VRAM Usage Plot (Bottom Right)
        plt.subplot(2, 2)
        plt.theme('dark')
        if GPU_AVAILABLE and any(self.vram_history):
            plt.plot(x_range, list(self.vram_history), color='magenta')
            plt.ylim(0, 100)
            plt.title(f"VRAM Usage: {current_vram:.1f}%")
        else:
            plt.plot([0, 1], [0, 0], color='red')
            plt.title("VRAM: Not Available")
        plt.xlabel("Time (seconds)")
        plt.ylabel("Usage %")
        
        # Capture the plot output
        old_stdout = sys.stdout
        sys.stdout = buffer = io.StringIO()
        
        try:
            # Print title
            print(self.get_ascii_title())
            
            # Show plots
            plt.show()
            
            # Additional system info
            print("\n" + "═" * 75)
            print(f"System Information | Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            print("═" * 75)
            print(f"CPU Cores: {psutil.cpu_count()} | CPU Frequency: {get_cpu_freq_mhz()} MHz")
            print(f"Total RAM: {ram_total_gb:.1f} GB | Available RAM: {ram_info.available/(1024**3):.1f} GB")
            
            if GPU_AVAILABLE:
                try:
                    gpus = GPUtil.getGPUs()
                    if gpus:
                        gpu = gpus[0]
                        print(f"GPU: {gpu.name} | VRAM: {gpu.memoryUsed:.0f}/{gpu.memoryTotal:.0f} MB")
                        print(f"GPU Temperature: {gpu.temperature}°C")
                except:
                    pass
            
            # Disk usage
            disk = psutil.disk_usage('/')
            print(f"Disk Usage: {disk.used/(1024**3):.1f}/{disk.total/(1024**3):.1f} GB ({disk.percent}%)")
            
            # Network info
            net = psutil.net_io_counters()
            print(f"Network - Sent: {net.bytes_sent/(1024**2):.1f} MB | Recv: {net.bytes_recv/(1024**2):.1f} MB")
            print("═" * 75)
            
            output = buffer.getvalue()
        finally:
            sys.stdout = old_stdout
        
        return output
    
    def get_metrics_dict(self):
        """Get current metrics as a dictionary - uses cached data from update_metrics()"""
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


# Standalone CLI usage
def main():
    """Run system monitor in standalone mode"""
    monitor = SystemMonitor()
    
    print("Starting System Monitor...")
    print("Press Ctrl+C to exit")
    
    try:
        while True:
            monitor.update_metrics()
            print("\033[2J\033[H")  # Clear screen
            print(monitor.create_monitor_view())
            time.sleep(1)
    except KeyboardInterrupt:
        print("\nExiting System Monitor...")


if __name__ == "__main__":
    main()