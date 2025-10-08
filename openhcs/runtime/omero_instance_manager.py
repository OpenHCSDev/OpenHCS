"""
OMERO Instance Manager - Manages OMERO server instances for testing.

Follows the same pattern as Napari instance management:
1. Check if OMERO is running
2. Connect to existing instance if available
3. Start new instance if needed (via docker-compose)
4. Provide cleanup utilities
"""

import logging
import subprocess
import time
from pathlib import Path
from typing import Optional, Tuple

logger = logging.getLogger(__name__)

# Default OMERO connection parameters
DEFAULT_OMERO_HOST = 'localhost'
DEFAULT_OMERO_PORT = 4064
DEFAULT_OMERO_WEB_PORT = 4080
DEFAULT_OMERO_USER = 'root'
DEFAULT_OMERO_PASSWORD = 'openhcs'


class OMEROInstanceManager:
    """
    Manages OMERO server instances for testing.
    
    Follows the same pattern as NapariStreamVisualizer:
    - Check if OMERO is running
    - Connect to existing instance if available
    - Start new instance if needed
    """
    
    def __init__(
        self,
        host: str = DEFAULT_OMERO_HOST,
        port: int = DEFAULT_OMERO_PORT,
        user: str = DEFAULT_OMERO_USER,
        password: str = DEFAULT_OMERO_PASSWORD,
        docker_compose_path: Optional[Path] = None
    ):
        """
        Initialize OMERO instance manager.
        
        Args:
            host: OMERO server hostname
            port: OMERO server port
            user: OMERO username
            password: OMERO password
            docker_compose_path: Path to docker-compose.yml (auto-detected if None)
        """
        self.host = host
        self.port = port
        self.user = user
        self.password = password
        self.docker_compose_path = docker_compose_path or self._find_docker_compose()
        self.conn = None
        self._started_by_us = False
    
    def _find_docker_compose(self) -> Optional[Path]:
        """Find docker-compose.yml in OMERO module or project root."""
        # First check OMERO module directory (preferred location)
        omero_module = Path(__file__).parent.parent / "omero" / "docker-compose.yml"
        if omero_module.exists():
            return omero_module

        # Fallback: search up from current file to find project root
        current = Path(__file__).parent
        for _ in range(5):  # Search up to 5 levels
            docker_compose = current / "docker-compose.yml"
            if docker_compose.exists():
                return docker_compose
            current = current.parent
        return None
    
    def is_omero_running(self) -> bool:
        """
        Check if OMERO is running and responsive.
        
        Returns:
            True if OMERO is running and we can connect
        """
        try:
            from omero.gateway import BlitzGateway
            
            # Try to connect with short timeout
            conn = BlitzGateway(
                self.user,
                self.password,
                host=self.host,
                port=self.port
            )
            
            if conn.connect():
                conn.close()
                return True
            return False
            
        except Exception as e:
            logger.debug(f"OMERO not running: {e}")
            return False
    
    def connect(self, timeout: int = 30) -> bool:
        """
        Connect to OMERO, starting it if necessary.
        
        Args:
            timeout: Maximum time to wait for OMERO to be ready (seconds)
        
        Returns:
            True if connected successfully
        """
        # Check if already connected
        if self.conn is not None:
            try:
                # Verify connection is still alive
                self.conn.getEventContext()
                logger.info("✓ Already connected to OMERO")
                return True
            except:
                # Connection is dead, close it
                try:
                    self.conn.close()
                except:
                    pass
                self.conn = None
        
        # Try to connect to existing instance
        if self.is_omero_running():
            logger.info(f"✓ Found existing OMERO instance at {self.host}:{self.port}")
            return self._connect_to_omero()
        
        # No existing instance - try to start one
        logger.info(f"No OMERO instance found, attempting to start one...")
        if self._start_omero_docker():
            # Wait for OMERO to be ready
            if self._wait_for_omero_ready(timeout):
                return self._connect_to_omero()
        
        logger.error("Failed to connect to or start OMERO")
        return False
    
    def _connect_to_omero(self) -> bool:
        """Establish connection to OMERO."""
        try:
            from omero.gateway import BlitzGateway
            
            self.conn = BlitzGateway(
                self.user,
                self.password,
                host=self.host,
                port=self.port
            )
            
            if self.conn.connect():
                logger.info(f"✓ Connected to OMERO at {self.host}:{self.port}")
                return True
            else:
                logger.error("Failed to connect to OMERO")
                return False
                
        except Exception as e:
            logger.error(f"Failed to connect to OMERO: {e}")
            return False
    
    def _start_omero_docker(self) -> bool:
        """
        Start OMERO using docker-compose.
        
        Returns:
            True if docker-compose started successfully
        """
        if self.docker_compose_path is None:
            logger.warning("No docker-compose.yml found, cannot start OMERO")
            return False
        
        if not self.docker_compose_path.exists():
            logger.warning(f"docker-compose.yml not found at {self.docker_compose_path}")
            return False
        
        try:
            logger.info(f"Starting OMERO via docker-compose at {self.docker_compose_path.parent}")
            
            # Run docker-compose up -d
            result = subprocess.run(
                ['docker-compose', 'up', '-d'],
                cwd=self.docker_compose_path.parent,
                capture_output=True,
                text=True,
                timeout=120  # 2 minute timeout for docker-compose
            )
            
            if result.returncode == 0:
                logger.info("✓ docker-compose up completed")
                self._started_by_us = True
                return True
            else:
                logger.error(f"docker-compose failed: {result.stderr}")
                return False
                
        except subprocess.TimeoutExpired:
            logger.error("docker-compose up timed out")
            return False
        except FileNotFoundError:
            logger.error("docker-compose command not found. Install Docker Compose.")
            return False
        except Exception as e:
            logger.error(f"Failed to start docker-compose: {e}")
            return False
    
    def _wait_for_omero_ready(self, timeout: int = 30) -> bool:
        """
        Wait for OMERO to be ready to accept connections.
        
        Args:
            timeout: Maximum time to wait (seconds)
        
        Returns:
            True if OMERO is ready
        """
        logger.info(f"Waiting for OMERO to be ready (timeout: {timeout}s)...")
        
        start_time = time.time()
        while time.time() - start_time < timeout:
            if self.is_omero_running():
                elapsed = time.time() - start_time
                logger.info(f"✓ OMERO is ready (took {elapsed:.1f}s)")
                return True
            
            time.sleep(2)  # Check every 2 seconds
        
        logger.error(f"Timeout waiting for OMERO to be ready ({timeout}s)")
        return False
    
    def close(self):
        """Close OMERO connection."""
        if self.conn is not None:
            try:
                self.conn.close()
                logger.info("✓ Closed OMERO connection")
            except:
                pass
            self.conn = None
    
    def cleanup(self, stop_if_started: bool = True):
        """
        Cleanup OMERO resources.
        
        Args:
            stop_if_started: If True, stop OMERO if we started it
        """
        self.close()
        
        if stop_if_started and self._started_by_us:
            self.stop_omero_docker()
    
    def stop_omero_docker(self):
        """Stop OMERO docker-compose services."""
        if self.docker_compose_path is None or not self.docker_compose_path.exists():
            logger.warning("Cannot stop OMERO: docker-compose.yml not found")
            return
        
        try:
            logger.info("Stopping OMERO via docker-compose...")
            
            result = subprocess.run(
                ['docker-compose', 'down'],
                cwd=self.docker_compose_path.parent,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            if result.returncode == 0:
                logger.info("✓ OMERO stopped")
            else:
                logger.warning(f"docker-compose down had issues: {result.stderr}")
                
        except Exception as e:
            logger.error(f"Failed to stop OMERO: {e}")
    
    def __enter__(self):
        """Context manager entry."""
        self.connect()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.cleanup(stop_if_started=False)  # Don't stop OMERO on exit by default

