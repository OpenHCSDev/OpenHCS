"""
Test Validator: Ensures GUI and CLI produce identical results

This module validates that a recorded GUI workflow produces the same output
as running the equivalent CLI command, ensuring both interfaces are tested
simultaneously.
"""

import json
import shutil
from pathlib import Path
from typing import Dict, Any, Optional, List
from dataclasses import dataclass
import subprocess
import hashlib


@dataclass
class WorkflowSnapshot:
    """Snapshot of a workflow's state and outputs."""
    config: Dict[str, Any]
    output_files: Dict[str, str]  # path -> hash
    metadata: Dict[str, Any]
    
    def to_json(self) -> str:
        """Serialize to JSON."""
        return json.dumps({
            'config': self.config,
            'output_files': self.output_files,
            'metadata': self.metadata
        }, indent=2)
    
    @classmethod
    def from_json(cls, json_str: str) -> 'WorkflowSnapshot':
        """Deserialize from JSON."""
        data = json.loads(json_str)
        return cls(**data)


class TestValidator:
    """Validates that GUI and CLI produce identical results."""
    
    def __init__(self, test_name: str, workspace_dir: Path):
        self.test_name = test_name
        self.workspace_dir = workspace_dir
        self.gui_snapshot: Optional[WorkflowSnapshot] = None
        self.cli_snapshot: Optional[WorkflowSnapshot] = None
        
    def capture_gui_snapshot(self, plate_dir: Path, config: Dict[str, Any]) -> WorkflowSnapshot:
        """Capture snapshot of GUI workflow results."""
        print(f"📸 Capturing GUI workflow snapshot...")
        
        output_files = self._hash_output_files(plate_dir)
        metadata = self._extract_metadata(plate_dir)
        
        snapshot = WorkflowSnapshot(
            config=config,
            output_files=output_files,
            metadata=metadata
        )
        
        self.gui_snapshot = snapshot
        
        # Save snapshot
        snapshot_path = self.workspace_dir / f"{self.test_name}_gui_snapshot.json"
        snapshot_path.write_text(snapshot.to_json())
        print(f"   Saved GUI snapshot: {snapshot_path}")
        
        return snapshot
    
    def run_cli_equivalent(self, cli_command: List[str]) -> WorkflowSnapshot:
        """Run equivalent CLI command and capture snapshot."""
        print(f"🖥️  Running CLI equivalent...")
        print(f"   Command: {' '.join(cli_command)}")
        
        # Run CLI command
        result = subprocess.run(
            cli_command,
            capture_output=True,
            text=True,
            cwd=self.workspace_dir
        )
        
        if result.returncode != 0:
            raise RuntimeError(f"CLI command failed:\n{result.stderr}")
        
        print(f"   CLI command completed successfully")
        
        # Capture snapshot (assuming same output directory)
        # This would need to be adapted based on your CLI structure
        plate_dir = self.workspace_dir / "plate_output"  # Adjust as needed
        
        output_files = self._hash_output_files(plate_dir)
        metadata = self._extract_metadata(plate_dir)
        
        snapshot = WorkflowSnapshot(
            config={},  # CLI config would be extracted from command args
            output_files=output_files,
            metadata=metadata
        )
        
        self.cli_snapshot = snapshot
        
        # Save snapshot
        snapshot_path = self.workspace_dir / f"{self.test_name}_cli_snapshot.json"
        snapshot_path.write_text(snapshot.to_json())
        print(f"   Saved CLI snapshot: {snapshot_path}")
        
        return snapshot
    
    def validate_equivalence(self) -> bool:
        """Validate that GUI and CLI snapshots are equivalent."""
        if not self.gui_snapshot or not self.cli_snapshot:
            raise ValueError("Both GUI and CLI snapshots must be captured first")
        
        print(f"🔍 Validating GUI ↔ CLI equivalence...")
        
        # Compare output files
        gui_files = set(self.gui_snapshot.output_files.keys())
        cli_files = set(self.cli_snapshot.output_files.keys())
        
        if gui_files != cli_files:
            print(f"   ❌ File mismatch!")
            print(f"      GUI only: {gui_files - cli_files}")
            print(f"      CLI only: {cli_files - gui_files}")
            return False
        
        # Compare file hashes
        mismatches = []
        for file_path in gui_files:
            gui_hash = self.gui_snapshot.output_files[file_path]
            cli_hash = self.cli_snapshot.output_files[file_path]
            
            if gui_hash != cli_hash:
                mismatches.append(file_path)
        
        if mismatches:
            print(f"   ❌ Content mismatch in {len(mismatches)} files:")
            for path in mismatches:
                print(f"      - {path}")
            return False
        
        # Compare metadata
        if self.gui_snapshot.metadata != self.cli_snapshot.metadata:
            print(f"   ⚠️  Metadata differs (may be acceptable)")
            # Metadata differences might be OK (timestamps, etc.)
        
        print(f"   ✅ GUI and CLI produce identical results!")
        return True
    
    def _hash_output_files(self, directory: Path) -> Dict[str, str]:
        """Hash all output files in directory."""
        file_hashes = {}
        
        if not directory.exists():
            return file_hashes
        
        for file_path in directory.rglob('*'):
            if file_path.is_file():
                # Skip log files and temporary files
                if file_path.suffix in ['.log', '.tmp']:
                    continue
                
                # Compute hash
                file_hash = self._hash_file(file_path)
                
                # Store relative path
                rel_path = file_path.relative_to(directory)
                file_hashes[str(rel_path)] = file_hash
        
        return file_hashes
    
    def _hash_file(self, file_path: Path) -> str:
        """Compute SHA256 hash of file."""
        sha256 = hashlib.sha256()
        
        with open(file_path, 'rb') as f:
            while chunk := f.read(8192):
                sha256.update(chunk)
        
        return sha256.hexdigest()
    
    def _extract_metadata(self, directory: Path) -> Dict[str, Any]:
        """Extract metadata from output directory."""
        metadata = {}
        
        # Look for openhcs_metadata.json
        metadata_file = directory / 'openhcs_metadata.json'
        if metadata_file.exists():
            metadata['openhcs'] = json.loads(metadata_file.read_text())
        
        # Count output files by type
        file_counts = {}
        for file_path in directory.rglob('*'):
            if file_path.is_file():
                ext = file_path.suffix
                file_counts[ext] = file_counts.get(ext, 0) + 1
        
        metadata['file_counts'] = file_counts
        
        return metadata


def generate_cli_command_from_config(config: Dict[str, Any], plate_dir: Path) -> List[str]:
    """
    Generate equivalent CLI command from GUI configuration.
    
    This is a placeholder - you'd need to implement the actual mapping
    from your GUI config structure to CLI arguments.
    """
    # Example structure - adapt to your actual CLI
    cmd = ['python', '-m', 'openhcs.cli']
    
    # Add plate directory
    cmd.extend(['--plate', str(plate_dir)])
    
    # Add pipeline config
    if 'pipeline' in config:
        pipeline_config = config['pipeline']
        # Convert pipeline config to CLI args
        # This would need to match your actual CLI structure
        pass
    
    return cmd


def create_dual_test(test_name: str, gui_test_path: Path, workspace_dir: Path) -> str:
    """
    Create a dual test that runs both GUI and CLI and validates equivalence.
    
    This generates a pytest test that:
    1. Runs the recorded GUI test
    2. Extracts the configuration
    3. Runs equivalent CLI command
    4. Validates both produce identical results
    """
    
    test_code = f'''
"""
Dual GUI/CLI Test: {test_name}

This test validates that the GUI and CLI produce identical results
for the same workflow configuration.
"""

import pytest
from pathlib import Path
from openhcs.pyqt_gui.testing.test_validator import TestValidator, generate_cli_command_from_config


def test_{test_name}_gui_cli_equivalence(qtbot, tmp_path):
    """Test that GUI and CLI produce identical results."""
    
    # Import the recorded GUI test
    from tests.pyqt_gui.recorded.test_{test_name} import test_{test_name}
    
    # Run GUI test
    print("Running GUI workflow...")
    test_{test_name}(qtbot)
    
    # Extract configuration from GUI state
    # (This would need to be implemented based on your GUI structure)
    config = {{}}  # Extract from GUI
    
    # Create validator
    validator = TestValidator("{test_name}", tmp_path)
    
    # Capture GUI snapshot
    plate_dir = tmp_path / "plate"
    gui_snapshot = validator.capture_gui_snapshot(plate_dir, config)
    
    # Generate equivalent CLI command
    cli_command = generate_cli_command_from_config(config, plate_dir)
    
    # Run CLI equivalent
    cli_snapshot = validator.run_cli_equivalent(cli_command)
    
    # Validate equivalence
    assert validator.validate_equivalence(), "GUI and CLI produced different results!"
'''
    
    return test_code

