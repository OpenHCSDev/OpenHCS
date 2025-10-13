#!/bin/bash
# Setup script for OMERO.web with OpenHCS plugin

set -e

echo "============================================"
echo "  OMERO.web + OpenHCS Plugin Setup"
echo "============================================"
echo ""

# Check if we're in the right directory
if [ ! -f "docker-compose.yml" ]; then
    echo "Error: Must run from openhcs/omero directory"
    exit 1
fi

# Stop existing containers
echo "[1/5] Stopping existing OMERO containers..."
sudo docker-compose down

# Build custom OMERO.web image with OpenHCS plugin
echo ""
echo "[2/5] Building custom OMERO.web image with OpenHCS plugin..."
sudo docker-compose -f docker-compose.openhcs.yml build omeroweb

# Start services
echo ""
echo "[3/5] Starting OMERO services..."
sudo docker-compose -f docker-compose.openhcs.yml up -d

# Wait for OMERO to be ready
echo ""
echo "[4/5] Waiting for OMERO to be ready..."
sleep 10

# Check if services are running
echo ""
echo "[5/5] Checking service status..."
sudo docker-compose -f docker-compose.openhcs.yml ps

echo ""
echo "============================================"
echo "  ✓ Setup Complete!"
echo "============================================"
echo ""
echo "OMERO.web is now running with OpenHCS plugin at:"
echo "  http://localhost:4080"
echo ""
echo "Login credentials:"
echo "  Username: root"
echo "  Password: openhcs"
echo ""
echo "To see the OpenHCS tab:"
echo "  1. Navigate to a Plate in OMERO.web"
echo "  2. Look for 'OpenHCS' tab in the right panel"
echo ""
echo "To view logs:"
echo "  sudo docker-compose -f docker-compose.openhcs.yml logs -f omeroweb"
echo ""

