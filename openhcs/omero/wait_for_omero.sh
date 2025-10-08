#!/bin/bash
# Wait for OMERO server to be ready
# OMERO can take 5-10 minutes to fully initialize on first startup

set -e

MAX_WAIT=600  # 10 minutes
INTERVAL=10
ELAPSED=0

echo "Waiting for OMERO server to be ready (max ${MAX_WAIT}s)..."

while [ $ELAPSED -lt $MAX_WAIT ]; do
    if sudo docker exec openhcs-omero-server-1 /opt/omero/server/OMERO.server/bin/omero admin status 2>&1 | grep -q "running"; then
        echo "✅ OMERO server is ready!"
        exit 0
    fi
    
    echo "⏳ Still waiting... (${ELAPSED}s elapsed)"
    sleep $INTERVAL
    ELAPSED=$((ELAPSED + INTERVAL))
done

echo "❌ Timeout waiting for OMERO server"
exit 1

