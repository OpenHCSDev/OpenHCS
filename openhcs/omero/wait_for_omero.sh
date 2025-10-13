#!/bin/bash
# Wait for OMERO server to be ready
# OMERO can take 5-10 minutes to fully initialize on first startup

set -e

MAX_WAIT=600  # 10 minutes
INTERVAL=5    # Check every 5 seconds for faster feedback
ELAPSED=0

echo "🔍 Checking OMERO containers..."
sudo docker ps --filter "name=omero" --format "table {{.Names}}\t{{.Status}}"

echo ""
echo "⏳ Waiting for OMERO server to be ready (max ${MAX_WAIT}s)..."

while [ $ELAPSED -lt $MAX_WAIT ]; do
    # Try to get status, show output for debugging
    echo "  [${ELAPSED}s] Checking OMERO server status..."

    # Check if container is even running
    if ! sudo docker ps --filter "name=omero-omeroserver-1" --format "{{.Names}}" | grep -q "omero-omeroserver-1"; then
        echo "  ⚠️  Container omero-omeroserver-1 is not running!"
        echo "  Container list:"
        sudo docker ps --filter "name=omero" --format "  - {{.Names}}: {{.Status}}"
    else
        # Container is running, check OMERO status
        STATUS_OUTPUT=$(sudo docker exec omero-omeroserver-1 /opt/omero/server/OMERO.server/bin/omero admin status 2>&1 || echo "ERROR: Command failed")

        if [ -z "$STATUS_OUTPUT" ]; then
            echo "  ⏳ OMERO not responding yet (still initializing...)"
            # Show last few lines of logs for context
            echo "  Recent logs:"
            sudo docker logs --tail 3 omero-omeroserver-1 2>&1 | sed 's/^/    /'
        else
            echo "  Status: $STATUS_OUTPUT"

            if echo "$STATUS_OUTPUT" | grep -q "running"; then
                echo ""
                echo "✅ OMERO server is ready!"
                exit 0
            fi
        fi
    fi

    sleep $INTERVAL
    ELAPSED=$((ELAPSED + INTERVAL))
done

echo ""
echo "❌ Timeout waiting for OMERO server"
exit 1

