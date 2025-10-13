#!/bin/bash
# Configure OpenHCS plugin in running OMERO.web container

set -e

echo "🔧 Configuring OpenHCS plugin in OMERO.web..."

# Wait for OMERO.web to be fully started
echo "  Waiting for OMERO.web to be ready..."
sleep 5

# Check current config
echo "  Current apps:"
sudo docker exec omero-omeroweb-1 /opt/omero/web/venv3/bin/omero config get omero.web.apps

# Add omero_openhcs to the apps list (if not already there)
if ! sudo docker exec omero-omeroweb-1 /opt/omero/web/venv3/bin/omero config get omero.web.apps | grep -q "omero_openhcs"; then
    echo "  Adding omero_openhcs to omero.web.apps..."
    sudo docker exec omero-omeroweb-1 /opt/omero/web/venv3/bin/omero config append omero.web.apps '"omero_openhcs"'
else
    echo "  omero_openhcs already in apps list"
fi

# Add OpenHCS tab to right panel (if not already there)
if ! sudo docker exec omero-omeroweb-1 /opt/omero/web/venv3/bin/omero config get omero.web.ui.right_plugins 2>/dev/null | grep -q "OpenHCS"; then
    echo "  Adding OpenHCS tab to right panel..."
    sudo docker exec omero-omeroweb-1 /opt/omero/web/venv3/bin/omero config append omero.web.ui.right_plugins \
        '["OpenHCS", "omero_openhcs/webclient_plugins/right_plugin.js.html", "openhcs_panel"]'
else
    echo "  OpenHCS already in right plugins"
fi

echo ""
echo "✅ OpenHCS plugin configured!"
echo ""
echo "📋 Current configuration:"
echo "  Apps:"
sudo docker exec omero-omeroweb-1 /opt/omero/web/venv3/bin/omero config get omero.web.apps
echo "  Right plugins:"
sudo docker exec omero-omeroweb-1 /opt/omero/web/venv3/bin/omero config get omero.web.ui.right_plugins
echo ""
echo "⚠️  You need to restart OMERO.web for changes to take effect:"
echo "   sudo docker restart omero-omeroweb-1"
echo ""
echo "🌐 Then access OMERO.web at: http://localhost:4080"
echo "   Username: openhcs"
echo "   Password: openhcs"

