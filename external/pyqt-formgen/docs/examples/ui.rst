UI Integration
==============

Examples of integrating objectstate with user interfaces.

Placeholder Service
-------------------

The ``LazyDefaultPlaceholderService`` helps generate placeholder text for UI forms:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import (
       LazyDataclassFactory,
       LazyDefaultPlaceholderService,
       config_context,
       extract_all_configs,
       get_current_temp_global,
   )

   @dataclass
   class GlobalConfig:
       api_endpoint: str = "https://api.example.com"
       timeout: int = 30

   @dataclass
   class ServiceConfig:
       service_name: str = "my-service"
       api_endpoint: str = None  # Will inherit
       timeout: int = 60  # Override

   # Create lazy versions
   LazyService = LazyDataclassFactory.make_lazy_simple(ServiceConfig)

   # Create placeholder service
   placeholder_service = LazyDefaultPlaceholderService()

   # Setup configs
   global_cfg = GlobalConfig(api_endpoint="https://prod.api.com")
   service_cfg = ServiceConfig(service_name="payment")

   with config_context(global_cfg):
       with config_context(service_cfg):
           lazy = LazyService()
           current = get_current_temp_global()
           available_configs = extract_all_configs(current)

           # Generate placeholder text
           if hasattr(placeholder_service, 'get_placeholder_text'):
               placeholder = placeholder_service.get_placeholder_text(
                   lazy,
                   "api_endpoint",
                   available_configs
               )
               print(f"Placeholder: {placeholder}")
               # Example output: "Inherited: https://prod.api.com (from GlobalConfig)"

Form Field Generation
---------------------

Generate form fields with inherited value hints:

.. code-block:: python

   from dataclasses import dataclass, fields
   from objectstate import LazyDataclassFactory, config_context

   @dataclass
   class FormConfig:
       username: str = "admin"
       email: str = "admin@example.com"
       role: str = "user"
       active: bool = True

   LazyForm = LazyDataclassFactory.make_lazy_simple(FormConfig)

   def generate_form_fields(config_instance):
       """Generate form fields from config."""
       form_fields = []

       for field in fields(config_instance):
           field_info = {
               'name': field.name,
               'type': field.type.__name__,
               'default': getattr(config_instance, field.name),
               'required': field.default is None
           }
           form_fields.append(field_info)

       return form_fields

   # Create config with some values set
   context_cfg = FormConfig(
       username="john_doe",
       email="john@example.com"
   )

   with config_context(context_cfg):
       lazy = LazyForm()
       fields_data = generate_form_fields(lazy)

       for field in fields_data:
           print(f"Field: {field['name']}")
           print(f"  Type: {field['type']}")
           print(f"  Default: {field['default']}")
           print(f"  Required: {field['required']}")
           print()

Configuration Editor
--------------------

Build a configuration editor that shows inheritance:

.. code-block:: python

   from dataclasses import dataclass, fields
   from objectstate import LazyDataclassFactory, config_context

   @dataclass
   class AppSettings:
       app_name: str = "MyApp"
       theme: str = "light"
       language: str = "en"
       notifications: bool = True

   @dataclass
   class UserSettings(AppSettings):
       username: str = "user"
       theme: str = None  # Inherit from AppSettings
       notifications: bool = False  # Override

   LazyUser = LazyDataclassFactory.make_lazy_simple(UserSettings)

   class ConfigEditor:
       """Simple configuration editor."""

       def __init__(self, objectstate):
           self.config = objectstate

       def display_settings(self):
           """Display all settings with their sources."""
           print("Configuration Settings:")
           print("-" * 50)

           for field in fields(self.config):
               value = getattr(self.config, field.name)
               print(f"{field.name}: {value}")

       def update_setting(self, field_name, value):
           """Update a configuration setting."""
           # In real implementation, this would create a new instance
           print(f"Updating {field_name} to {value}")

   # Use the editor
   app_settings = AppSettings(
       app_name="ProductionApp",
       theme="dark"
   )

   user_settings = UserSettings(
       username="alice",
       language="fr"
   )

   with config_context(app_settings):
       with config_context(user_settings):
           lazy_user = LazyUser()
           editor = ConfigEditor(lazy_user)

           editor.display_settings()
           # Shows:
           # app_name: ProductionApp (from AppSettings)
           # theme: dark (inherited from AppSettings)
           # language: fr (from UserSettings)
           # notifications: False (from UserSettings)
           # username: alice (from UserSettings)

Validation with UI Feedback
----------------------------

Validate configuration and provide UI feedback:

.. code-block:: python

   from dataclasses import dataclass
   from typing import List, Tuple
   from objectstate import LazyDataclassFactory, config_context

   @dataclass
   class ServerConfig:
       host: str = "localhost"
       port: int = 8000
       workers: int = 4
       max_connections: int = 100

   LazyServer = LazyDataclassFactory.make_lazy_simple(ServerConfig)

   def validate_config(config) -> List[Tuple[str, bool, str]]:
       """Validate configuration and return results."""
       results = []

       # Validate port
       if 1 <= config.port <= 65535:
           results.append(("port", True, "Valid port number"))
       else:
           results.append(("port", False, "Port must be between 1 and 65535"))

       # Validate workers
       if config.workers > 0:
           results.append(("workers", True, "Valid worker count"))
       else:
           results.append(("workers", False, "Workers must be positive"))

       # Validate max_connections
       if config.max_connections >= config.workers:
           results.append(("max_connections", True, "Valid max connections"))
       else:
           results.append(("max_connections", False,
                          "Max connections must be >= workers"))

       return results

   # Use validation
   server_cfg = ServerConfig(
       host="production.server.com",
       port=443,
       workers=8,
       max_connections=500
   )

   with config_context(server_cfg):
       lazy = LazyServer()
       validation_results = validate_config(lazy)

       print("Validation Results:")
       print("-" * 50)
       for field, valid, message in validation_results:
           status = "✓" if valid else "✗"
           print(f"{status} {field}: {message}")

Hiding Configs from UI with ui_hidden
--------------------------------------

Use the ``ui_hidden`` parameter to hide intermediate configs from the UI while keeping them available for inheritance:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import auto_create_decorator

   # Create global config
   @auto_create_decorator
   @dataclass
   class GlobalAppConfig:
       app_name: str = "MyApp"
       debug: bool = False

   # Intermediate config - hidden from UI
   @dataclass
   class BaseDisplayConfig:
       """Base display configuration - not meant for direct UI use."""
       resolution: str = "1920x1080"
       fullscreen: bool = False
       vsync: bool = True

   # Apply decorator with ui_hidden=True
   # This config is only inherited by other display configs, so hide it
   BaseDisplayConfig = global_app_config(ui_hidden=True)(BaseDisplayConfig)

   # Concrete display configs - visible in UI
   @global_app_config
   @dataclass
   class GameDisplayConfig(BaseDisplayConfig):
       """Game-specific display settings."""
       fps_limit: int = 60
       anti_aliasing: str = "FXAA"

   @global_app_config
   @dataclass
   class VideoDisplayConfig(BaseDisplayConfig):
       """Video playback display settings."""
       aspect_ratio: str = "16:9"
       color_space: str = "sRGB"

   # UI rendering logic
   def render_config_ui(global_config):
       """Render configuration UI, skipping hidden configs."""
       from dataclasses import fields

       for field in fields(global_config):
           field_value = getattr(global_config, field.name)
           field_type = type(field_value)

           # Check if config should be hidden from UI
           if hasattr(field_type, '_ui_hidden') and field_type._ui_hidden:
               print(f"Skipping hidden config: {field.name}")
               continue

           # Render UI for visible config
           print(f"Rendering UI for: {field.name}")
           # ... actual UI rendering logic

   # Check ui_hidden attribute
   print(f"BaseDisplayConfig._ui_hidden: {BaseDisplayConfig._ui_hidden}")  # True
   print(f"GameDisplayConfig._ui_hidden: {GameDisplayConfig._ui_hidden}")  # False
   print(f"VideoDisplayConfig._ui_hidden: {VideoDisplayConfig._ui_hidden}")  # False

**How it works:**

* ``ui_hidden=True`` sets ``_ui_hidden = True`` on the config class
* The config is still injected as a field in the global config
* Lazy version is still created for inheritance
* UI layer checks ``_ui_hidden`` attribute to skip rendering

**Use cases:**

* Abstract base classes with common fields
* Intermediate configs only used for inheritance
* Internal implementation details not meant for user configuration
* Simplifying UI by hiding technical details

Conditional UI Rendering
~~~~~~~~~~~~~~~~~~~~~~~~~

Build a smart UI that respects the ``ui_hidden`` flag:

.. code-block:: python

   from dataclasses import dataclass, fields, is_dataclass

   def generate_ui_tree(config, indent=0):
       """Generate UI tree, respecting ui_hidden flags."""
       prefix = "  " * indent

       for field in fields(config):
           field_value = getattr(config, field.name)

           # Check if this is a dataclass config
           if is_dataclass(type(field_value)):
               field_type = type(field_value)

               # Skip if hidden
               if hasattr(field_type, '_ui_hidden') and field_type._ui_hidden:
                   continue

               # Render config section
               print(f"{prefix}📁 {field.name}")
               generate_ui_tree(field_value, indent + 1)
           else:
               # Render simple field
               print(f"{prefix}📄 {field.name}: {field_value}")

   # Example usage
   global_config = GlobalAppConfig(app_name="MyGame", debug=True)

   print("UI Configuration Tree:")
   print("=" * 50)
   generate_ui_tree(global_config)
   # Output will show GameDisplayConfig and VideoDisplayConfig
   # but NOT BaseDisplayConfig (it's hidden)

**Benefits:**

* Cleaner UI with only user-relevant configs
* Reduces complexity for end users
* Maintains flexibility for developers
* Configs remain available for inheritance and lazy resolution
