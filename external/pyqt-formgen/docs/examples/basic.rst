Basic Usage
===========

This page provides basic examples of using objectstate.

Simple Configuration
--------------------

The most basic usage of objectstate:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import (
       set_base_config_type,
       LazyDataclassFactory,
       config_context,
   )

   @dataclass
   class AppConfig:
       api_key: str = "default-key"
       timeout: int = 30
       retries: int = 3

   # Setup
   set_base_config_type(AppConfig)
   LazyAppConfig = LazyDataclassFactory.make_lazy_simple(AppConfig)

   # Create configuration
   config = AppConfig(
       api_key="prod-key-123",
       timeout=60
   )

   # Use with context
   with config_context(config):
       lazy = LazyAppConfig()
       print(lazy.api_key)   # "prod-key-123"
       print(lazy.timeout)   # 60
       print(lazy.retries)   # 3 (default)

Multiple Configurations
-----------------------

Managing multiple configuration types:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import LazyDataclassFactory, config_context

   @dataclass
   class DatabaseConfig:
       host: str = "localhost"
       port: int = 5432
       database: str = "myapp"

   @dataclass
   class CacheConfig:
       backend: str = "redis"
       ttl: int = 300
       max_size: int = 1000

   # Create lazy versions
   LazyDB = LazyDataclassFactory.make_lazy_simple(DatabaseConfig)
   LazyCache = LazyDataclassFactory.make_lazy_simple(CacheConfig)

   # Setup configurations
   db_config = DatabaseConfig(
       host="prod.db.internal",
       port=5433,
       database="production"
   )

   cache_config = CacheConfig(
       backend="memcached",
       ttl=600
   )

   # Use both in context
   with config_context(db_config):
       with config_context(cache_config):
           db = LazyDB()
           cache = LazyCache()

           print(f"Connecting to {db.host}:{db.port}/{db.database}")
           print(f"Cache: {cache.backend}, TTL: {cache.ttl}s")

Function Integration
--------------------

Using lazy configs with functions:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import LazyDataclassFactory, config_context

   @dataclass
   class ProcessConfig:
       batch_size: int = 100
       parallel: bool = False
       log_level: str = "INFO"

   LazyProcess = LazyDataclassFactory.make_lazy_simple(ProcessConfig)

   def process_items(items: list, config: LazyProcess):
       """Process items using configuration."""
       print(f"Processing {len(items)} items")
       print(f"Batch size: {config.batch_size}")
       print(f"Parallel: {config.parallel}")
       print(f"Log level: {config.log_level}")

       # Process in batches
       for i in range(0, len(items), config.batch_size):
           batch = items[i:i + config.batch_size]
           print(f"Processing batch of {len(batch)} items")

   # Use it
   config = ProcessConfig(batch_size=50, parallel=True)

   with config_context(config):
       items = list(range(250))
       lazy_cfg = LazyProcess()
       process_items(items, lazy_cfg)

Overriding Values
-----------------

Explicitly override context values:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import LazyDataclassFactory, config_context

   @dataclass
   class ServerConfig:
       host: str = "0.0.0.0"
       port: int = 8000
       workers: int = 4

   LazyServer = LazyDataclassFactory.make_lazy_simple(ServerConfig)

   # Context provides defaults
   context_config = ServerConfig(
       host="prod.server.com",
       port=443,
       workers=8
   )

   with config_context(context_config):
       # Use all from context
       server1 = LazyServer()
       print(f"Server 1: {server1.host}:{server1.port}, workers={server1.workers}")
       # Output: Server 1: prod.server.com:443, workers=8

       # Override specific values
       server2 = LazyServer(port=8443)
       print(f"Server 2: {server2.host}:{server2.port}, workers={server2.workers}")
       # Output: Server 2: prod.server.com:8443, workers=8

       # Override multiple values
       server3 = LazyServer(host="localhost", port=8080, workers=1)
       print(f"Server 3: {server3.host}:{server3.port}, workers={server3.workers}")
       # Output: Server 3: localhost:8080, workers=1

Automatic Field Injection with Decorators
------------------------------------------

Using the decorator pattern for automatic field injection and lazy class generation:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import auto_create_decorator, ensure_global_config_context

   # Create global config with auto_create_decorator
   @auto_create_decorator
   @dataclass
   class GlobalPipelineConfig:
       num_workers: int = 4
       verbose: bool = False

   # This automatically creates:
   # 1. A decorator named `global_pipeline_config`
   # 2. A lazy class named `PipelineConfig`

   # Use the decorator on other config classes
   @global_pipeline_config
   @dataclass
   class DatabaseConfig:
       host: str = "localhost"
       port: int = 5432
       pool_size: int = 10

   @global_pipeline_config
   @dataclass
   class CacheConfig:
       backend: str = "redis"
       ttl: int = 300

   # After module loading, GlobalPipelineConfig automatically has:
   # - database_config: DatabaseConfig = DatabaseConfig()
   # - cache_config: CacheConfig = CacheConfig()
   # And lazy classes are created: LazyDatabaseConfig, LazyCacheConfig

   # Create and set up global config instance
   global_config = GlobalPipelineConfig(
       num_workers=8,
       verbose=True
   )

   # REQUIRED: Establish global context for lazy resolution
   ensure_global_config_context(GlobalPipelineConfig, global_config)

   # Now you can access injected configs
   print(f"Database: {global_config.database_config.host}:{global_config.database_config.port}")
   print(f"Cache: {global_config.cache_config.backend}, TTL={global_config.cache_config.ttl}")

**Key Benefits:**

* **Automatic injection**: Decorated configs become fields in the global config
* **Lazy class generation**: Lazy versions are automatically created
* **Modular structure**: Each component has its own config class
* **Type-safe**: Full IDE support and type checking

Nested Dataclass Auto-Lazification
-----------------------------------

The framework automatically converts nested dataclass fields to lazy versions:

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import LazyDataclassFactory, config_context

   @dataclass
   class LoggingConfig:
       level: str = "INFO"
       format: str = "json"

   @dataclass
   class AppConfig:
       app_name: str = "MyApp"
       logging: LoggingConfig = LoggingConfig()
       port: int = 8000

   # Create lazy version - nested LoggingConfig is automatically lazified
   LazyAppConfig = LazyDataclassFactory.make_lazy_simple(AppConfig)

   # Use it
   config = AppConfig(
       app_name="ProductionApp",
       logging=LoggingConfig(level="WARNING", format="text"),
       port=443
   )

   with config_context(config):
       lazy_app = LazyAppConfig()

       # Access nested config - it's automatically lazy
       print(f"App: {lazy_app.app_name}")
       print(f"Log level: {lazy_app.logging.level}")
       print(f"Log format: {lazy_app.logging.format}")
       print(f"Port: {lazy_app.port}")

**Benefits:**

* No need to manually create ``LazyLoggingConfig``
* Works recursively for deeply nested configs
* Preserves all field properties and metadata
