# Context-Engine MCP Server - Quick Reference

## Installation Complete ✅

**Location**: `/home/ts/code/projects/context-engine`

## Start/Stop Services

```bash
cd /home/ts/code/projects/context-engine

# Start all services
docker compose up -d

# Stop all services
docker compose down

# View status
docker compose ps

# View logs
docker compose logs -f
```

## Ports & Endpoints

| Service | Port | Protocol | Purpose |
|---------|------|----------|---------|
| Memory MCP | 8000 | SSE | Code search, memory store |
| Indexer MCP | 8001 | SSE | Indexing, collection management |
| Memory MCP (Alt) | 8002 | HTTP/RMCP | Alternative transport |
| Indexer MCP (Alt) | 8003 | HTTP/RMCP | Alternative transport |
| Qdrant DB | 6333 | HTTP | Vector database (internal) |
| llama.cpp | 8080 | HTTP | Q&A decoder (optional) |

## Index Your Codebase

### Index OpenHCS (Your Project)

```bash
cd /home/ts/code/projects/context-engine

HOST_INDEX_PATH=/home/ts/code/projects/openhcs \
COLLECTION_NAME=codebase \
REPO_NAME=openhcs \
docker compose run --rm indexer --root /work
```

### Index Context-Engine Itself

```bash
cd /home/ts/code/projects/context-engine
make index
```

### Watch Mode (Auto-Reindex on Save)

```bash
cd /home/ts/code/projects/context-engine
make watch
```

## Configure IDE Agent

### Augment / Cursor / Windsurf (SSE)

Add to your MCP configuration:

```json
{
  "mcpServers": {
    "memory": {
      "type": "sse",
      "url": "http://localhost:8000/sse",
      "disabled": false
    },
    "qdrant-indexer": {
      "type": "sse",
      "url": "http://localhost:8001/sse",
      "disabled": false
    }
  }
}
```

### Qodo (HTTP/RMCP)

```json
{
  "memory": { "url": "http://localhost:8002/mcp" },
  "qdrant-indexer": { "url": "http://localhost:8003/mcp" }
}
```

## Available MCP Tools

### Memory Server (Port 8000/8002)
- **store** - Save information/memories with metadata
- **find** - Search memories by query

### Indexer Server (Port 8001/8003)
- **repo_search** / **code_search** - Hybrid code search with filters
- **context_search** - Search + optional Q&A with decoder
- **context_answer** - Answer questions using retrieval + decoder
- **qdrant_list** - List collections
- **qdrant_index** - Index a directory
- **qdrant_prune** - Remove stale points
- **qdrant_status** - Collection statistics

## Common Tasks

```bash
cd /home/ts/code/projects/context-engine

# Full reindex (drops existing data)
make reindex

# Health check
make health

# View logs
docker compose logs -f mcp

# Check Qdrant status
curl -s http://localhost:6333/readyz

# List collections
docker compose run --rm indexer python -c \
  "from qdrant_client import QdrantClient; \
   c = QdrantClient('http://qdrant:6333'); \
   print(c.get_collections())"
```

## Configuration

Edit `/home/ts/code/projects/context-engine/.env`:

```bash
# Qdrant connection
QDRANT_URL=http://localhost:6333
COLLECTION_NAME=codebase

# Embeddings
EMBEDDING_MODEL=BAAI/bge-base-en-v1.5

# Micro-chunking (better retrieval)
INDEX_MICRO_CHUNKS=1
MAX_MICRO_CHUNKS_PER_FILE=200

# Optional: Decoder for Q&A
REFRAG_DECODER=1
REFRAG_RUNTIME=llamacpp
LLAMACPP_URL=http://localhost:8080
```

## Troubleshooting

**Services won't start**
```bash
docker ps  # Check if Docker is running
docker compose logs  # View error logs
```

**No search results**
```bash
cd /home/ts/code/projects/context-engine
make health  # Run health check
make reindex  # Reindex everything
```

**Port conflicts**
- Edit `.env` to change `FASTMCP_PORT`, `FASTMCP_INDEXER_PORT`
- Edit `docker-compose.yml` to update port mappings

**Qdrant connection fails**
```bash
docker compose ps qdrant  # Check if Qdrant container is running
curl -s http://localhost:6333/readyz  # Test connectivity
```

## Documentation

- Full docs: https://github.com/m1rl0k/Context-Engine/blob/test/README.md
- Key features:
  - ReFRAG micro-chunking for precise retrieval
  - Token budgeting to keep prompts lean
  - Multi-repo unified search
  - Automatic cache/collection sync
  - Production-ready operational playbooks

## Next Steps

1. ✅ Verify services are running: `docker compose ps`
2. ✅ Index your codebase (see "Index Your Codebase" section)
3. ✅ Configure your IDE agent with MCP endpoints
4. ✅ Start using context-aware search in your agent!

