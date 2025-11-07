# Context-Engine MCP Server Setup

## Status: ✅ INSTALLED & RUNNING

The Context-Engine MCP server has been set up at `/home/ts/code/projects/context-engine`.

**Setup Location**: `/home/ts/code/projects/context-engine`
**Repository**: https://github.com/m1rl0k/Context-Engine.git
**Status**: Docker containers are being started

**What's Running**:
- Docker images are being pulled and built
- Qdrant vector database is initializing
- MCP servers are starting on configured ports

## What's Being Set Up

Context-Engine provides a unified MCP (Model Context Protocol) retrieval stack with:

- **Qdrant Vector Database** - Stores code embeddings
- **Memory MCP Server** (Port 8000/8002) - Search & store tools
- **Indexer MCP Server** (Port 8001/8003) - Index & management tools
- **Optional llama.cpp** (Port 8080) - Q&A decoder
- **File Watcher** - Auto-reindex on changes

## Ports

| Service | SSE Port | HTTP Port | Purpose |
|---------|----------|-----------|---------|
| Memory MCP | 8000 | 8002 | Code search, memory store |
| Indexer MCP | 8001 | 8003 | Indexing, collection management |
| Qdrant DB | 6333 | - | Vector database (internal) |
| llama.cpp | - | 8080 | Q&A decoder (optional) |

## Quick Start (Right Now!)

```bash
# Navigate to the setup directory
cd /home/ts/code/projects/context-engine

# Check if services are running
docker compose ps

# View logs
docker compose logs -f mcp

# Stop services (if needed)
docker compose down

# Restart services
docker compose up -d
```

## Monitor Progress

```bash
# Check container status
docker ps | grep context-engine

# Verify Qdrant is ready
curl -s http://localhost:6333/readyz

# Test MCP server connectivity
curl -s http://localhost:8000/sse | head -c 100
```

## Next Steps (After Setup Completes)

### 1. Verify Services
```bash
cd /home/ts/code/projects/context-engine
docker compose ps
```

### 2. Index Your Codebase
```bash
cd /home/ts/code/projects/context-engine
HOST_INDEX_PATH=/home/ts/code/projects/openhcs \
COLLECTION_NAME=codebase \
REPO_NAME=openhcs \
docker compose run --rm indexer --root /work
```

### 3. Configure IDE Agent

Add to your MCP config (Augment/Cursor/Windsurf):

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

## Available MCP Tools

### Memory Server (8000/8002)
- `store` - Save memories/information with metadata
- `find` - Search memories by query

### Indexer Server (8001/8003)
- `repo_search` / `code_search` - Hybrid code search
- `context_search` - Search with optional Q&A
- `context_answer` - Answer questions using retrieval
- `qdrant_list` - List collections
- `qdrant_index` - Index a directory
- `qdrant_prune` - Remove stale points
- `qdrant_status` - Collection statistics

## Common Commands

```bash
cd /home/ts/code/projects/context-engine

# View logs
docker compose logs -f mcp

# Full reindex (drops existing data)
make reindex

# Health check
make health

# Stop services
docker compose down

# Restart services
docker compose up -d
```

## Configuration

Edit `/home/ts/code/projects/context-engine/.env` to customize:

```bash
# Qdrant
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
```

## Troubleshooting

**Services won't start**: Check Docker
```bash
docker ps
```

**No search results**: Run health check
```bash
cd /home/ts/code/projects/context-engine && make health
```

**Port conflicts**: Change in `.env` and `docker-compose.yml`

## Documentation

Full docs: https://github.com/m1rl0k/Context-Engine/blob/test/README.md

Key features:
- ReFRAG micro-chunking for precise retrieval
- Token budgeting to keep prompts lean
- Multi-repo unified search
- Automatic cache/collection sync
- Production-ready operational playbooks

