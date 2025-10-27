# LOGOS AGI Database Service

The Database Service is the centralized persistence layer for the LOGOS AGI system, responsible for storing and retrieving ontological knowledge, goals, system logs, and semantic representations.

## Features

- **Thread-safe SQLite operations** with WAL mode for better concurrency
- **RabbitMQ integration** for asynchronous database operations
- **Comprehensive schema** supporting ontological nodes, fractal positions, and trinity vectors
- **Spatial indexing** for efficient similarity queries
- **Graceful shutdown** handling with proper cleanup
- **Health monitoring** and database statistics
- **Backup capabilities** for data protection

## Database Schema

### Core Tables

1. **system_log** - System events and monitoring data
2. **goals** - AGI goal definitions and lifecycle management
3. **nodes** - Ontological knowledge nodes with spatial properties
4. **relations** - Relationships between ontological nodes
5. **semantic_glyphs** - Complex semantic representations

### Key Features

- **Foreign key constraints** for data integrity
- **Optimized indexes** for query performance
- **JSON storage** for flexible metadata
- **Automatic timestamps** for audit trails

## Message Formats

### Write Requests (db_write_queue)

```json
{
    "table": "nodes",
    "data": {
        "id": "node_123",
        "query": "What is consciousness?",
        "trinity_vector": {"existence": 0.8, "goodness": 0.6, "truth": 0.9},
        "fractal_position": {"c_real": 0.1, "c_imag": -0.2, "iterations": 42, "in_set": false},
        "created_at": 1703001234.567,
        "metadata": {"source": "user_query", "confidence": 0.85}
    },
    "operation": "save",
    "request_id": "req_001"
}
```

### Query Requests (db_query_queue)

```json
{
    "query": "SELECT * FROM nodes WHERE created_at > ? ORDER BY created_at DESC LIMIT 10",
    "params": [1703000000],
    "request_id": "query_001",
    "reply_to": "db_response_queue"
}
```

### Query Responses (db_response_queue)

```json
{
    "request_id": "query_001",
    "status": "success",
    "results": [...],
    "row_count": 5,
    "processing_time": 0.023
}
```

## Configuration

### Environment Variables

- `RABBITMQ_HOST` - RabbitMQ server hostname (default: 'rabbitmq')
- `RABBITMQ_PORT` - RabbitMQ server port (default: 5672)
- `RABBITMQ_USER` - RabbitMQ username (default: 'guest')
- `RABBITMQ_PASS` - RabbitMQ password (default: 'guest')

### Database Location

The SQLite database is stored at `/data/logos_agi.db` inside the container, which should be mounted as a volume for persistence.

## Usage

### Direct API Usage

```python
from persistence_manager import PersistenceManager

# Initialize persistence manager
pm = PersistenceManager()

# Save a goal
goal_data = {
    'goal_id': 'goal_001',
    'status': 'active',
    'description': 'Learn about quantum mechanics',
    'priority': 3
}
pm.save('goals', goal_data)

# Query data
results = pm.query("SELECT * FROM goals WHERE status = ?", ('active',))

# Get database statistics
stats = pm.get_database_stats()
print(f"Total nodes: {stats['nodes']}")
```

### RabbitMQ Integration

```python
import pika
import json

# Connect to RabbitMQ
connection = pika.BlockingConnection(pika.ConnectionParameters('localhost'))
channel = connection.channel()

# Send write request
message = {
    'table': 'system_log',
    'data': {
        'source': 'test_service',
        'log_data': json.dumps({'event': 'test_event', 'details': 'test data'}),
        'log_level': 'INFO'
    }
}

channel.basic_publish(
    exchange='',
    routing_key='db_write_queue',
    body=json.dumps(message)
)
```

## Development

### Running Tests

```bash
# Install test dependencies
pip install pytest pytest-mock

# Run tests
pytest tests/
```

### Code Quality

```bash
# Format code
black .

# Type checking
mypy .

# Linting
flake8 .
```

## Docker Usage

### Building the Image

```bash
docker build -t logos-database-service .
```

### Running the Container

```bash
docker run -d \
  --name logos-database \
  -v logos_data:/data \
  -e RABBITMQ_HOST=rabbitmq \
  logos-database-service
```

### Health Check

```bash
docker exec logos-database python -c "
import sqlite3
conn = sqlite3.connect('/data/logos_agi.db')
conn.execute('SELECT COUNT(*) FROM system_log')
print('Database is healthy')
conn.close()
"
```

## Monitoring and Maintenance

### Database Statistics

The service provides real-time statistics about database content:

- Total records in each table
- Recent activity metrics
- Query performance data
- Storage usage information

### Backup and Recovery

```python
# Create backup
pm.backup_database('/data/backup_20231201.db')

# Restore from backup (manual process)
# 1. Stop the service
# 2. Replace /data/logos_agi.db with backup file
# 3. Restart the service
```

### Log Analysis

Service logs are written to:
- Console output (Docker logs)
- `/data/db_service.log` (persistent log file)

Key log events:
- Service startup/shutdown
- Database operations
- Error conditions
- Performance metrics

## Troubleshooting

### Common Issues

1. **RabbitMQ Connection Failed**
   - Check network connectivity
   - Verify RabbitMQ credentials
   - Ensure RabbitMQ service is running

2. **Database Lock Errors**
   - Check for long-running transactions
   - Verify WAL mode is enabled
   - Monitor concurrent access patterns

3. **Out of Disk Space**
   - Monitor `/data` volume usage
   - Implement log rotation
   - Consider database cleanup policies

### Performance Optimization

- Use appropriate indexes for frequent queries
- Monitor query execution times
- Consider database maintenance (VACUUM, ANALYZE)
- Implement connection pooling for high-load scenarios

## Security Considerations

- Database runs as non-root user
- Input validation prevents SQL injection
- Sensitive data should be encrypted before storage
- Regular security updates for base image
- Network isolation through Docker networking
