# logos_agi_v1/services/database/persistence_manager.py

import json
import logging
import sqlite3
import threading
import time
from typing import Any

# --- Basic Configuration ---
DB_FILE = "/data/logos_agi.db"  # Path inside the Docker container
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - PERSISTENCE - %(message)s"
)


class PersistenceManager:
    """
    Consolidated database persistence layer for the LOGOS AGI system.
    Handles all low-level SQLite operations with thread-safety.
    Supports ontological nodes, goals, system logs, semantic glyphs, and relations.
    """

    def __init__(self, db_file=DB_FILE):
        self.db_file = db_file
        self.lock = threading.Lock()
        self._init_db()
        logging.info(f"PersistenceManager initialized with database: {db_file}")

    def _get_connection(self):
        """Creates a new database connection with proper configuration."""
        conn = sqlite3.connect(self.db_file, check_same_thread=False)
        conn.execute("PRAGMA foreign_keys = ON")  # Enable foreign key constraints
        conn.execute("PRAGMA journal_mode = WAL")  # Write-Ahead Logging for better concurrency
        return conn

    def _init_db(self):
        """Initializes the database and creates all necessary tables."""
        with self.lock:
            try:
                conn = self._get_connection()
                cursor = conn.cursor()

                # System log table for all system events/data
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS system_log (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                        source TEXT NOT NULL,
                        log_data TEXT NOT NULL,
                        log_level TEXT DEFAULT 'INFO'
                    )
                """
                )

                # Goals table for AGI goal management
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS goals (
                        goal_id TEXT PRIMARY KEY,
                        status TEXT NOT NULL,
                        description TEXT,
                        priority INTEGER DEFAULT 5,
                        details TEXT, -- JSON blob for extra data
                        created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                        updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
                    )
                """
                )

                # Ontological nodes table for fractal knowledge representation
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS nodes (
                        id TEXT PRIMARY KEY,
                        query TEXT NOT NULL,
                        trinity_vector TEXT NOT NULL, -- JSON: {existence, goodness, truth}
                        fractal_position TEXT NOT NULL, -- JSON: {c_real, c_imag, iterations, in_set}
                        created_at REAL NOT NULL,
                        parent_id TEXT,
                        children_ids TEXT, -- JSON array of child node IDs
                        metadata TEXT, -- JSON blob for additional data
                        FOREIGN KEY (parent_id) REFERENCES nodes(id)
                    )
                """
                )

                # Relations table for node relationships
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS relations (
                        src TEXT NOT NULL,
                        tgt TEXT NOT NULL,
                        type TEXT NOT NULL,
                        weight REAL DEFAULT 1.0,
                        metadata TEXT, -- JSON blob
                        created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                        PRIMARY KEY (src, tgt, type),
                        FOREIGN KEY (src) REFERENCES nodes(id),
                        FOREIGN KEY (tgt) REFERENCES nodes(id)
                    )
                """
                )

                # Semantic glyphs table for complex semantic representations
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS semantic_glyphs (
                        glyph_id TEXT PRIMARY KEY,
                        center_x REAL NOT NULL,
                        center_y REAL NOT NULL,
                        fractal_dimension REAL NOT NULL,
                        semantic_complexity REAL NOT NULL,
                        topology_signature TEXT NOT NULL,
                        source_hashes TEXT NOT NULL, -- JSON array
                        synthesis_weights TEXT NOT NULL, -- JSON object
                        creation_timestamp REAL NOT NULL,
                        usage_count INTEGER DEFAULT 0,
                        last_accessed REAL DEFAULT 0,
                        validation_status TEXT DEFAULT 'pending',
                        coherence_score REAL DEFAULT 0.0,
                        metaphysical_coordinates TEXT DEFAULT '{}' -- JSON object
                    )
                """
                )

                # Create indexes for performance optimization
                self._create_indexes(cursor)

                conn.commit()
                conn.close()
                logging.info("Database initialized successfully with all tables and indexes.")

            except Exception as e:
                logging.error(f"Failed to initialize database: {e}")
                raise

    def _create_indexes(self, cursor):
        """Create database indexes for optimal query performance."""
        indexes = [
            "CREATE INDEX IF NOT EXISTS idx_system_log_timestamp ON system_log (timestamp)",
            "CREATE INDEX IF NOT EXISTS idx_system_log_source ON system_log (source)",
            "CREATE INDEX IF NOT EXISTS idx_goals_status ON goals (status)",
            "CREATE INDEX IF NOT EXISTS idx_goals_priority ON goals (priority DESC)",
            "CREATE INDEX IF NOT EXISTS idx_nodes_parent ON nodes (parent_id)",
            "CREATE INDEX IF NOT EXISTS idx_nodes_created ON nodes (created_at)",
            "CREATE INDEX IF NOT EXISTS idx_relations_src ON relations (src)",
            "CREATE INDEX IF NOT EXISTS idx_relations_tgt ON relations (tgt)",
            "CREATE INDEX IF NOT EXISTS idx_relations_type ON relations (type)",
            "CREATE INDEX IF NOT EXISTS idx_glyphs_spatial ON semantic_glyphs (center_x, center_y)",
            "CREATE INDEX IF NOT EXISTS idx_glyphs_complexity ON semantic_glyphs (semantic_complexity)",
            "CREATE INDEX IF NOT EXISTS idx_glyphs_usage ON semantic_glyphs (usage_count DESC, last_accessed DESC)",
            "CREATE INDEX IF NOT EXISTS idx_glyphs_validation ON semantic_glyphs (validation_status, coherence_score DESC)",
        ]

        for index_sql in indexes:
            try:
                cursor.execute(index_sql)
            except sqlite3.Error as e:
                logging.warning(f"Index creation warning: {e}")

    def save(self, table_name: str, data_dict: dict[str, Any]) -> bool:
        """
        Saves a dictionary of data to a specified table.
        Uses INSERT OR REPLACE for upsert functionality.

        Args:
            table_name: Name of the target table
            data_dict: Dictionary containing the data to save

        Returns:
            bool: True if successful, False otherwise
        """
        if not self._validate_table_name(table_name):
            logging.error(f"Invalid table name: {table_name}")
            return False

        with self.lock:
            conn = self._get_connection()
            try:
                cursor = conn.cursor()

                # Prepare data for insertion
                columns = list(data_dict.keys())
                placeholders = ["?" for _ in columns]
                values = []

                # Convert complex objects to JSON strings
                for key, value in data_dict.items():
                    if isinstance(value, (dict, list)):
                        values.append(json.dumps(value))
                    elif value is None:
                        values.append(None)
                    else:
                        values.append(value)

                # Build and execute SQL
                columns_str = ", ".join(columns)
                placeholders_str = ", ".join(placeholders)
                sql = f"INSERT OR REPLACE INTO {table_name} ({columns_str}) VALUES ({placeholders_str})"

                cursor.execute(sql, values)
                conn.commit()

                logging.info(
                    f"Successfully saved data to table '{table_name}' with {len(data_dict)} fields."
                )
                return True

            except sqlite3.Error as e:
                logging.error(f"Database error saving to '{table_name}': {e}")
                conn.rollback()
                return False
            except Exception as e:
                logging.error(f"Unexpected error saving to '{table_name}': {e}")
                conn.rollback()
                return False
            finally:
                conn.close()

    def query(self, sql: str, params: tuple = ()) -> list[dict[str, Any]]:
        """
        Execute a SELECT query and return results as list of dictionaries.

        Args:
            sql: SQL query string
            params: Query parameters tuple

        Returns:
            List of dictionaries representing query results
        """
        with self.lock:
            conn = self._get_connection()
            try:
                conn.row_factory = sqlite3.Row  # Enable column access by name
                cursor = conn.cursor()
                cursor.execute(sql, params)

                results = []
                for row in cursor.fetchall():
                    row_dict = dict(row)
                    # Try to parse JSON fields
                    for key, value in row_dict.items():
                        if isinstance(value, str) and value.startswith(("{", "[")):
                            try:
                                row_dict[key] = json.loads(value)
                            except json.JSONDecodeError:
                                pass  # Keep as string if not valid JSON
                    results.append(row_dict)

                return results

            except sqlite3.Error as e:
                logging.error(f"Database query error: {e}")
                return []
            except Exception as e:
                logging.error(f"Unexpected query error: {e}")
                return []
            finally:
                conn.close()

    def execute(self, sql: str, params: tuple = ()) -> bool:
        """
        Execute a non-SELECT SQL statement (INSERT, UPDATE, DELETE).

        Args:
            sql: SQL statement string
            params: Statement parameters tuple

        Returns:
            bool: True if successful, False otherwise
        """
        with self.lock:
            conn = self._get_connection()
            try:
                cursor = conn.cursor()
                cursor.execute(sql, params)
                conn.commit()

                logging.info(
                    f"Successfully executed SQL statement. Rows affected: {cursor.rowcount}"
                )
                return True

            except sqlite3.Error as e:
                logging.error(f"Database execution error: {e}")
                conn.rollback()
                return False
            except Exception as e:
                logging.error(f"Unexpected execution error: {e}")
                conn.rollback()
                return False
            finally:
                conn.close()

    def get_node(self, node_id: str) -> dict[str, Any] | None:
        """Retrieve a specific ontological node by ID."""
        results = self.query("SELECT * FROM nodes WHERE id = ?", (node_id,))
        return results[0] if results else None

    def get_goals_by_status(self, status: str) -> list[dict[str, Any]]:
        """Retrieve goals filtered by status."""
        return self.query("SELECT * FROM goals WHERE status = ? ORDER BY priority", (status,))

    def log_system_event(self, source: str, data: dict[str, Any], level: str = "INFO") -> bool:
        """Convenience method to log system events."""
        log_entry = {
            "source": source,
            "log_data": json.dumps(data),
            "log_level": level,
            "timestamp": time.time(),
        }
        return self.save("system_log", log_entry)

    def update_glyph_usage(self, glyph_id: str) -> bool:
        """Update usage statistics for a semantic glyph."""
        return self.execute(
            "UPDATE semantic_glyphs SET usage_count = usage_count + 1, last_accessed = ? WHERE glyph_id = ?",
            (time.time(), glyph_id),
        )

    def get_database_stats(self) -> dict[str, int]:
        """Get basic statistics about database content."""
        stats = {}
        tables = ["system_log", "goals", "nodes", "relations", "semantic_glyphs"]

        for table in tables:
            results = self.query(f"SELECT COUNT(*) as count FROM {table}")
            stats[table] = results[0]["count"] if results else 0

        return stats

    def _validate_table_name(self, table_name: str) -> bool:
        """Validate table name to prevent SQL injection."""
        allowed_tables = {"system_log", "goals", "nodes", "relations", "semantic_glyphs"}
        return table_name in allowed_tables

    def backup_database(self, backup_path: str) -> bool:
        """Create a backup of the database."""
        try:
            with self.lock:
                source = self._get_connection()
                backup = sqlite3.connect(backup_path)
                source.backup(backup)
                backup.close()
                source.close()

            logging.info(f"Database backed up to: {backup_path}")
            return True

        except Exception as e:
            logging.error(f"Database backup failed: {e}")
            return False

    def close(self):
        """Clean shutdown of the persistence manager."""
        logging.info("PersistenceManager shutting down.")
        # No persistent connections to close in this implementation
