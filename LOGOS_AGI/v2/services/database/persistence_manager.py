# logos_agi_v1/services/database/persistence_manager.py

import sqlite3
import json
import logging
import threading

# --- Basic Configuration ---
DB_FILE = "/data/logos_agi.db"  # Path inside the Docker container
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - PERSISTENCE - %(message)s"
)


class PersistenceManager:
    """
    Handles the actual read/write operations to the database.
    This implementation uses SQLite for simplicity.
    It's designed to be thread-safe for use by the DatabaseService.
    """

    def __init__(self, db_file=DB_FILE):
        self.db_file = db_file
        self.lock = threading.Lock()
        self._init_db()

    def _get_connection(self):
        """Creates a new database connection."""
        return sqlite3.connect(self.db_file, check_same_thread=False)

    def _init_db(self):
        """Initializes the database and creates tables if they don't exist."""
        with self.lock:
            try:
                conn = self._get_connection()
                cursor = conn.cursor()

                # Example table: A generic log for all system events/data
                # We store data as a JSON blob for maximum flexibility in this prototype stage.
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS system_log (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                        source TEXT NOT NULL,
                        log_data TEXT NOT NULL
                    )
                """
                )

                # Example table: Goals
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS goals (
                        goal_id TEXT PRIMARY KEY,
                        status TEXT NOT NULL,
                        description TEXT,
                        priority INTEGER,
                        details TEXT, -- JSON blob for extra data
                        created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                        updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
                    )
                """
                )

                conn.commit()
                conn.close()
                logging.info("Database initialized successfully.")
            except Exception as e:
                logging.error(f"Failed to initialize database: {e}")

    def save(self, table_name, data_dict):
        """
        Saves a dictionary of data to a specified table.
        This is a flexible but simplified "upsert" (insert or update).
        """
        with self.lock:
            conn = self._get_connection()
            try:
                cursor = conn.cursor()

                # Sanitize table_name to prevent SQL injection
                if not table_name.isalnum():
                    raise ValueError("Invalid table name")

                columns = ", ".join(data_dict.keys())
                placeholders = ", ".join(["?"] * len(data_dict))
                values = [
                    json.dumps(v) if isinstance(v, (dict, list)) else v for v in data_dict.values()
                ]

                # Using INSERT OR REPLACE for simplicity (requires a PRIMARY KEY in the data)
                # A more robust solution would use INSERT... ON CONFLICT DO UPDATE
                sql = f"INSERT OR REPLACE INTO {table_name} ({columns}) VALUES ({placeholders})"

                cursor.execute(sql, values)
                conn.commit()
                logging.info(f"Successfully saved data to table '{table_name}'.")

            except Exception as e:
                logging.error(f"Error saving to database table '{table_name}': {e}")
                conn.rollback()
            finally:
                conn.close()

    def find(self, table_name, query_dict, limit=1):
        """
        Finds records in a table based on a query dictionary.
        Returns a list of dictionaries.
        """
        with self.lock:
            conn = self._get_connection()
            conn.row_factory = sqlite3.Row  # To get dict-like rows
            try:
                cursor = conn.cursor()

                if not table_name.isalnum():
                    raise ValueError("Invalid table name")

                query_clauses = " AND ".join([f"{key} = ?" for key in query_dict.keys()])
                values = list(query_dict.values())

                sql = f"SELECT * FROM {table_name} WHERE {query_clauses}"
                if limit:
                    sql += f" LIMIT {int(limit)}"

                cursor.execute(sql, values)
                rows = cursor.fetchall()

                # Convert Row objects to plain dicts
                results = [dict(row) for row in rows]
                return results

            except Exception as e:
                logging.error(f"Error finding in database table '{table_name}': {e}")
                return None
            finally:
                conn.close()
