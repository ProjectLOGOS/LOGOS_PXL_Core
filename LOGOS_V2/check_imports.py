#!/usr/bin/env python3
"""
Import checker for LOGOS_V2
"""
import os
import sys
import ast
import importlib.util

def check_imports(file_path):
    try:
        with open(file_path, 'r') as f:
            content = f.read()

        tree = ast.parse(content, filename=file_path)

        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    module_name = alias.name.split('.')[0]
                    if module_name not in ['os', 'sys', 'json', 'time', 'datetime', 'pathlib', 'typing', 'collections', 'functools', 'itertools', 'math', 'random', 're', 'subprocess', 'threading', 'multiprocessing', 'asyncio', 'logging', 'warnings', 'traceback', 'inspect', 'ast', 'pickle', 'sqlite3', 'hashlib', 'hmac', 'secrets', 'uuid', 'tempfile', 'shutil', 'glob', 'fnmatch', 'linecache', 'tokenize', 'token', 'keyword', 'ast', 'symtable', 'symbol', 'compiler', 'dis', 'pickletools', 'copyreg', 'copy', 'pprint', 'reprlib', 'enum', 'numbers', 'decimal', 'fractions', 'cmath', 'operator', 'contextlib', 'abc', 'atexit', 'weakref', 'gc', 'inspect', 'site', 'warnings', 'contextvars', 'concurrent', 'multiprocessing', 'subprocess', 'sched', 'queue', 'dummy_thread', '_thread', 'io', 'codecs', 'unicodedata', 'stringprep', 're', 'difflib', 'textwrap', 'string', 'binary', 'struct', 'weakref', 'list', 'tuple', 'range', 'dict', 'set', 'frozenset', 'slice', 'property', 'classmethod', 'staticmethod', 'super', 'type', 'object', 'int', 'float', 'complex', 'bool', 'str', 'bytes', 'bytearray', 'memoryview', 'None', 'Ellipsis', 'NotImplemented', 'True', 'False']:
                        try:
                            importlib.import_module(module_name)
                        except ImportError:
                            print(f'Import issue in {file_path}: {module_name}')
            elif isinstance(node, ast.ImportFrom):
                module_name = node.module.split('.')[0] if node.module else ''
                if module_name and module_name not in ['os', 'sys', 'json', 'time', 'datetime', 'pathlib', 'typing', 'collections', 'functools', 'itertools', 'math', 'random', 're', 'subprocess', 'threading', 'multiprocessing', 'asyncio', 'logging', 'warnings', 'traceback', 'inspect', 'ast', 'pickle', 'sqlite3', 'hashlib', 'hmac', 'secrets', 'uuid', 'tempfile', 'shutil', 'glob', 'fnmatch', 'linecache', 'tokenize', 'token', 'keyword', 'ast', 'symtable', 'symbol', 'compiler', 'dis', 'pickletools', 'copyreg', 'copy', 'pprint', 'reprlib', 'enum', 'numbers', 'decimal', 'fractions', 'cmath', 'operator', 'contextlib', 'abc', 'atexit', 'weakref', 'gc', 'inspect', 'site', 'warnings', 'contextvars', 'concurrent', 'multiprocessing', 'subprocess', 'sched', 'queue', 'dummy_thread', '_thread', 'io', 'codecs', 'unicodedata', 'stringprep', 're', 'difflib', 'textwrap', 'string', 'binary', 'struct', 'weakref', 'list', 'tuple', 'range', 'dict', 'set', 'frozenset', 'slice', 'property', 'classmethod', 'staticmethod', 'super', 'type', 'object', 'int', 'float', 'complex', 'bool', 'str', 'bytes', 'bytearray', 'memoryview', 'None', 'Ellipsis', 'NotImplemented', 'True', 'False']:
                    try:
                        importlib.import_module(module_name)
                    except ImportError:
                        print(f'ImportFrom issue in {file_path}: {module_name}')
    except Exception as e:
        print(f'Error checking {file_path}: {e}')

if __name__ == "__main__":
    for root, dirs, files in os.walk('.'):
        for file in files:
            if file.endswith('.py'):
                check_imports(os.path.join(root, file))