# LOGOS PXL Core - Development Guide

## Local QA

Setup development environment:
```bash
make setup
```

Run quality assurance checks:
```bash
make lint type test
```

Format code:
```bash
make fmt
```

Run pre-commit hooks on all files:
```bash
make precommit
```

## CI Matrix

The continuous integration pipeline enforces:

- **Ruff** → Style and static checks
- **Black** → Code formatting gate  
- **Mypy** → Strict type checking
- **Pytest** → Fast unit and smoke tests

## Testing Strategy

### Smoke Tests
Fast, essential checks marked with `@pytest.mark.smoke`:
- Health endpoint verification
- Service import validation
- Environment variable configuration
- Tool routing dispatch logic

### Unit Tests
Comprehensive tests with mocked dependencies:
- Request/response validation
- Proof token flow verification
- Error handling scenarios

Run smoke tests only:
```bash
pytest -m smoke
```

Run all tests:
```bash
pytest
```

## Development Workflow

1. Install pre-commit hooks: `pre-commit install`
2. Make changes with automatic formatting and linting
3. Run tests locally: `make test`
4. Push - CI will validate everything automatically

## Type Checking

The codebase uses strict mypy configuration:
- All functions must have type annotations
- No `Any` types allowed without explicit ignore
- Return types must be specified
- Import resolution enforced

Check types:
```bash
make type
```

## Code Quality

- **Line length**: 100 characters (Black + Ruff compatible)
- **Python version**: 3.11+ required
- **Import sorting**: Automatic via Ruff
- **Formatting**: Black with 100-char line length
- **Linting**: Ruff with comprehensive ruleset

Quality gates will prevent commits that don't meet standards.