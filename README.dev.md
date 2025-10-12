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

## Windows notes
Use WSL for best results.
```
# From repo root (WSL Ubuntu)
python3 tools/gen_coq_index.py
make docs-index
make verify-kernel
make coq-test
```

## Suggested First PRs

Welcome to the LOGOS PXL Core project! Here are some good starting points for your first contributions:

### Documentation Improvements
- **Improve error messages**: Add more descriptive error messages in validation functions
- **Add docstrings**: Add comprehensive docstrings to public functions missing them
- **Update comments**: Improve code comments for complex algorithms

### Testing Enhancements
- **Add unit tests**: Write tests for functions that lack coverage
- **Improve test data**: Add more edge cases to existing test suites
- **Add integration tests**: Test component interactions

### Code Quality
- **Performance optimizations**: Identify and optimize slow code paths
- **Refactor complex functions**: Break down large functions into smaller, testable units
- **Add type hints**: Improve type annotations where missing

### Feature Additions
- **New validation rules**: Add domain-specific validation logic
- **Configuration options**: Add new configurable parameters
- **Logging improvements**: Enhance logging and monitoring capabilities

### Infrastructure
- **CI/CD improvements**: Enhance the build pipeline
- **Documentation generation**: Improve automated documentation tools
- **Development tools**: Add helpful development utilities

Start with issues labeled `good first issue` or `beginner-friendly` in the repository.
