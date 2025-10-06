.PHONY: setup test lint type fmt precommit

setup:
	python -m pip install --upgrade pip
	pip install -e .[dev]
	pre-commit install

fmt:
	ruff format .
	black .

lint:
	ruff check .

type:
	mypy .

test:
	pytest -q

precommit:
	pre-commit run --all-files