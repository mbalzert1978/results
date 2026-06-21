# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

`results` is a dependency-free Python library providing Rust-inspired `Result` (success/failure) and `Option` (presence/absence) types for functional-style error handling. It ships type information (`py.typed`) and targets Python >=3.13.

## Commands

Tooling is managed with `uv` (a `uv.lock` is committed).

```bash
uv sync                                          # install/refresh dev environment
uv run pytest                                    # run the full test suite
uv run pytest tests/results/test_result.py       # run one test file
uv run pytest tests/results/test_result.py::test_map   # run a single test
uv run pytest -k pattern_matching                # run tests matching an expression
uv run pytest --cov=results                      # run with coverage (pytest-cov is installed)
uv run mypy src tests                            # type-check
uv run ruff check                                # lint
uv run ruff format                               # format
```

There is no pytest/ruff/mypy configuration block in `pyproject.toml` — all three run with their default settings.

## Architecture

The entire library is one module, [src/results/results.py](src/results/results.py); [src/results/__init__.py](src/results/__init__.py) only re-exports the public names. There are two parallel, Rust-inspired type families with a deliberately different internal design:

__`Result[T, E]`__ is an `abc.ABC` with two `@final` concrete subclasses, `Ok[T]` (declared `Result[T, Any]`) and `Err[E]` (declared `Result[Any, E]`). Every method is abstract on the base and implemented on both subclasses — behavior is selected by *polymorphism*, never by `isinstance`/flag checks inside a method. When adding a method to `Result`, add the `@abc.abstractmethod` stub plus an `Ok` and an `Err` implementation.

__`Option[T]`__ is a *single concrete class* (not split into subclasses). It stores `_content: T | None` and uses `None` as the "null" sentinel. `Some(value)` and `Null()` are module-level factory functions delegating to the `Option.some()` / `Option.none()` classmethods. Consequences to keep in mind:

- `Some(None)` is indistinguishable from `Null()`.
- `unwrap_or` / `unwrap_or_else` test truthiness (`self._content or default`), so falsy values like `0` or `""` are treated like absence.

__Cross-conversions__ tie the two families together: `Result.ok()` / `Result.err()` produce an `Option`; `Option.ok_or()` / `Option.ok_or_else()` produce a `Result`; `Option.transpose()` swaps an `Option[Result]` into a `Result[Option]`.

__Constructors from callables__: `Result.as_result` (decorator) and `Result.from_fn` wrap exception-raising functions (catching `Exception` into `Err`); `Option.as_option` (decorator) and `Option.from_fn` wrap `None`-returning functions into `Some`/`Null`.

__Failure mode__: unwrap-style failures raise `UnwrapFailedError` (subclass of `ResultError`); `Option`/transpose errors derive from `OptionError` / `TransposeError`. `Err.unwrap()` chains the original exception via `raise ... from` when the inner value is a `BaseException`.

__Pattern matching__ relies on `__match_args__`: match `Ok`/`Err` on their inner value (`case Ok(v)`), and match `Option` on its content (`case Option(value)` / `case Option(None)`).

The codebase uses PEP 695 generics throughout — `class Result[T, E]`, method-level `def map[U](...)`, and ParamSpec via `[**P]`. Preserve this style rather than reverting to `TypeVar`/`Generic`.

## Tests

Tests live in `tests/results/` and lean heavily on `pytest.mark.parametrize` with explicit human-readable `ids=` for each case. Follow that convention — add cases to the existing parametrized tables rather than writing one-off test functions, and import the public API from `results` (e.g. `from results import Ok, Err, Some, Null`).

## Note

The "Project Structure" section of [README.md](README.md) is stale — it lists `results.pyi` and `test_factories.py`, neither of which exists.

## graphify

This project has a knowledge graph at graphify-out/ with god nodes, community structure, and cross-file relationships.

Rules:

- For codebase questions, first run `graphify query "<question>"` when graphify-out/graph.json exists. Use `graphify path "<A>" "<B>"` for relationships and `graphify explain "<concept>"` for focused concepts. These return a scoped subgraph, usually much smaller than GRAPH_REPORT.md or raw grep output.
- If graphify-out/wiki/index.md exists, use it for broad navigation instead of raw source browsing.
- Read graphify-out/GRAPH_REPORT.md only for broad architecture review or when query/path/explain do not surface enough context.
- After modifying code, run `graphify update .` to keep the graph current (AST-only, no API cost).
