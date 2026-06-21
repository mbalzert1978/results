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

The library is split across two modules: the `Result` family (`Result`/`Ok`/`Err`) plus the error hierarchy live in [src/results/results.py](src/results/results.py), and the `Option` family (`Option`/`Some`/`Null`) lives in [src/results/option.py](src/results/option.py); [src/results/__init__.py](src/results/__init__.py) re-exports the public names from both. The two modules are mutually dependent — `results.py` imports `Some`/`Null` at module top, while `option.py` breaks the cycle with function-local (deferred) imports of `Ok`/`Err`/`UnwrapFailedError` inside the few Option methods that construct the Result family (see [docs/decisions/issue-13-split-option-module.md](docs/decisions/issue-13-split-option-module.md)). There are two parallel, Rust-inspired type families with a deliberately different internal design:

__`Result[T, E]`__ is an `abc.ABC` with two `@final` concrete subclasses, `Ok[T]` (declared `Result[T, Any]`) and `Err[E]` (declared `Result[Any, E]`). Every method is abstract on the base and implemented on both subclasses — behavior is selected by *polymorphism*, never by `isinstance`/flag checks inside a method. When adding a method to `Result`, add the `@abc.abstractmethod` stub plus an `Ok` and an `Err` implementation.

__`Option[T]`__ mirrors `Result`'s design: an `abc.ABC` with two `@final` concrete subclasses, `Some[T]` (value present) and `Null[T]` (value absent). Absence is encoded in the *type* — there is no stored `None` sentinel — so behavior is selected by *polymorphism*, never by `_content is None` or truthiness checks inside a method. `Some(value)` and `Null()` are the only constructors (the base ABC is not directly instantiable). When adding a method to `Option`, add the `@abc.abstractmethod` stub plus a `Some` and a `Null` implementation. Consequences to keep in mind:

- `Some(None)` is forbidden and raises `ValueError` (guard in `Some.__init__`) — `None` is solely the absence sentinel, represented only by `Null()`. Any path that would wrap `None` raises too: `Ok(None).ok()`, `Some(5).map(lambda _: None)`, `Some(Ok(None)).transpose()`. Rule of thumb: `map` (`T -> U`) must not produce `None`; for a step that may be absent use `and_then` (`T -> Option[U]`), and for absence use `Null()`.
- `unwrap_or` / `unwrap_or_else` / `__iter__` dispatch structurally on the variant, so falsy values like `0` / `""` / `[]` are treated as *present* (e.g. `Some(0).unwrap_or(42) == 0`). `None` is not a present value — `Some(None)` raises.

__Cross-conversions__ tie the two families together: `Result.ok()` / `Result.err()` produce an `Option`; `Option.ok_or()` / `Option.ok_or_else()` produce a `Result`; `Option.transpose()` swaps an `Option[Result]` into a `Result[Option]`.

__Constructors from callables__: `Result.as_result` (decorator) and `Result.from_fn` wrap exception-raising functions (catching `Exception` into `Err`); `Option.as_option` (decorator) and `Option.from_fn` wrap `None`-returning functions into `Some`/`Null`.

__Failure mode__: unwrap-style failures raise `UnwrapFailedError` (subclass of `ResultError`) — including `Option.expect`/`Option.unwrap`, which use this Result-side class. `Err.unwrap()` chains the original exception via `raise ... from` when the inner value is a `BaseException`. `Option.transpose`/`Result.transpose` raise `TransposeError` (also a `ResultError` subclass) when the payload is not the expected `Result`/`Option` wrapper — a contract violation, never silently wrapped.

__Pattern matching__ relies on `__match_args__`: match `Ok`/`Err` on their inner value (`case Ok(v)`), and match the `Option` variants directly (`case Some(v)` binds the value; `case Null()` matches the empty variant).

The codebase uses PEP 695 generics throughout — `class Result[T, E]`, method-level `def map[U](...)`, and ParamSpec via `[**P]`. Preserve this style rather than reverting to `TypeVar`/`Generic`.

__Ubiquitous Language__: [CONTEXT.md](CONTEXT.md) is the authoritative glossary for the domain terms used here (`Result`/`Ok`/`Err`, `Option`/`Some`/`Null`, `unwrap`/`map`/`and_then`, the cross-conversions, the callable constructors, and the error hierarchy), including the deliberate "what it is NOT" boundaries. Consult it when a term is ambiguous or when writing user-facing names, docstrings, or messages, and keep it in sync: whenever you add, rename, or change the contract of a public type/method, update the matching entry in `CONTEXT.md` (the code is the source of truth — the glossary follows it).

## Tests

Tests live in `tests/results/` and lean heavily on `pytest.mark.parametrize` with explicit human-readable `ids=` for each case. Follow that convention — add cases to the existing parametrized tables rather than writing one-off test functions, and import the public API from `results` (e.g. `from results import Ok, Err, Some, Null`).

## Note

The "Project Structure" section of [README.md](README.md) now reflects the real layout (`src/results/option.py` + `src/results/results.py`, `tests/results/test_public_api.py`).

## graphify

This project has a knowledge graph at graphify-out/ with god nodes, community structure, and cross-file relationships.

Rules:

- For codebase questions, first run `graphify query "<question>"` when graphify-out/graph.json exists. Use `graphify path "<A>" "<B>"` for relationships and `graphify explain "<concept>"` for focused concepts. These return a scoped subgraph, usually much smaller than GRAPH_REPORT.md or raw grep output.
- If graphify-out/wiki/index.md exists, use it for broad navigation instead of raw source browsing.
- Read graphify-out/GRAPH_REPORT.md only for broad architecture review or when query/path/explain do not surface enough context.
- After modifying code, run `graphify update .` to keep the graph current (AST-only, no API cost).
