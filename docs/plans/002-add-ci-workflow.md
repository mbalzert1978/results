# Plan 002: Add a GitHub Actions CI pipeline that enforces the green baseline

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat 7e4f2e7..HEAD -- pyproject.toml .python-version` and `ls .github/workflows 2>/dev/null`
> If `.github/workflows/ci.yml` already exists, STOP — CI may already be set up.

## Status

- **Priority**: P1
- **Effort**: S
- **Risk**: LOW
- **Depends on**: none
- **Category**: dx
- **Planned at**: commit `7e4f2e7`, 2026-06-21

## Why this matters

The repo is configured for quality — `mypy`, `ruff`, `pytest`, and `pytest-cov`
are all declared as dev dependencies (`pyproject.toml:20`) and the working tree
is currently green (215 tests pass, `mypy` clean, `ruff check` clean). But
**nothing runs them automatically**: there is no `.github/` directory, no
pre-commit config, no tox/nox. Every check depends on a human remembering to run
it locally before merging. For a typed, dependency-free library that other plans
in this batch will modify, an automated CI gate on push/PR is the missing
verification baseline — it makes "the suite is green" a property of `main`
instead of a hope.

## Current state

- No CI exists. Confirm with: `ls -la .github 2>/dev/null` → no such directory.
- Tooling is `uv`-managed. `uv.lock` is committed. Relevant facts:
  - `pyproject.toml:12` → `requires-python = ">=3.13"`.
  - `.python-version` → `3.13`.
  - `pyproject.toml:19-20` → dev group: `mypy>=1.14.1`, `pytest-cov>=6.0.0`,
    `pytest>=8.3.4`, `ruff>=0.8.6`.
- The exact local commands that are known-green at this commit (verify them
  yourself in Step 1 before encoding them in CI):
  - `uv run ruff check` → `All checks passed!`
  - `uv run mypy src tests` → `Success: no issues found in 9 source files`
  - `uv run pytest --cov=results` → `215 passed`, total coverage 99%.
- **Known caveat — do not add `ruff format --check` as a gate.** At this commit,
  `uv run ruff format --check` reports `tests/results/test_public_api.py` would
  be reformatted. Enforcing format in CI now would make the pipeline red on its
  first run. Format enforcement is intentionally deferred (see Maintenance
  notes) — it needs a separate change that first runs `uv run ruff format`.

## Commands you will need

| Purpose      | Command                                                                                                  | Expected on success                                                                                |
|--------------|--------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------- |
| Install      | `uv sync`                                                                                                | exit 0                                                                                             |
| Lint         | `uv run ruff check`                                                                                      | `All checks passed!`                                                                               |
| Typecheck    | `uv run mypy src tests`                                                                                  | `Success: no issues found ...`                                                                     |
| Tests + cov  | `uv run pytest --cov=results`                                                                            | `215 passed`, coverage table                                                                       |
| YAML sanity  | `uv run python -c "import yaml,sys; yaml.safe_load(open('.github/workflows/ci.yml')); print('yaml ok')"` | `yaml ok` (if `yaml` import fails, skip — it is not a dependency; rely on the Actions run instead) |

## Scope

**In scope** (the only files you should create/modify):

- `.github/workflows/ci.yml` (create).

**Out of scope** (do NOT touch):

- `pyproject.toml`, `uv.lock`, any source or test file. This plan adds CI only;
  it must not change a single line of library code or config.
- `ruff format` enforcement (deferred — see Maintenance notes).
- Release/publish workflows, coverage upload services, badges in README.

## Git workflow

- Branch: `advisor/002-add-ci-workflow`.
- Commit message style: conventional commits (e.g.
  `ci: add GitHub Actions workflow (ruff, mypy, pytest) on push/PR`).
- Do NOT push or open a PR unless the operator instructed it.

## Steps

### Step 1: Re-confirm the gates are green locally

Run, and confirm each expected result, before writing the workflow:

```text
uv sync
uv run ruff check
uv run mypy src tests
uv run pytest --cov=results
```

If any of these is NOT green at this commit, STOP and report — CI must encode
commands that already pass.

**Verify**: all four succeed as described in "Commands you will need".

### Step 2: Create the workflow file

Create `.github/workflows/ci.yml` with exactly this content:

```yaml
name: CI

on:
  push:
    branches: [main]
  pull_request:

permissions:
  contents: read

concurrency:
  group: ci-${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install uv
        uses: astral-sh/setup-uv@v5
        with:
          enable-cache: true

      - name: Set up Python
        run: uv python install

      - name: Install dependencies
        run: uv sync --frozen

      - name: Lint (ruff)
        run: uv run ruff check

      - name: Type-check (mypy)
        run: uv run mypy src tests

      - name: Test (pytest + coverage)
        run: uv run pytest --cov=results
```

Notes the executor should not "improve" away:

- `uv sync --frozen` makes CI fail if `uv.lock` is out of date rather than
  silently updating it — the lockfile is committed, so this is correct.
- `uv python install` reads `.python-version` (`3.13`), keeping CI on the same
  interpreter as local dev. No version matrix — `requires-python` is a single
  floor and the maintainer develops on 3.13.
- Pin notes: `actions/checkout@v4`, `astral-sh/setup-uv@v5` are current major
  tags. If a newer major is the documented default when you run this, prefer it,
  but do not downgrade.

**Verify**: `uv run python -c "import yaml; yaml.safe_load(open('.github/workflows/ci.yml')); print('yaml ok')"`
→ `yaml ok`. (If `yaml` is not importable, that's fine — it is not a project
dependency; instead just re-read the file and confirm indentation is 2-space and
consistent.)

### Step 3: Confirm no library code changed

**Verify**: `git status --porcelain` shows only `.github/workflows/ci.yml` (and
`plans/README.md` once you update it). No `src/`, `tests/`, `pyproject.toml`, or
`uv.lock` changes.

## Test plan

- No application tests are added — this plan adds infrastructure.
- The workflow itself is the "test": once pushed, the Actions run must go green.
  Because Step 1 confirmed every encoded command passes locally against a frozen
  lockfile, a green run is expected. If the operator pushes and the run is red,
  treat the failing step's log as the report-back.

## Done criteria

Machine-checkable. ALL must hold:

- [ ] `.github/workflows/ci.yml` exists and parses as valid YAML
- [ ] The workflow references `uv run ruff check`, `uv run mypy src tests`, and
      `uv run pytest --cov=results` — and does NOT reference `ruff format`
- [ ] `git status --porcelain` lists only `.github/workflows/ci.yml` and
      `plans/README.md`
- [ ] `uv run pytest -q` still passes locally (sanity: nothing else changed)
- [ ] `plans/README.md` status row for 002 updated

## STOP conditions

Stop and report back (do not improvise) if:

- `.github/workflows/` already contains a workflow — report what's there instead
  of overwriting it.
- Any of the four gate commands in Step 1 is NOT green at this commit — do not
  encode a failing command into CI.
- `uv sync --frozen` fails locally with a lockfile-mismatch error — that means
  `uv.lock` is stale; report it rather than regenerating the lock in this plan.

## Maintenance notes

- **Deferred follow-up — format enforcement.** Once someone runs
  `uv run ruff format` (which will reformat `tests/results/test_public_api.py`)
  and commits it, add a `Format (ruff)` step running `uv run ruff format --check`
  to this workflow. It is omitted now only because the tree isn't format-clean
  and CI must not be red on day one.
- For the reviewer: check that triggers are `push` to `main` + `pull_request`,
  that `permissions` is read-only, and that the lockfile is used frozen.
- If a Python version matrix becomes desirable later (e.g. testing 3.13 and a
  future 3.14), convert `check` to a `strategy.matrix` job — out of scope here.
