# Plan 003: Rename `_inner_value` → `_value` so both families name the contained value identically

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat 7e4f2e7..HEAD -- src/results/results.py`
> If `src/results/results.py` changed since this plan was written, compare the
> "Current state" excerpts against the live code before proceeding; on a
> mismatch, treat it as a STOP condition.

## Status

- **Priority**: P2
- **Effort**: S
- **Risk**: LOW
- **Depends on**: none (but interacts with 005 — see Maintenance notes)
- **Category**: tech-debt
- **Planned at**: commit `7e4f2e7`, 2026-06-21

## Why this matters

`CONTEXT.md` treats "the contained value" as a single domain concept shared by
both families, but the code stores it under two names: the `Result` side
(`Ok`/`Err`) uses `_inner_value`, while the `Option` side (`Some`) uses `_value`.
The two families are meant to read as exact mirrors — that symmetry is the
property an AI explorer (and a human) relies on most. This plan removes the
naming tax with a purely mechanical, **internal-only** rename on the `Result`
side: `_inner_value` → `_value` (and the constructor parameter `inner_value` →
`value`). The attribute is private (`__slots__`/underscore), so this changes no
public API and no behavior.

**Deliberately scoped to the rename (the "cheap rung").** The deeper option — a
shared value-carrier base/mixin to also de-duplicate the `__eq__`/`__hash__`/
`__repr__` trio — is **out of scope**: `docs/decisions/issue-13-split-option-module.md`
§E2 already rejected a shared private base as YAGNI for this codebase, and the
duplication is four short, stable methods. Do not introduce a carrier here.

## Current state

- `src/results/results.py` — defines `Ok` and `Err`. The private attribute is
  `_inner_value` throughout. There are ~40 occurrences. Representative excerpts:

  `Ok` (lines 200-220):

  ```python
  @final
  class Ok[T](Result[T, Any]):
      __slots__ = ("_inner_value",)
      __match_args__ = ("_inner_value",)

      UNWRAP_ERROR_MESSAGE = "Called `.%s` on an [`Ok`] value: %s"

      def __iter__(self) -> Iterator[T]:
          yield self._inner_value
      ...
      def __init__(self, inner_value: T) -> None:
          self._inner_value = inner_value
  ```

  `Err` (lines 305-325):

  ```python
  @final
  class Err[E](Result[Any, E]):
      __slots__ = ("_inner_value",)
      __match_args__ = ("_inner_value",)
      ...
      def __init__(self, inner_value: E) -> None:
          self._inner_value = inner_value
  ```

- The mirror name already in use on the `Option` side
  (`src/results/option.py:420-430`), which this rename aligns to:

  ```python
  @final
  class Some[T](Option[T]):
      __slots__ = ("_value",)
      __match_args__ = ("_value",)

      def __init__(self, value: T) -> None:
          if value is None:
              raise ValueError("Some(None) is forbidden; use Null() for absence")
          self._value = value
  ```

- Confirmed scope of the token (run to reproduce): `grep -rn "_inner_value" src tests`
  returns matches **only** in `src/results/results.py`. (It also appears in
  several `docs/decisions/*.md` files — those are historical records and are
  **out of scope**; do not edit them.) No test references `_inner_value`.

- Why this is safe for pattern matching: `__match_args__` is positional, so
  `case Ok(v)` binds by position regardless of the underlying attribute name —
  renaming the entry in `__match_args__` keeps matching working.

## Commands you will need

| Purpose         | Command                                             | Expected on success            |
|-----------------|---------------------------------------------------- |--------------------------------|
| Install         | `uv sync`                                           | exit 0                         |
| Tests (Result)  | `uv run pytest tests/results/test_result.py -q`     | all pass                       |
| Tests (all)     | `uv run pytest -q`                                  | all pass                       |
| Typecheck       | `uv run mypy src tests`                             | `Success: no issues found ...` |
| Lint            | `uv run ruff check`                                 | `All checks passed!`           |
| Format the file | `uv run ruff format src/results/results.py`         | reformats 0 / normalizes edits |
| Confirm rename  | `grep -rn "_inner_value" src tests`                 | **no matches**                 |

## Scope

**In scope** (the only file you should modify):

- `src/results/results.py`.

**Out of scope** (do NOT touch):

- `src/results/option.py` — already uses `_value`.
- `docs/decisions/*.md` — historical references to `_inner_value` stay as written.
- `__eq__` / `__hash__` / `__repr__` deduplication / any shared carrier base —
  explicitly rejected (issue-13 §E2). This plan only renames.
- Public behavior: no message text, no hashing formula, no equality semantics
  change. (The `UNWRAP_ERROR_MESSAGE` strings stay byte-identical; only the
  `repr(self._inner_value)` *expression* changes to `repr(self._value)`.)

## Git workflow

- Branch: `advisor/003-rename-inner-value-to-value`.
- Commit message style: conventional commits (e.g.
  `refactor(result): rename _inner_value -> _value to mirror the Option side`).
  No `!` — this is internal-only, not a breaking change.
- Do NOT push or open a PR unless the operator instructed it.

## Steps

### Step 1: Rename the attribute everywhere in `results.py`

In `src/results/results.py` **only**, replace every occurrence of the token
`_inner_value` with `_value`. This covers `__slots__`, `__match_args__`, all
method bodies, the `repr(...)` calls inside `UNWRAP_ERROR_MESSAGE % (...)`, the
`isinstance(other, Ok) and self._inner_value == other._inner_value` comparisons,
the `raise exc from self._inner_value` line, and the `__init__` assignments.

A safe way to do it (token is unique to this file):

```text
# from the repo root
python - <<'PY'
import pathlib
p = pathlib.Path("src/results/results.py")
p.write_text(p.read_text().replace("_inner_value", "_value"))
print("done")
PY
```

(Or do the equivalent with your editor's replace-all, scoped to this one file.)

**Verify**: `grep -rn "_inner_value" src tests` → **no matches**.

### Step 2: Rename the constructor parameter to match the Option side

After Step 1, the two `__init__` signatures read `def __init__(self, value: T)`
**only if** you also renamed the parameter. Step 1 renamed `_inner_value` but the
parameter is spelled `inner_value` (no leading underscore), so it is untouched.
Rename it now for full symmetry with `Some.__init__(self, value)`:

- `Ok.__init__`: `def __init__(self, inner_value: T) -> None:` →
  `def __init__(self, value: T) -> None:` and body `self._value = value`.
- `Err.__init__`: `def __init__(self, inner_value: E) -> None:` →
  `def __init__(self, value: E) -> None:` and body `self._value = value`.

`Ok`/`Err` are constructed positionally everywhere (`Ok(x)`, `Err(e)`), so the
parameter rename breaks nothing.

**Verify**: `grep -n "inner_value" src/results/results.py` → **no matches**.

### Step 3: Format, type-check, test

```text
uv run ruff format src/results/results.py
uv run ruff check
uv run mypy src tests
uv run pytest -q
```

**Verify**: ruff clean, mypy `Success: no issues found in 9 source files`, all
215 tests pass.

## Test plan

- No new tests required — this is a behavior-preserving internal rename, and the
  existing suite already exercises `Ok`/`Err` equality, hashing, repr, iteration,
  unwrap, and pattern-binding (`tests/results/test_result.py`).
- The regression guard is the existing suite plus `mypy` staying green and the
  `grep` confirming the old token is gone.
- Verification: `uv run pytest -q` → all pass; `grep -rn "_inner_value" src tests`
  → empty.

## Done criteria

Machine-checkable. ALL must hold:

- [ ] `grep -rn "_inner_value" src tests` returns no matches
- [ ] `grep -n "inner_value" src/results/results.py` returns no matches
- [ ] `uv run pytest -q` passes (still 215 tests)
- [ ] `uv run mypy src tests` → `Success: no issues found in 9 source files`
- [ ] `uv run ruff check` → `All checks passed!`
- [ ] Only `src/results/results.py` (and `plans/README.md`) changed (`git status`)
- [ ] `plans/README.md` status row for 003 updated

## STOP conditions

Stop and report back (do not improvise) if:

- `grep -rn "_inner_value" src tests` shows matches **outside**
  `src/results/results.py` (e.g. a test started depending on the private name) —
  the rename's blast radius is larger than this plan assumed.
- Any test fails after the rename — a failure means the replace caught something
  it shouldn't have (e.g. a docstring example or a string literal that must stay
  `_inner_value`); report the diff.
- You find yourself wanting to also touch `__eq__`/`__hash__`/`__repr__` or add a
  base class — that is explicitly out of scope; stop and report instead.

## Maintenance notes

- **Interaction with plan 005 (`Result.flatten`).** Plan 005 adds a `flatten`
  method to `Ok` whose body returns the contained value. Its excerpts are
  written against `_inner_value` (this commit). Whichever lands second must use
  the then-current name: if 003 lands first, `Ok.flatten` returns `self._value`;
  the 005 drift check will surface the rename. There is no deep conflict — they
  touch different methods.
- For the reviewer: confirm zero behavioral diff — same hash formula
  (`hash(self._value) * 41`), same `__eq__`, same error-message text. The only
  change is the identifier.
- The duplicated dunder trio across `Ok`/`Err`/`Some`/`Null` remains by design
  (issue-13 §E2). If it ever *grows* (the `* 41` salt or equality rule starts
  changing), revisit the carrier idea then — not before.
