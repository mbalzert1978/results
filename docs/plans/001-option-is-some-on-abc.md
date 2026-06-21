# Plan 001: `is_some` / `is_some_and` are part of the `Option` typed interface

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat 7e4f2e7..HEAD -- src/results/option.py tests/results/test_option.py CONTEXT.md`
> If any in-scope file changed since this plan was written, compare the
> "Current state" excerpts against the live code before proceeding; on a
> mismatch, treat it as a STOP condition.

## Status

- **Priority**: P1
- **Effort**: S
- **Risk**: LOW
- **Depends on**: none
- **Category**: bug
- **Planned at**: commit `7e4f2e7`, 2026-06-21

## Why this matters

`Some` and `Null` both implement `is_some()` and `is_some_and(...)`, but those
two methods are **not declared on the `Option` abstract base class**. As a
result, any user holding a value typed `Option[T]` (the normal case — that is
the return type of `map`, `filter`, `from_fn`, `and_then`, etc.) gets a static
type error when calling them:

```text
error: "Option[int]" has no attribute "is_some"  [attr-defined]
error: "Option[int]" has no attribute "is_some_and"  [attr-defined]
```

This is an asymmetry bug: the sibling `Result` family **does** declare
`is_ok` / `is_ok_and` on its base (`src/results/results.py:107-113`), so they
work through a `Result[T, E]` reference. `Option` should match. The fix is
additive and low-risk: the concrete implementations already exist on both
subclasses, so we only add the two `@abc.abstractmethod` stubs to the base
(making them visible to the type checker) and lock the behavior in with a
type-checked regression test.

## Current state

- `src/results/option.py` — the `Option` ABC and its two `@final` subclasses.
  - The `Option` base declares abstract methods including `is_none` and
    `is_none_or`, but **not** `is_some` / `is_some_and`. Excerpt (lines 185-219):

    ```python
    @abc.abstractmethod
    def is_none(self) -> bool:
        ...

    @abc.abstractmethod
    def is_none_or(self, fn: Callable[[T], bool]) -> bool:
        ...
        """

    @abc.abstractmethod
    def map[U](self, op: Callable[[T], U]) -> Option[U]:
        ...
    ```

  - The concrete methods **already exist** on both subclasses (do NOT touch
    these — they are correct):
    - `Some` (`src/results/option.py:474-478`):

      ```python
      def is_some(self) -> Literal[True]:
          return True

      def is_some_and(self, op: Callable[[T], bool]) -> bool:
          return op(self._value)
      ```

    - `Null` (`src/results/option.py:593-597`):

      ```python
      def is_some(self) -> Literal[False]:
          return False

      def is_some_and(self, op: Callable[[T], bool]) -> Literal[False]:
          return False
      ```

- Conventions to follow (match exactly):
  - Every `Option` method is `@abc.abstractmethod` on the base plus one
    implementation on each of `Some` and `Null` — behavior by polymorphism,
    never `isinstance`/flag checks. See the existing `is_none` / `is_none_or`
    pair as the structural exemplar.
  - The concrete `is_some_and` uses the parameter name `op` (not `fn`). The new
    abstract stub MUST use `op` too, so the signatures match the existing impls.
  - Method ordering in the base follows the documented convention in
    `docs/decisions/issue-17-option-is-none-or-inspect.md:16-17`:
    `is_none` → `is_none_or` → `is_some` → `is_some_and`. So the new stubs go
    **immediately after `is_none_or` and before `map`**.
  - Docstrings on the base are kept short with a `# Examples:` block, matching
    the surrounding methods.

- Documented vocabulary the change must honor (`CONTEXT.md`):
  - `CONTEXT.md` already names these methods in passing — the `is_none_or`
    entry (line 128) calls itself "Komplement zu `is_some_and`", and the `Some`
    entry (line 102) uses `Some(v).is_some()`. After this change they become
    first-class members of the `Option` interface, mirroring `is_ok`/`is_ok_and`
    on `Result`. `CLAUDE.md` mandates: "whenever you add, rename, or change the
    contract of a public type/method, update the matching entry in `CONTEXT.md`".

## Commands you will need

| Purpose         | Command                                                                 | Expected on success                       |
| --------------- | ----------------------------------------------------------------------- | ----------------------------------------- |
| Install         | `uv sync`                                                               | exit 0                                    |
| Typecheck       | `uv run mypy src tests`                                                 | `Success: no issues found ...`            |
| Tests (Option)  | `uv run pytest tests/results/test_option.py -q`                         | all pass                                  |
| Tests (all)     | `uv run pytest -q`                                                      | all pass                                  |
| Lint            | `uv run ruff check`                                                     | `All checks passed!`                      |
| Format the file | `uv run ruff format src/results/option.py tests/results/test_option.py` | reformats 0 or normalizes only your edits |

## Scope

**In scope** (the only files you should modify):

- `src/results/option.py` — add two abstract method stubs to the `Option` base.
- `tests/results/test_option.py` — add one type-checked regression test.
- `CONTEXT.md` — add a short glossary entry.

**Out of scope** (do NOT touch, even though they look related):

- The concrete `is_some` / `is_some_and` on `Some` and `Null` — already correct.
- `src/results/results.py` — the `Result` side is already correct.
- `docs/decisions/*` — historical records; do not edit.
- Any other `Option` method or its tests.

## Git workflow

- Branch: `advisor/001-option-is-some-on-abc` (or the repo's convention if one
  is evident from `git branch`/PR history).
- Commit message style: conventional commits, matching `git log` (e.g.
  `fix(option): declare is_some/is_some_and on the Option ABC`).
- Do NOT push or open a PR unless the operator instructed it.

## Steps

### Step 1: Add the two abstract stubs to the `Option` base

In `src/results/option.py`, insert the following **between** the `is_none_or`
abstract method and the `map` abstract method (i.e. directly after the
`is_none_or` docstring closes, before `@abc.abstractmethod def map`):

```python
    @abc.abstractmethod
    def is_some(self) -> bool:
        """
        Returns `true` if the option is a [`Some`] value.

        # Examples:

        >>> assert Some(10).is_some()
        >>> assert not Null().is_some()
        """

    @abc.abstractmethod
    def is_some_and(self, op: Callable[[T], bool]) -> bool:
        """
        Returns `true` if the option is [`Some`] and the value inside matches
        the predicate `op`. The complement of `is_none_or`.

        # Examples:

        >>> assert Some(10).is_some_and(is_even)
        >>> assert not Some(15).is_some_and(is_even)
        >>> assert not Null().is_some_and(is_even)
        """
```

Do not add or remove anything else.

**Verify**: `uv run pytest tests/results/test_option.py -q` → all pass (the ABC
can still be subclassed and instantiated as `Some`/`Null`; `Option()` still
raises `TypeError` because both subclasses implement the new abstractmethods).

### Step 2: Add a type-checked regression test

In `tests/results/test_option.py`, add this test (place it near the existing
`test_is_some_when_value_should_return_true`). The point of this test is that it
calls the two methods **through an `Option[int]`-typed reference** — which is
exactly what fails to type-check before Step 1:

```python
def test_is_some_and_is_some_and_callable_through_option_base() -> None:
    # Regression for the typed interface: is_some / is_some_and must be
    # reachable through an Option[T] reference (declared on the ABC), not only
    # on the concrete Some / Null. This guards against them silently slipping
    # off the base again — `uv run mypy src tests` is the real gate here.
    present: Option[int] = Some(10)
    absent: Option[int] = Null()
    assert present.is_some()
    assert not absent.is_some()
    assert present.is_some_and(lambda v: v > 5)
    assert not absent.is_some_and(lambda v: v > 5)
```

**Verify**:

- `uv run mypy src tests` → `Success: no issues found in 9 source files`
  (before Step 1 this same test produces two `attr-defined` errors — that is the
  bug this plan fixes).
- `uv run pytest tests/results/test_option.py -q` → all pass.

### Step 3: Update `CONTEXT.md`

Add a short glossary subsection so the docs follow the code. Insert it
**immediately after** the `### is_none_or / inspect` section and **before** the
`### and_ / xor` section:

```markdown
### is_some / is_some_and

Zwei `Option`-Methoden zum **Abfragen der Variante** auf der Vorhanden-Seite —
das Spiegelbild von `is_ok` / `is_ok_and` auf `Result`:

- `is_some()` — `True`, wenn die Option `Some` ist, sonst `False`.
- `is_some_and(op)` — `True`, wenn die Option `Some(v)` ist **und** `op(v)`
  wahr ergibt; bei `Null` immer `False` (das Prädikat wird nicht aufgerufen).
  Komplement zu `is_none_or`.

Beide sind `@abc.abstractmethod` auf `Option` und je einmal auf `Some` und
`Null` implementiert (polymorpher Dispatch, kein `isinstance`/Flag-Check). Sie
gehören zur abstrakten `Option`-Oberfläche — über eine `Option[T]`-Referenz
typgeprüft aufrufbar.

*Avoid:* annehmen, `is_some_and` werte `op` auch bei `Null` aus. Tut es nicht —
`Null.is_some_and` gibt `False` zurück, ohne `op` zu berühren.
```

**Verify**: `uv run pytest -q` → all pass (no test reads CONTEXT.md, but run
the full suite as a final gate).

## Test plan

- New test: `test_is_some_and_is_some_and_callable_through_option_base` in
  `tests/results/test_option.py`, covering both methods through an `Option[int]`
  reference for the `Some` and `Null` cases. Model it after the existing
  `test_is_none_or_when_null_returns_true_and_some_defers_to_predicate`.
- The existing parametrized `test_is_some_*` / `test_is_some_and_*` tables stay
  as-is and keep covering runtime behavior.
- Verification: `uv run pytest -q` → all pass (216 tests: 215 existing + 1 new),
  and `uv run mypy src tests` → success.

## Done criteria

Machine-checkable. ALL must hold:

- [ ] `uv run mypy src tests` exits 0 with `Success: no issues found in 9 source files`
- [ ] `uv run pytest -q` exits 0; the new test exists and passes
- [ ] `grep -n "def is_some" src/results/option.py` shows **three** matches
      (one abstract on `Option`, one on `Some`, one on `Null`) and likewise for
      `def is_some_and`
- [ ] `uv run ruff check` → `All checks passed!`
- [ ] No files outside the in-scope list are modified (`git status`)
- [ ] `plans/README.md` status row for 001 updated

## STOP conditions

Stop and report back (do not improvise) if:

- The concrete `is_some` / `is_some_and` on `Some` or `Null` are **missing**
  (not just the base) — the "Current state" excerpts don't match; the codebase
  has drifted and this plan's premise is wrong.
- After adding the abstract stubs, `uv run pytest` fails with
  `TypeError: Can't instantiate abstract class Some/Null with abstract methods`
  — that means a subclass is missing an implementation; report which one.
- `uv run mypy src tests` still reports `attr-defined` on `is_some` after Step 1
  — the stub was placed inside a subclass instead of the `Option` base.

## Maintenance notes

- For the reviewer: confirm the new methods sit on the `Option` ABC (not inside
  `Some`/`Null`), use `@abc.abstractmethod`, and that `is_some_and`'s parameter
  is named `op` to match the concrete signatures.
- Future `Option` methods must keep the add-to-base + implement-on-both-variants
  shape; this plan reinforces that invariant rather than changing it.
- Plan 004 (delete `Option.some`/`none`) also edits the `Option` base in a
  different region; if both are in flight, expect a trivial merge in
  `src/results/option.py`.
