# Plan 005: Add `Result.flatten` to mirror `Option.flatten`

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat 7e4f2e7..HEAD -- src/results/results.py tests/results/test_result.py CONTEXT.md`
> If any in-scope file changed since this plan was written, compare the "Current
> state" excerpts against the live code before proceeding. **Most likely drift:**
> plan 003 renamed `_inner_value` → `_value` in `results.py`. If so, use `_value`
> in Step 3's `Ok.flatten` body instead of `_inner_value` — that is expected, not
> a STOP. Any other mismatch is a STOP condition.

## Status

- **Priority**: P3
- **Effort**: S
- **Risk**: LOW
- **Depends on**: none (soft interaction with 003 — see drift note above)
- **Category**: direction
- **Planned at**: commit `7e4f2e7`, 2026-06-21

## Why this matters

`Option` has `flatten` — it collapses `Option[Option[T]]` into `Option[T]`
(`src/results/option.py:148-167`). `Result` has no counterpart, even though the
nesting `Result[Result[T, E], E]` arises naturally (e.g. `and_then` over a
function that itself returns a `Result`-of-`Result`). Rust provides
`Result::flatten`. This is a surface asymmetry between two families whose value
is being mirror images, and the repo is clearly pursuing incremental Rust-parity
one method per numbered decision log (see `docs/decisions/issue-14..issue-22`).
`Result.flatten` is the smallest next parity step and follows an exact existing
template (`Option.flatten`, decided in `docs/decisions/issue-20-option-flatten.md`).

Note the scope boundary in `CONTEXT.md` ("kein vollständiger Port der Rust-API")
— this is curated parity, a deliberate addition, not a bug fix. It is included
here because you selected it; it follows the established per-method pattern.

## Current state

- `src/results/results.py` — `Result` ABC plus `Ok`/`Err`. No `flatten` exists.
  The relevant region of the base (lines 93-101):

  ```python
  @abc.abstractmethod
  def expect_err(self, msg: str) -> E:
      """Returns the contained [`Err`] value, consuming the `self` value.
      Raises an `UnwrapFailedError` with the provided message if the value is an [`Ok`].
      """

  @abc.abstractmethod
  def is_err(self) -> bool:
      """Returns `True` if the result is an [`Err`] value."""
  ```

  `Ok` carries the contained value in `self._inner_value` (lines 200-302); `Err`
  returns `self` from no-op transforms like `map` (`src/results/results.py:361-362`):

  ```python
  def map[T, U](self, fn: Callable[[T], U]) -> Result[U, E]:
      return self
  ```

- The template to mirror — `Option.flatten` (`src/results/option.py`):
  - ABC (148-167): `def flatten[U](self: Option[Option[U]]) -> Option[U]` with a
    docstring listing the three mappings and the identity note.
  - `Some` (459-462):

    ```python
    def flatten[U](self: Some[Option[U]]) -> Option[U]:
        # ponytail: self._value is already an Option[U] — return it directly.
        # No re-wrap, no None risk, O(1). Identity: Some(inner).flatten() is inner.
        return self._value
    ```

  - `Null` (581-582):

    ```python
    def flatten[U](self: Null[Option[U]]) -> Option[U]:
        return Null()
    ```

- Conventions (from `docs/decisions/issue-20-option-flatten.md`, the `Option`
  flatten decision log — read it; it is the authority for this style):
  - §E1: the present variant returns its inner container **directly** (identity,
    no re-wrap). For `Result`, `Ok.flatten` returns the inner `Result` unchanged;
    `Err.flatten` returns `self` (propagate, like `Err.map`).
  - §E2/§E3: no `None` handling, no raise-on-`None` test (N/A to `Result`).
  - §E4: self-type signatures via PEP 695 method-level generics — no `isinstance`
    or runtime type check. `flatten` is statically gated to the nested type.
  - §E6: TDD — add the failing tests first, watch them go red, then implement.
  - §E7: document in `CONTEXT.md` in the `### flatten` section (which already
    exists for `Option`), keeping `flatten` near `and_then`.

- Existing `Result` test style: parametrized tables with human-readable `ids=`,
  importing from `results`. The closest structural exemplar is
  `tests/results/test_result.py:573-594` (`test_transpose` +
  `test_transpose_round_trip`).

## Commands you will need

| Purpose         | Command                                                                  | Expected on success            |
|-----------------|------------------------------------------------------------------------- |--------------------------------|
| Install         | `uv sync`                                                                | exit 0                         |
| Tests (Result)  | `uv run pytest tests/results/test_result.py -q`                          | all pass                       |
| Tests (all)     | `uv run pytest -q`                                                       | all pass                       |
| Typecheck       | `uv run mypy src tests`                                                  | `Success: no issues found ...` |
| Lint            | `uv run ruff check`                                                      | `All checks passed!`           |
| Format          | `uv run ruff format src/results/results.py tests/results/test_result.py` | normalizes only your edits     |

## Scope

**In scope** (the only files you should modify/create):

- `src/results/results.py` — add `flatten` (1 abstract + `Ok` + `Err`).
- `tests/results/test_result.py` — add the flatten tests.
- `CONTEXT.md` — extend the `### flatten` section with the `Result` side.
- `docs/decisions/result-flatten.md` — create the decision log.

**Out of scope** (do NOT touch):

- `src/results/option.py` — `Option.flatten` is the template, not a target.
- `README.md` — optional, deliberately skipped (it lists Result methods only
  loosely); leave it.
- Any other `Result` method.
- Do NOT add a runtime `isinstance` / `None` check to `flatten` (issue-20 §E2/E4).

## Git workflow

- Branch: `advisor/005-result-flatten`.
- Commit message style: conventional commits matching `git log` (e.g.
  `feat(result): add flatten — collapse one level of Result nesting`).
- Do NOT push or open a PR unless the operator instructed it.

## Steps

### Step 1: Write the decision log

Create `docs/decisions/result-flatten.md` (German, mirroring issue-20):

```markdown
# Entscheidungs-Log — `Result`: `flatten`

Spiegelt [issue-20-option-flatten.md](issue-20-option-flatten.md) auf die
`Result`-Seite. Offene Punkte autonom gemäß Entscheidungsreihenfolge gelöst:
1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`-Semantik (std) · 4. ponytail-Default.

## E1 — `Ok.flatten` gibt das innere `Result` direkt zurück (Identität)

- **Entscheidung:** `return self._inner_value` — kein neues `Ok`/`Err`.
  `self._inner_value` ist bereits ein `Result[U, E]`, also das korrekte
  Ergebnis für `Ok(Ok(v))` (→ `Ok(v)`) und `Ok(Err(e))` (→ `Err(e)`).
- **Begründung:** (3) Rust: `Result::flatten` ≙ `and_then(|x| x)`. (4) ponytail:
  O(1), kein neues Objekt; Identität `Ok(inner).flatten() is inner`.

## E2 — `Err.flatten` reicht sich selbst durch

- **Entscheidung:** `return self` — wie `Err.map`/`Err.and_then`: der Fehler
  propagiert unverändert (`Err(e)` → `Err(e)`).

## E3 — Self-Typ-Signatur mit PEP 695, kein Laufzeit-Check

- **Entscheidung:**
  - ABC: `def flatten[U](self: Result[Result[U, E], E]) -> Result[U, E]`
  - `Ok`: `def flatten[U, E](self: Ok[Result[U, E]]) -> Result[U, E]`
  - `Err`: `def flatten[U](self) -> Result[U, E]`
- **Begründung:** (2) konsistent mit `Option.flatten`/`transpose`/`unzip`. Der
  Self-Typ macht `flatten` statisch nur auf verschachtelten `Result`s aufrufbar —
  kein `isinstance`, kein `TransposeError`-artiger Laufzeit-Check nötig (anders
  als `transpose`, dessen Vertragsbruch nicht über den Self-Typ ausdrückbar ist).

## E4 — TDD & Doku

- **Vorgehen:** Tests zuerst (rot: `AttributeError: ... has no attribute
  'flatten'`), dann Implementierung (grün). `CONTEXT.md`-Abschnitt `### flatten`
  um die `Result`-Seite ergänzt.
```

**Verify**: file exists; `uv run pytest -q` still green.

### Step 2: Add the failing tests (TDD red)

In `tests/results/test_result.py`, add near the existing `test_transpose`:

```python
@pytest.mark.parametrize(
    "result, expected",
    [
        (Ok(Ok(5)), Ok(5)),
        (Ok(Err("e")), Err("e")),
        (Err("e"), Err("e")),
    ],
    ids=[
        "flatten Ok(Ok(v)) -> Ok(v)",
        "flatten Ok(Err(e)) -> Err(e)",
        "flatten Err(e) -> Err(e)",
    ],
)
def test_flatten(result, expected):
    assert result.flatten() == expected


def test_flatten_ok_returns_inner_result_identity() -> None:
    # Ok.flatten must return the inner Result unchanged — not a re-wrapped copy.
    inner_ok: Result[int, str] = Ok(5)
    assert Ok(inner_ok).flatten() is inner_ok

    inner_err: Result[int, str] = Err("e")
    assert Ok(inner_err).flatten() is inner_err
```

**Verify**: `uv run pytest tests/results/test_result.py -k flatten -q` → fails
with `AttributeError: 'Ok'/'Err' object has no attribute 'flatten'` (this is the
expected red state).

### Step 3: Implement `flatten` (TDD green)

In `src/results/results.py`:

**(a)** Add the abstract method to the `Result` base, between `expect_err`
(ends ~line 97) and `is_err` (line 99):

```python
    @abc.abstractmethod
    def flatten[U](self: Result[Result[U, E], E]) -> Result[U, E]:
        """Collapses one level of `Result` nesting.

        Mappings:

        - `Ok(Ok(v))`  → `Ok(v)`
        - `Ok(Err(e))` → `Err(e)`
        - `Err(e)`     → `Err(e)`

        This is the named form of `and_then(lambda x: x)` (identity flatmap) and
        the `Result` mirror of [`Option.flatten`]. `Ok.flatten` returns the
        stored inner `Result` unchanged — an identity operation
        (`Ok(inner).flatten() is inner`), never re-wraps.

        # Examples:

        >>> assert Ok(Ok(5)).flatten() == Ok(5)
        >>> assert Ok(Err("e")).flatten() == Err("e")
        >>> assert Err("e").flatten() == Err("e")
        """
```

**(b)** Add to `Ok`, between `Ok.expect_err` (line 234-235) and `Ok.is_err`
(line 237). Use `self._inner_value` — **unless plan 003 already renamed it, then
use `self._value`** (see drift note at top):

```python
    def flatten[U, E](self: Ok[Result[U, E]]) -> Result[U, E]:
        # ponytail: self._inner_value is already a Result[U, E] — return it
        # directly. No re-wrap, O(1). Identity: Ok(inner).flatten() is inner.
        return self._inner_value
```

**(c)** Add to `Err`, between `Err.expect_err` (line 339-340) and `Err.is_err`
(line 342):

```python
    def flatten[U](self) -> Result[U, E]:
        # ponytail: Err propagates unchanged — same shape as Err.map.
        return self
```

**Verify**:

- `uv run pytest tests/results/test_result.py -k flatten -q` → all flatten tests pass.
- `uv run mypy src tests` → `Success: no issues found in 9 source files`.

### Step 4: Document in `CONTEXT.md`

The `### flatten` section already exists (currently Option-only). Append a
`Result`-side paragraph to it, just before its closing `*Avoid:*` line:

```markdown
**`Result.flatten`** spiegelt das auf die `Result`-Seite — kollabiert
`Result[Result[T, E], E]` zu `Result[T, E]`:

- `Ok(Ok(v))`  → `Ok(v)`
- `Ok(Err(e))` → `Err(e)`
- `Err(e)`     → `Err(e)`

`Ok.flatten` gibt das innere `Result` direkt zurück (Identität:
`Ok(inner).flatten() is inner`); `Err.flatten` reicht sich selbst durch (`return
self`), wie `Err.map`. Keine `None`-Behandlung — `Result` erlaubt `None` als
Wert; das `Some(None)`-Risiko der `Option`-Seite existiert hier nicht.
```

**Verify**: `uv run pytest -q` → all pass.

### Step 5: Format + full gate

```text
uv run ruff format src/results/results.py tests/results/test_result.py
uv run ruff check
uv run mypy src tests
uv run pytest -q
```

**Verify**: ruff clean, mypy success, all tests pass (existing + 4 new flatten
cases).

## Test plan

- New tests in `tests/results/test_result.py`:
  - `test_flatten` — parametrized: `Ok(Ok(v))→Ok(v)`, `Ok(Err(e))→Err(e)`,
    `Err(e)→Err(e)` (the three mappings).
  - `test_flatten_ok_returns_inner_result_identity` — pins the `is`-identity for
    both an inner `Ok` and an inner `Err`.
  - Model: the existing `test_transpose` / `test_transpose_round_trip` and the
    `Option` flatten tests (`test_flatten_collapses_one_level_of_nesting`,
    `test_flatten_some_returns_inner_option_identity`).
- No raise-on-`None` test (issue-20 §E3 rationale; N/A to `Result`).
- Verification: `uv run pytest -q` → all pass; `uv run mypy src tests` → success.

## Done criteria

Machine-checkable. ALL must hold:

- [ ] `grep -n "def flatten" src/results/results.py` shows **three** matches
      (abstract on `Result`, one on `Ok`, one on `Err`)
- [ ] `uv run pytest -q` passes; the 4 new flatten test cases exist and pass
- [ ] `uv run mypy src tests` → `Success: no issues found in 9 source files`
- [ ] `uv run ruff check` → `All checks passed!`
- [ ] `docs/decisions/result-flatten.md` exists; `CONTEXT.md` `### flatten`
      section mentions `Result.flatten`
- [ ] Only the four in-scope files (and `plans/README.md`) changed (`git status`)
- [ ] `plans/README.md` status row for 005 updated

## STOP conditions

Stop and report back (do not improvise) if:

- `Option.flatten` no longer matches the "Current state" template excerpt — the
  pattern this plan mirrors has changed; re-derive before copying it.
- mypy rejects the self-type signatures (e.g. "Self argument ... incompatible")
  after two reasonable attempts — report the exact error; the PEP-695 form may
  need adjusting for the installed mypy version.
- The identity test fails (`Ok(inner).flatten() is inner` is False) — that means
  `Ok.flatten` re-wrapped instead of returning the inner value directly.

## Maintenance notes

- For the reviewer: confirm `flatten` is statically gated (self-type), has **no**
  runtime `isinstance`/`None` check (unlike `transpose`, which legitimately
  raises `TransposeError`), and that `Ok.flatten` returns the inner `Result` by
  identity while `Err.flatten` returns `self`.
- If `_inner_value` was renamed to `_value` by plan 003, the `Ok.flatten` body
  must use `_value`; the drift check at the top covers this.
- Follow-up deliberately deferred: `README.md` is not updated (its Result method
  list is illustrative, not exhaustive). Add `flatten` there only if the
  maintainer wants the README to enumerate the full surface.
