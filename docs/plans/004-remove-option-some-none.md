# Plan 004: Remove `Option.some` / `Option.none` pass-through classmethods (breaking)

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat 7e4f2e7..HEAD -- src/results/option.py tests/results/test_option.py`
> If either file changed since this plan was written, compare the "Current
> state" excerpts against the live code before proceeding; on a mismatch, treat
> it as a STOP condition.

## Status

- **Priority**: P2
- **Effort**: S
- **Risk**: MED (public API removal — breaking, but pre-1.0)
- **Depends on**: none (interacts with 001 — both edit the `Option` base)
- **Category**: tech-debt
- **Planned at**: commit `7e4f2e7`, 2026-06-21

## Why this matters

`Option.some(v)` is `return Some(v)` and `Option.none()` is `return Null()` —
two thin pass-throughs that duplicate the canonical constructors `Some(...)` and
`Null()`. They give one construction concept a second vocabulary, they are
undocumented in `CONTEXT.md`, and the sibling `Result` family has no equivalent
classmethod constructors (you just write `Ok(...)`/`Err(...)`). Removing them
shrinks the public surface to one name per concept and makes the two families
read as exact mirrors.

**This reverses a recorded decision — handle it correctly.**
`docs/decisions/issue-7-seal-option-two-state.md` §E2 explicitly decided to
*keep* `some`/`none` and rejected removal. Crucially, the stated reason was
narrow: avoiding "a second breaking change beyond issue #7's scope" — a
timing/scope objection, not a semantic one. The package is pre-1.0 (`0.1.0`), so
a deliberate, standalone `refactor!` removal now is exactly the intentional break
E2 deferred. Per `CLAUDE.md` / repo convention, **a superseding ADR must be
written** so the reversal is on record (this plan creates it).

## Current state

- `src/results/option.py:66-84` — the two classmethods to remove:

  ```python
  @classmethod
  def some(cls, content: T) -> Option[T]:
      """
      Creates an `Option` instance that contains `Some` value.

      Examples:
      >>> assert Option.some(10) == Some(10)
      """
      return Some(content)

  @classmethod
  def none(cls) -> Option[T]:
      """
      Creates an `Option` instance that contains a `Null` value.

      Examples:
      >>> assert Option.none() == Null()
      """
      return Null()
  ```

  They sit on the `Option` ABC, directly after the `as_option` staticmethod
  (line 44-64) and before the first `@abc.abstractmethod` (`and_`, line 86).

- The only non-doc reference is in a test. `tests/results/test_option.py:417-427`
  (`test_some_none_is_forbidden`):

  ```python
  def test_some_none_is_forbidden() -> None:
      # None is absence, not a value: Some(None) raises, as do paths that would
      # wrap None (map -> None, transpose). Use Null() / and_then instead.
      with pytest.raises(ValueError, match="Some.None. is forbidden"):
          Some(None)
      with pytest.raises(ValueError, match="Some.None. is forbidden"):
          Option.some(None)
      with pytest.raises(ValueError, match="Some.None. is forbidden"):
          Some(5).map(lambda _: None)
      with pytest.raises(ValueError, match="Some.None. is forbidden"):
          Some(Ok(None)).transpose()
  ```

  The second `with`-block (`Option.some(None)`) must be removed — it tests a
  method that will no longer exist. The other three blocks stay (they test the
  `Some.__init__` guard via other paths).

- Confirmed scope (run to reproduce):
  `grep -rn "\.some(\|\.none(\|Option.some\|Option.none\|def some\|def none" src tests`
  shows matches only in `src/results/option.py` (the defs + docstring examples)
  and `tests/results/test_option.py:423`. References in `docs/decisions/*.md` and
  `docs/prompts/*.md` are historical records — **out of scope, do not edit**.
- `CONTEXT.md` does not mention `some`/`none` at all — nothing to remove there.
- `README.md` does not mention them — nothing to change there.

## Commands you will need

| Purpose         | Command                                                                               | Expected on success            |
|-----------------|---------------------------------------------------------------------------------------|--------------------------------|
| Install         | `uv sync`                                                                             | exit 0                         |
| Tests (Option)  | `uv run pytest tests/results/test_option.py -q`                                       | all pass                       |
| Tests (all)     | `uv run pytest -q`                                                                    | all pass                       |
| Typecheck       | `uv run mypy src tests`                                                               | `Success: no issues found ...` |
| Lint            | `uv run ruff check`                                                                   | `All checks passed!`           |
| Format          | `uv run ruff format src/results/option.py tests/results/test_option.py`               | normalizes only your edits     |
| Confirm removal | `grep -rn "def some\|def none\|Option.some\|Option.none\|\.some(\|\.none(" src tests` | **no matches**                 |

## Scope

**In scope** (the only files you should modify/create):

- `src/results/option.py` — delete the two classmethods.
- `tests/results/test_option.py` — delete the `Option.some(None)` assertion.
- `docs/decisions/remove-option-some-none.md` — create the superseding ADR.

**Out of scope** (do NOT touch):

- `Option.some` / `Option.none` callers elsewhere — there are none (verified).
- The other three assertions in `test_some_none_is_forbidden` — keep them.
- `Some` / `Null` constructors and the `Some.__init__` `None` guard — unchanged.
- `docs/decisions/issue-7-seal-option-two-state.md` — it is a historical record;
  do NOT edit it. The new ADR supersedes it by reference.
- Do NOT add `Result.some`/`Result.none` "for symmetry" — `Result.ok()`/`err()`
  already exist as conversions to `Option`; constructor classmethods would
  collide and add surface, defeating the point of this plan.

## Git workflow

- Branch: `advisor/004-remove-option-some-none`.
- Commit message style: conventional commits with the breaking-change marker,
  matching `git log` (e.g. `refactor(option)!: remove Option.some/none pass-through constructors`).
  The recent history uses this exact `refactor!:` form (commit `7e4f2e7`).
- Do NOT push or open a PR unless the operator instructed it.

## Steps

### Step 1: Write the superseding ADR

Create `docs/decisions/remove-option-some-none.md` with this content (German, to
match the existing decision logs):

```markdown
# Entscheidungs-Log — `Option.some()` / `Option.none()` entfernen

Kehrt die Festlegung aus
[issue-7-seal-option-two-state.md](issue-7-seal-option-two-state.md) §E2
(„`Option.some()` / `Option.none()` Classmethods behalten") um. Offene Punkte
autonom gemäß Entscheidungsreihenfolge gelöst: 1. Projekt-Domäne
(`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen · 3. Rust-`Option`-Semantik ·
4. ponytail-Default.

## E1 — `some`/`none` ersatzlos entfernen

- **Offener Punkt:** Die beiden Classmethods sind dünne Delegatoren
  (`some(v) -> Some(v)`, `none() -> Null()`). Behalten (issue-7 §E2) oder
  entfernen?
- **Entscheidung:** Entfernen. Die kanonischen Konstruktoren sind `Some(...)`
  und `Null()`. Ein Konzept, ein Name.
- **Begründung:** (4) ponytail/Deletionstest: löscht man beide, taucht die
  Komplexität nicht wieder auf — Aufrufer schreiben `Some(v)`/`Null()`, die sie
  ohnehin importieren. (2) Symmetrie: die `Result`-Familie hat keine analogen
  Konstruktor-Classmethods; `Result.ok()`/`err()` sind Konversionen nach
  `Option`, keine Konstruktoren. (1) `CONTEXT.md` führt `some`/`none` nirgends.
- **Verworfen:** Behalten + dokumentieren (hält die zweite Vokabel am Leben);
  `Result.some`/`none` ergänzen (kollidiert mit `Result.ok()`/`err()`, mehr
  Oberfläche statt weniger).

## E2 — Warum issue-7 §E2 jetzt umgekehrt wird

- **Offener Punkt:** §E2 verwarf das Entfernen ausdrücklich.
- **Entscheidung:** Die §E2-Begründung war eng auf den Issue-#7-Scope bezogen
  („unnötiger zweiter Breaking Change" *innerhalb von #7*), kein dauerhafter
  semantischer Einwand. Als eigenständiger, gewollter `refactor!` ist das genau
  der aufgeschobene Bruch — vor 1.0 (`0.1.0`) ist er günstig.
- **Begründung:** Konvention: API-/Semantik-Brüche werden dokumentiert; diese
  ADR ist der Datensatz.

## E3 — Breaking Change kennzeichnen & Test anpassen

- **Entscheidung:** Im PR-Body als Breaking Change vermerken. Der einzige
  Verweis im Testcode (`Option.some(None)` in `test_some_none_is_forbidden`)
  entfällt; die übrigen `Some(None)`-Pfade (direkt, via `map`, via `transpose`)
  bleiben und decken den `Some.__init__`-Guard weiterhin ab.
- **Begründung:** Tests decken den Konstruktor-Guard, nicht eine entfernte
  Methode.
```

**Verify**: file exists; `uv run pytest -q` still green (no test reads it yet).

### Step 2: Delete the two classmethods

In `src/results/option.py`, delete the entire `some` and `none` classmethod
blocks shown in "Current state" (lines 66-84, from `@classmethod` above
`def some` through the `return Null()` of `none`, inclusive). Leave the
`as_option` staticmethod above and the first `@abc.abstractmethod def and_`
below intact, with one blank line between them.

**Verify**:

- `grep -n "def some\|def none" src/results/option.py` → no matches.
- `uv run pytest tests/results/test_option.py -q` → fails **only** in
  `test_some_none_is_forbidden` with `AttributeError: type object 'Option' has
  no attribute 'some'` (expected — fixed in Step 3). If anything *else* fails,
  STOP.

### Step 3: Remove the now-dead test assertion

In `tests/results/test_option.py`, inside `test_some_none_is_forbidden`, delete
exactly this block (and only this block):

```python
    with pytest.raises(ValueError, match="Some.None. is forbidden"):
        Option.some(None)
```

Keep the three other `with pytest.raises(...)` blocks (`Some(None)`,
`Some(5).map(lambda _: None)`, `Some(Ok(None)).transpose()`).

**Verify**: `uv run pytest tests/results/test_option.py -q` → all pass.

### Step 4: Format, type-check, full suite

```text
uv run ruff format src/results/option.py tests/results/test_option.py
uv run ruff check
uv run mypy src tests
uv run pytest -q
```

**Verify**: ruff clean, mypy `Success: no issues found in 9 source files`, all
tests pass (one fewer assertion than before, same test count).

## Test plan

- No new tests. One assertion is removed (`Option.some(None)`); the
  `Some.__init__` `None` guard remains covered by the three surviving paths in
  `test_some_none_is_forbidden` plus `test_ok_when_ok_none_is_forbidden` in
  `tests/results/test_result.py`.
- Verification: `uv run pytest -q` → all pass; `grep` confirms the methods and
  their last caller are gone.

## Done criteria

Machine-checkable. ALL must hold:

- [ ] `grep -rn "def some\|def none\|Option.some\|Option.none\|\.some(\|\.none(" src tests` → no matches
- [ ] `docs/decisions/remove-option-some-none.md` exists
- [ ] `uv run pytest -q` passes
- [ ] `uv run mypy src tests` → `Success: no issues found in 9 source files`
- [ ] `uv run ruff check` → `All checks passed!`
- [ ] Only `src/results/option.py`, `tests/results/test_option.py`,
      `docs/decisions/remove-option-some-none.md` (and `plans/README.md`) changed
- [ ] `plans/README.md` status row for 004 updated

## STOP conditions

Stop and report back (do not improvise) if:

- `grep` finds a caller of `Option.some` / `Option.none` anywhere in `src/` or
  `tests/` beyond the single known one in `test_some_none_is_forbidden` — the
  blast radius is larger than assumed; report the call sites before deleting.
- After Step 2, a test **other than** `test_some_none_is_forbidden` fails — that
  means something depended on these methods that this plan didn't account for.
- The "Current state" excerpt at `option.py:66-84` doesn't match the live code
  (e.g. the methods grew real logic beyond the pass-through) — the deletion
  premise is wrong.

## Maintenance notes

- For the reviewer: confirm the PR is labeled/messaged as a breaking change
  (`refactor(option)!:`), that the new ADR references and supersedes issue-7 §E2,
  and that `Some`/`Null` and the `None` guard are untouched.
- Interaction with plan 001: both edit the `Option` base. 001 adds abstract
  methods near `is_none_or`; 004 deletes classmethods near the top of the class.
  Different regions — expect at most a trivial merge.
- After this lands, `Option.some`/`Option.none` are gone for good; the
  superseding ADR is the durable record of why.
