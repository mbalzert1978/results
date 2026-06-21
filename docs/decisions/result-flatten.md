# Entscheidungs-Log — `Result`: `flatten`

Spiegelt [issue-20-option-flatten.md](issue-20-option-flatten.md) auf die
`Result`-Seite. Offene Punkte autonom gemäß Entscheidungsreihenfolge gelöst:
1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`-Semantik (std) · 4. ponytail-Default.

## E1 — `Ok.flatten` gibt das innere `Result` direkt zurück (Identität)

- **Entscheidung:** `return self._value` — kein neues `Ok`/`Err`.
  `self._value` ist bereits ein `Result[U, E]`, also das korrekte
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
