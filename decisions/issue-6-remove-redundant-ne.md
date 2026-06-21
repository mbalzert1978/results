# Entscheidungs-Log — Issue #6 (Redundante `__ne__`-Overrides entfernen)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:
1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default.

## E1 — Scope: nur `Ok` und `Err`
- **Offener Punkt:** Issue #6 nennt drei `__ne__` (`Ok`, `Err`, `Option`); alle drei in diesem PR?
- **Entscheidung:** Nur `Ok.__ne__` und `Err.__ne__` entfernen. `Option.__ne__` bleibt → wird von #7 mitentfernt.
- **Begründung:** Maintainer-Re-Scoping; #7 fasst die `Option`-Klasse komplett neu. Disjunkte Code-Bereiche → konfliktfreie Parallel-PRs.
- **Verworfen:** Alle drei hier — kollidiert mit #7s Rewrite von `Option`.

## E2 — Beweisbarkeit des „kein Verhaltenswechsel"
- **Offener Punkt:** Ist die Löschung garantiert verhaltenserhaltend?
- **Entscheidung:** Ja — beide `__eq__` liefern immer ein `bool` (nie `NotImplemented`), daher reproduziert Pythons auto-abgeleitetes `!=` exakt das alte `not self.__eq__(other)`.
- **Begründung:** (2)/Python-Datenmodell seit Py3. Ein Tiebreaker über Rust war nicht nötig.

## E3 — Testplatzierung
- **Offener Punkt:** Wo den Regressionstest ablegen und welchen Fall?
- **Entscheidung:** Cross-Type-Fall `(Ok(1), Err(1), True)` in die bestehende `test__ne__`-Tabelle in `tests/results/test_result.py`.
- **Begründung:** Konvention (parametrisierte Tabellen mit `ids=`). `test_option.py` gehört #7 — bewusst nicht angefasst, um Datei-Kollisionen zu vermeiden.
- **Verworfen:** Neue Testfunktion / Eingriff in `test_option.py`.
