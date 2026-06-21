# Entscheidungs-Log — Issue #15 (Result: add eager and_ / or_ combinators)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default.

Zwei eager Kombinatoren — `and_` / `or_` — für die `Result`-Familie
(`src/results/results.py`). Keine Verhaltensänderung an bestehenden Methoden,
kein Berühren von `option.py` (disjunkter Lane #17).

## E1 — Benennung: Trailing Underscore statt Alias

- **Offener Punkt:** `and`/`or` sind Python-Schlüsselwörter; wie heißen die Methoden?
- **Entscheidung:** `and_` und `or_` (trailing underscore) — identisch mit Rusts
  `Result::and` / `Result::or`, nur um den Namenskonflikt umgangen.
- **Begründung:** (3) Rust-Semantik: dies ist die kanonische Rust-Konvention für
  Methoden, deren Name ein reserviertes Wort wäre. Keine Alias-Lösung nötig.
- **Verworfen:** `result_and`, `combine`, `chain`.

## E2 — Keine neuen Typparameter auf der inerten Variante nötig

- **Offener Punkt:** Welche Typparameter brauchen `Ok.or_` und `Err.and_`, die
  `self` zurückgeben?
- **Entscheidung:** Die inerten Varianten folgen dem bestehenden Muster analoger
  Methoden. `Ok.or_` deklariert `def or_[E, F](self, res: Result[T, F]) ->
  Result[T, F]` (freie Typparameter `E`, `F`); `Err.and_` entsprechend
  `def and_[T, U](self, res: Result[U, E]) -> Result[U, E]`.
- **Begründung:** (2) Konventionstreue: dasselbe Muster nutzen `Ok.inspect_err`
  und `Err.inspect` — freier Typparameter in der Methode, damit die Signatur auf
  der ABC-Basis passt.

## E3 — Rückgabe des bestehenden Objekts (keine Rekonstruktion)

- **Offener Punkt:** Sollen `Ok.or_` und `Err.and_` `self` oder ein neu
  konstruiertes Objekt zurückgeben?
- **Entscheidung:** `return self` — das bestehende Objekt wird unverändert
  zurückgegeben, kein `Ok(self._inner_value)` o. ä.
- **Begründung:** (4) ponytail/minimaler Diff: eine Rekonstruktion wäre
  überflüssige Arbeit, die die Identitäts-Invariante (`is`-Test) brechen würde.
  Die Methode nimmt auch nichts Neues ein — sie gibt `self` direkt durch.
- **Verworfen:** `return Ok(self._inner_value)` in `Ok.or_`.

## E4 — Alphabetische Einordnung (placement)

- **Offener Punkt:** Wo in der Methodenliste werden `and_` / `or_` eingefügt?
- **Entscheidung:** `and_` unmittelbar **vor** `and_then` (alphabetisch: `and_`
  < `and_then`); `or_` unmittelbar **vor** `or_else`. Gilt für ABC, `Ok` und
  `Err` gleichermaßen.
- **Begründung:** (2) Konsistenz mit dem bestehenden Ordnungsprinzip; eager/lazy-
  Paare liegen direkt nebeneinander, was die Dokumentations-Signalwirkung stärkt.

## E5 — Doku-Synchronisation

- **Offener Punkt:** Welche Doku-Dateien berührt diese Änderung?
- **Entscheidung:** (a) `CONTEXT.md` erhält einen neuen Glossar-Abschnitt
  `### \`and_\` / \`or_\`` unmittelbar nach `### inspect / inspect_err` und vor
  `### and_then`. (b) Ein Entscheidungs-Log wird unter
  `docs/decisions/issue-15-result-and-or.md` abgelegt. (c) `CLAUDE.md` wird
  **nicht** geändert — es pflegt keine Per-Methoden-Liste.
- **Begründung:** (1) CLAUDE.md-Anweisung: CONTEXT.md ist das maßgebliche
  Glossar; Code ist die Source of Truth, Glossar folgt. CLAUDE.md beschreibt
  die Architektur, keine Methodenliste.
