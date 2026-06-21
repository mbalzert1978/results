# Entscheidungs-Log — Issue #16 (Result: add transpose (Result[Option] -> Option[Result]))

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default.

`Result.transpose` als Gegenstück zu `Option.transpose` in `src/results/results.py`.
Keine Änderung an `option.py`, `__init__.py` oder `test_option.py` (disjunkte Lanes).

## E1 — Semantik: Rust-Abbildung plus toleranter Fallback

- **Offener Punkt:** Welche Fälle deckt `Result.transpose` ab? Rust kennt nur
  `Ok(Some(v))`, `Ok(None)` und `Err(e)` — was passiert bei `Ok(nicht-Option-Wert)`?
- **Entscheidung:** Die drei Rust-Fälle werden 1:1 übernommen; ein nicht-`Option`-
  Inhalt in `Ok` löst den toleranten Fallback `Some(self)` aus — identisch mit dem
  Fallback in `Option.transpose` (`case _: return Ok(self)`).
- **Begründung:** (2) Konsistenz: `Option.transpose` hat denselben Fallback;
  das Spiegeln des Verhaltens macht das Paar symmetrisch und vermeidet eine
  `TypeError`-Ausnahme, die den Aufrufer unerwartet trifft.
- **Verworfen:** `raise TypeError` bei unbekanntem Inhalt.

## E2 — Implementierungsform: polymorphe Dispatch, kein isinstance

- **Offener Punkt:** Kann die Fallunterscheidung in der Basisklasse per
  `isinstance`-Check erfolgen?
- **Entscheidung:** Nein. Das Architektur-Prinzip verbietet `isinstance`-Checks auf
  der eigenen Variante. `Ok.transpose` verwendet `match self._inner_value` (Payload-
  Matching ist erlaubt); `Err.transpose` gibt schlicht `Some(self)` zurück.
- **Begründung:** (1) CLAUDE.md: „Behavior is selected by POLYMORPHISM only —
  NEVER isinstance/flag/is None/truthiness checks on self's variant."

## E3 — Typparameter: method-level `[U]` / `[T, U]`

- **Offener Punkt:** Welche Typparameter brauchen die Signaturen?
- **Entscheidung:**
  - Basis-ABC: `def transpose[U](self) -> Option[Result[U, E]]`
  - `Ok.transpose`: `def transpose[U, E](self) -> Option[Result[U, E]]` — `E` als
    freier Parameter, da `Ok[T]` deklariert ist als `Result[T, Any]`.
  - `Err.transpose`: `def transpose[T, U](self) -> Option[Result[U, E]]` — `T` und
    `U` als freie Parameter, da `Err[E]` deklariert ist als `Result[Any, E]`.
- **Begründung:** (2) Konventionstreue: dasselbe Muster nutzen `Ok.map_err` und
  `Err.map` — freie Typparameter auf der inerten Variante, damit die Signatur mit
  der ABC-Basis übereinstimmt.

## E4 — cast für den Fallback-Zweig in `Ok.transpose`

- **Offener Punkt:** `Some(self)` im `case _`-Zweig: mypy meldet
  `Argument 1 to "Some" has incompatible type "Ok[T]"; expected "Result[U, E]"`.
- **Entscheidung:** `Some(cast(Result[U, E], self))` — ein `cast` macht mypy klar,
  dass `Ok[T]` hier als `Result[U, E]` behandelt wird.
- **Begründung:** (2) Konsistenz: `Ok.map_err` nutzt ebenfalls `cast(U, …)` für
  den analogen Typ-Mismatch. `cast` ist reines Typ-Annotation-Werkzeug ohne
  Laufzeit-Kosten.
- **Verworfen:** `# type: ignore` (zu grob), Umstrukturierung der Rückgabe (unnötig).

## E5 — Placement: nach `or_else`, vor `unwrap`

- **Offener Punkt:** Wo in der Methodenliste wird `transpose` eingefügt?
- **Entscheidung:** Unmittelbar nach `or_else` (alphabetisch: `t` > `o`), vor
  `unwrap` — gilt für ABC, `Ok` und `Err` gleichermaßen.
- **Begründung:** (2) Konsistenz mit dem bestehenden Ordnungsprinzip.

## E6 — Invariante: kein None-Check nötig

- **Offener Punkt:** Muss `transpose` selbst prüfen, ob der extrahierte Wert `None`
  ist?
- **Entscheidung:** Nein. `transpose` gibt immer einen `Result` oder `Null()` zurück,
  nie einen rohen Wert in `Some`. `Some.__init__` fängt `None` bereits ab, falls es
  unerwartet auftritt.
- **Begründung:** (1) Invariante: „The invariant is enforced EXACTLY ONCE at the
  construction boundary." Eigene None-Checks wären defensive Duplikation.

## E7 — Doku-Synchronisation

- **Offener Punkt:** Welche Doku-Dateien berührt diese Änderung?
- **Entscheidung:** (a) Der bestehende `### transpose`-Abschnitt in `CONTEXT.md`
  (Zeile ~287) wird erweitert, um **beide** Richtungen zu dokumentieren.
  (b) Dieses Entscheidungs-Log unter `docs/decisions/issue-16-result-transpose.md`.
  (c) `CLAUDE.md` wird **nicht** geändert.
- **Begründung:** (1) CLAUDE.md-Anweisung: CONTEXT.md ist das maßgebliche Glossar;
  der bestehende Abschnitt beschreibt bereits `Option.transpose` — er wird erweitert,
  nicht dupliziert.
