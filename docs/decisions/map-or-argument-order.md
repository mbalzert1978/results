# Entscheidungs-Log — `Result.map_or` auf Rust-Reihenfolge `(default, op)`

Datum: 2026-06-21
Auslöser: Code-Quality-Review (Inkonsistenz der Argumentreihenfolge).

## E1 — `Result.map_or(op, default)` → `Result.map_or(default, op)`

- **Offener Punkt:** `Result.map_or` nahm `(op, default)`, während
  - `Option.map_or` `(default, op)` nimmt,
  - `Result.map_or_else` `(default, op)` nimmt,
  - Rust `map_or(self, default, f)` = `(default, op)` ist.

  `Result.map_or` war damit dreifach der Ausreißer — gegen die Schwester-Familie,
  gegen die eigene `*_else`-Variante und gegen das Rust-Vorbild.
- **Entscheidung:** `Result.map_or` auf `(default, op)` umgestellt (Basis-ABC, `Ok`,
  `Err`), inkl. Parameternamen `default`/`op` wie bei `Option`. **Breaking Change** für
  positionale Aufrufer.
- **Begründung:** Stiller Bruch jetzt (laut, mit klarer Migration) ist besser als eine
  dauerhaft verdrehte Signatur zwischen zwei Schwester-Typen, die positional vertauscht
  werden kann, ohne dass ein Fehler auffällt.
- **Migration:** `result.map_or(f, default)` → `result.map_or(default, f)`.
- **Hinweis:** `Option.map_or` war bereits korrekt und bleibt unverändert; ebenso
  `Some.xor`s interner Aufruf `optb.map_or(self, lambda _: Null())` (Option-Seite).
