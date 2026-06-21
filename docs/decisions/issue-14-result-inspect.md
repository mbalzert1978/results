# Entscheidungs-Log — Issue #14 (Result: add inspect / inspect_err)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default.

Zwei seiteneffektbehaftete Inspektoren — `inspect` / `inspect_err` — für die
`Result`-Familie (`src/results/results.py`). Keine Verhaltensänderung an
bestehenden Methoden, kein Berühren von `option.py` (disjunkter Lane #17).

## E1 — Kein neuer Typparameter in `inspect` / `inspect_err` nötig

- **Offener Punkt:** Sollen die Methoden mit einem eigenen Typparameter `[U]`
  o. ä. parametrisiert werden, wie `map[U]` es tut?
- **Entscheidung:** Keine neuen Typparameter. `inspect(fn: Callable[[T], Any])`
  und `inspect_err(fn: Callable[[E], Any])` verwenden `Any` für den Rückgabetyp
  von `fn` — genau wie Rusts `FnOnce(T)` ohne Rückgabewert; der Rückgabewert
  wird verworfen.
- **Begründung:** (4) ponytail/minimaler Diff: ein Typparameter wäre nur nötig,
  wenn der Rückgabewert von `fn` in den Container einginge. Das tut er nicht —
  `inspect` gibt `self` zurück. PEP 695 `def inspect[U](...)` wäre totes Gewicht.
- **Verworfen:** `def inspect[U](self, fn: Callable[[T], U]) -> Result[T, E]`.

## E2 — Rückgabetyp-Annotation auf der inerten Variante

- **Offener Punkt:** Die inerte Variante (z. B. `Ok.inspect_err`) gibt `self`
  zurück; ihr Rückgabetyp trägt einen „losen" Typparameter (`Result[T, E]` bzw.
  `Result[Any, E]`). Muss das präzisiert werden?
- **Entscheidung:** Die inerten Varianten folgen dem bestehenden Muster analoger
  Methoden: `Ok.inspect_err` deklariert `def inspect_err[E](...) -> Result[T, E]`
  (Typparameter für `E` nötig, weil `Ok[T]` kein `E` kennt), `Err.inspect`
  entsprechend `def inspect[T](...) -> Result[T, E]`. Das ist byte-ident mit der
  Signatur von `Err.map` und `Ok.map_err`.
- **Begründung:** (2) Konventionstreue: bestehende inerte Varianten verwenden
  denselben Trick (freier Typparameter in der Methode, damit die Signatur auf der
  ABC-Basis passt). Ein abweichendes Muster würde ohne Mehrwert Inkonsistenz
  erzeugen.

## E3 — Alphabetische Einordnung (placement)

- **Offener Punkt:** Wo in der Methodenliste werden `inspect` / `inspect_err`
  eingefügt — vor oder nach `is_*`-Methoden?
- **Entscheidung:** Einordnung unmittelbar **nach** `is_ok_and` und **vor**
  `map` — alphabetisch: `inspect` < `is_*` … nein; tatsächlich `i` < `m`, und
  `inspect` < `is_err` alphabetisch nicht. Da `is_err` < `inspect_err` < `map`
  und `inspect` < `is_err`, wird `inspect` / `inspect_err` direkt nach dem
  `is_ok_and`-Block gesetzt, unmittelbar vor `map`. Das entspricht dem
  Positionierungsprinzip der Geschwistermethoden.
- **Begründung:** (2) Konsistenz mit der bestehenden Reihenfolge; ein Bruch der
  Reihenfolge erschwert das Auffinden.

## E4 — No-op auf der inerten Variante: kein `isinstance`, kein Guard

- **Offener Punkt:** Könnte die inerte Variante aus Sicherheitsgründen einen
  `isinstance`-Check einbauen?
- **Entscheidung:** Nein. Die inerte Variante gibt ausschließlich `return self`
  zurück. Kein Check, kein Sentinel-Vergleich.
- **Begründung:** (1) CLAUDE.md/CONTEXT.md-Invariante: Verhalten wird
  ausschließlich durch **Polymorphie** ausgewählt. `inspect` verpackt nichts
  und gibt `self` zurück — der `Some(None)`-Guard (in `Some.__init__`,
  `option.py`) ist nicht involviert. Kein neuer Zustand, keine neue Grenze.
- **Verworfen:** Guard-Check in der inerten Variante.

## E5 — Doku-Synchronisation

- **Offener Punkt:** Welche Doku-Dateien berührt diese Änderung?
- **Entscheidung:** (a) `CONTEXT.md` erhält einen neuen Glossar-Abschnitt
  `### inspect / inspect_err` unmittelbar nach `### map`. (b) Ein
  Entscheidungs-Log wird unter `docs/decisions/issue-14-result-inspect.md`
  abgelegt. (c) `CLAUDE.md` wird **nicht** geändert — es pflegt keine
  Per-Methoden-Liste, und die Verträge der bestehenden Abschnitte ändern sich
  nicht.
- **Begründung:** (1) CLAUDE.md-Anweisung: CONTEXT.md ist das maßgebliche
  Glossar; Code ist die Source of Truth, Glossar folgt. CLAUDE.md beschreibt
  die Architektur, keine Methodenliste.
