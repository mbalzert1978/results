# Entscheidungs-Log — Issue #17 (Option: `is_none_or` / `inspect`)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Option`-Semantik (std) · 4. ponytail-Default.

Lane O: ausschließlich `src/results/option.py`, zugehöriger Testmodul und CONTEXT.md
(Anker `### Null`). Kein `results.py`-Diff.

## E1 — Methoden-Platzierung: alphabetisch innerhalb beider Klassen

- **Offener Punkt:** Wo genau landen `inspect` und `is_none_or` in der
  Methodenreihenfolge von `Some` und `Null`?
- **Entscheidung:** Alphabetisch nach den unmittelbaren Geschwistern:
  `inspect` nach `filter` (f < i); `is_none_or` nach `is_none`, vor `is_some`
  (lexikographisch `is_none_or` < `is_some`). Dasselbe Muster in `Some` und `Null`.
- **Begründung:** (2) Bestehende Konvention — alle Methoden innerhalb der Klassen
  sind alphabetisch geordnet.
- **Verworfen:** Neue Methoden ans Ende hängen (würde die Ordnung brechen).

## E2 — Signatur `inspect`: `Callable[[T], object]` statt `Callable[[T], Any]`

- **Offener Punkt:** `Any` (wie Rust's `FnOnce(T)`) oder `object`?
- **Entscheidung:** `Callable[[T], object]` — der Rückgabewert wird nie genutzt;
  `object` drückt das mit der breitestmöglichen statischen Typ-Einschränkung aus
  (jede callable ist hier gültig).
- **Begründung:** (4) ponytail: `object` ist restriktiver als `Any` und
  signalisiert „Rückgabewert egal, nicht genutzt".
- **Verworfen:** `Callable[[T], Any]` (weniger präzise für die Intention).

## E3 — `is_none_or` auf `Null`: `Literal[True]` Rückgabetyp

- **Offener Punkt:** `bool` oder `Literal[True]`?
- **Entscheidung:** `Literal[True]` — spiegelt `is_none()` und `is_some_and()` auf
  `Null`, die ebenfalls Literal-Typen zurückgeben (`Literal[True]` bzw.
  `Literal[False]`).
- **Begründung:** (2) Konsistenz mit den Geschwistern `is_none`, `is_some`,
  `is_some_and` auf denselben konkreten Klassen.
- **Verworfen:** `bool` (weniger präzise, inkonsistent mit Geschwistern).

## E4 — `inspect` gibt `self` zurück (kein neues Objekt)

- **Offener Punkt:** Darf `inspect` ein neues `Some`/`Null` bauen?
- **Entscheidung:** Nein. Beide Implementierungen geben `self` zurück; der Test
  `assert o.inspect(fn) is o` erzwingt Objektidentität.
- **Begründung:** (3) Rust-Semantik: `Option::inspect` gibt `self` zurück. (1)
  Invariante: kein öffentlicher Pfad darf einen ungültigen Zustand erzeugen; da
  `self` unveränderlich ist, ist Identität die sicherste Rückgabe. `Some(None)`
  kann dadurch nicht entstehen.
- **Verworfen:** `Some(self._value)` oder `Null()` als neue Instanzen (unnötig,
  würde Identitätstest brechen).

## E5 — Keine `None`-Prüfung in den Implementierungskörpern

- **Offener Punkt:** Soll `inspect` sicherstellen, dass `fn` kein `None`
  zurückgibt?
- **Entscheidung:** Nein. `inspect` verwirft den Rückgabewert; es entsteht kein
  Wrapper. Kein `if result is None: raise ValueError(...)`.
- **Begründung:** (1) Aufgabenstellung: „Add NO None checks." `Some(None)` kann
  nicht entstehen, weil `inspect` den Rückgabewert von `fn` schlicht ignoriert.

## E6 — TDD: Failing Tests vor der Implementierung

- **Vorgehen:** Alle neuen Testfälle wurden in `tests/results/test_option.py` als
  zusätzliche parametrized-Einträge und zwei eigenständige Testfunktionen
  (Identitäts-Pin, Side-Effect-Recorder) eingefügt, **bevor** die Implementierung
  in `option.py` erfolgte. Sechs rote Fehler bestätigt, dann alle 174 grün.

## E7 — CONTEXT.md: ein neuer Abschnitt, lokalisiert am `### Null`-Anker

- **Offener Punkt:** Wo in CONTEXT.md einfügen?
- **Entscheidung:** Unmittelbar nach `### Null`, vor `### unwrap`. Kein anderer
  CONTEXT.md-Abschnitt berührt.
- **Begründung:** (1) Aufgabenstellung: Anker `### Null`. (2) Disjunktheit: Lane
  #14 editiert den Bereich nach `### map` — kein Konflikt.
