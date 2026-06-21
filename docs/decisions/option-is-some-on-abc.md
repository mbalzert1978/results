# Entscheidungs-Log — Plan 001 (Option: `is_some` / `is_some_and` auf der ABC)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Option`-Semantik (std) · 4. ponytail-Default.

Scope: ausschließlich `src/results/option.py`, `tests/results/test_option.py`,
`CONTEXT.md` (Anker `### is_none_or / inspect`) und dieser Log. Kein
`results.py`-Diff, keine Änderung an den konkreten `Some`/`Null`-Implementierungen.

## E1 — Diagnose: Asymmetrie-Bug, keine Verhaltensänderung

- **Offener Punkt:** Was genau ist defekt?
- **Entscheidung:** `is_some` / `is_some_and` existieren konkret auf `Some` und
  `Null`, sind aber **nicht** als `@abc.abstractmethod` auf `Option` deklariert.
  Über eine `Option[T]`-Referenz (der Normalfall — Rückgabetyp von `map`,
  `filter`, `and_then`, `from_fn`, …) meldet mypy `attr-defined`. Die Schwester
  `Result` deklariert `is_ok` / `is_ok_and` auf ihrer Basis; `Option` zog nicht
  nach.
- **Begründung:** (1)/(2) Die Invariante „jede `Option`-Methode ist abstrakt auf
  der Basis plus je eine Implementierung auf `Some` und `Null`" war für dieses
  Paar verletzt. Der Fix ist rein additiv — Laufzeitverhalten bleibt identisch.

## E2 — Nur zwei abstrakte Stubs hinzufügen (ponytail)

- **Offener Punkt:** Wie minimal lässt sich der Bug beheben?
- **Entscheidung:** Genau zwei `@abc.abstractmethod`-Stubs auf `Option`. Die
  konkreten Implementierungen auf `Some`/`Null` sind bereits korrekt und werden
  **nicht** angefasst.
- **Begründung:** (4) ponytail — kürzester Diff, der den Typfehler schließt.
  Mehr Code wäre Scope-Creep.
- **Verworfen:** `is_some` über `not self.is_none()` auf der Basis
  default-implementieren. Das bräche das Polymorphie-Muster (Verhalten käme aus
  einer Default-Methode statt aus den Varianten) und widerspräche `CLAUDE.md`.

## E3 — Parametername `op`, nicht `fn`

- **Offener Punkt:** Welcher Parametername für den abstrakten `is_some_and`-Stub?
- **Entscheidung:** `op` — exakt wie die bestehenden konkreten Signaturen auf
  `Some`/`Null`. (`is_none_or` nutzt `fn`; das Prädikat-Argument von `is_some_and`
  heißt im Bestand `op`.)
- **Begründung:** (2) Signatur-Parität zwischen Basis und Implementierungen;
  divergierende Namen brächen die LSP-Übereinstimmung optisch und sind irritierend.
- **Verworfen:** `fn` (würde von den konkreten Implementierungen abweichen).

## E4 — Rückgabetyp `bool` auf der Basis

- **Offener Punkt:** `bool` oder `Literal[...]` auf den abstrakten Stubs?
- **Entscheidung:** `bool`. Die varianten-spezifischen `Literal[True]` /
  `Literal[False]` bleiben auf `Some`/`Null`; die Basis nennt den gemeinsamen
  Obertyp.
- **Begründung:** (2) Spiegelt `is_none` / `is_none_or` auf der Basis (beide
  `-> bool`), während die Literals auf der konkreten Ebene erhalten bleiben.

## E5 — Methoden-Platzierung: `is_none` → `is_none_or` → `is_some` → `is_some_and`

- **Offener Punkt:** Wo auf der Basis einfügen?
- **Entscheidung:** Direkt nach `is_none_or`, vor `map` — entsprechend der in
  `docs/decisions/issue-17-option-is-none-or-inspect.md:16-17` dokumentierten
  Reihenfolge.
- **Begründung:** (1)/(2) Bestehende, dokumentierte Ordnungs-Konvention.

## E6 — TDD: roter Typ-Check vor der Implementierung

- **Vorgehen:** `test_is_some_and_is_some_and_callable_through_option_base` ruft
  beide Methoden über eine `Option[int]`-Referenz auf. Zuerst hinzugefügt: vier
  rote `attr-defined`-Fehler in mypy bestätigt (der eigentliche Gate), dann die
  Stubs ergänzt — mypy grün, Suite grün. Die bestehenden parametrisierten
  `is_some_*`-Tabellen decken das Laufzeitverhalten unverändert ab.

## E7 — CONTEXT.md: neuer Abschnitt `### is_some / is_some_and`

- **Offener Punkt:** Wo in CONTEXT.md einfügen?
- **Entscheidung:** Unmittelbar nach `### is_none_or / inspect`, vor
  `### and_ / xor`. Kein anderer Abschnitt berührt.
- **Begründung:** (1) `CLAUDE.md` verlangt CONTEXT.md-Pflege bei Vertrags-
  änderungen an öffentlichen Methoden; der Abschnitt steht thematisch neben
  seinem Komplement `is_none_or`.
