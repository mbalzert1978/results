# Entscheidungs-Log — Issue #4 (Dedup der Result-Konstruktoren)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
2. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default (laziest funktionierend).

## E1 — Scope: nur die Result-Seite statt aller vier Konstruktoren

- **Offener Punkt:** Issue #4 nennt vier „callable constructors"; soll dieser PR alle vier dedupen?
- **Entscheidung:** Nur `Result.as_result` → delegiert an `Result.from_fn`. `Option.from_fn`/`Option.as_option` bleiben unangetastet.
- **Begründung:** Maintainer-Re-Scoping + Konvention „ein Anliegen pro PR". Die Option-Seite liefert die `Option`-Neufassung in #7. Parallele PRs müssen disjunkt bleiben, sonst Merge-Konflikt im selben Klassenbereich.
- **Verworfen:** Alle vier hier dedupen — würde mit #7s Rewrite von `Option` kollidieren.

## E2 — Testplatzierung der „kein Verhaltenswechsel"-Garantie

- **Offener Punkt:** Wie absichern, dass die Delegation nichts ändert?
- **Entscheidung:** Bestehenden `test_as_result` um eine Metadaten-Assertion (`__name__`/`__doc__`) erweitern.
- **Begründung:** Konvention (`CLAUDE.md`, Abschnitt *Tests*): Fälle zu bestehenden parametrisierten Tabellen hinzufügen statt Einzeltests. `functools.wraps` ist der einzige Bruchpunkt der Delegation, daher genau dort der Anker.
- **Verworfen:** Neue eigenständige Testfunktion.

## E3 — `CONTEXT.md` bleibt unverändert

- **Offener Punkt:** Muss das Glossar angepasst werden?
- **Entscheidung:** Nein.
- **Begründung:** Verhalten ist identisch; der Eintrag `as_result / from_fn` bleibt korrekt. Code ist Source of Truth, die Doku folgt nur bei Vertrags-/Verhaltensänderung (`CLAUDE.md`-Sync-Regel).
- **Verworfen:** Glossar „vorsorglich" anfassen (Scope-Creep, widerspricht ponytail).
