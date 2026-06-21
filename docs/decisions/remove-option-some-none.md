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
