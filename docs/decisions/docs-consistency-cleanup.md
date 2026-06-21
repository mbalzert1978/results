# Doku-Konsistenz-Pass — Prosa-Doku gegen den realen Code abgleichen

Kein Code-Refactor, sondern ein Konsistenz-Pass: abgeleitete und Prosa-Artefakte
mit dem Code (Source of Truth) in Einklang bringen. Ein sequenzieller Slice, ein
PR — die wenigen Doc-Dateien überschneiden sich, Parallelisierung erzeugte nur
Konflikte.

## E1 — Stale Prämissen verifiziert, nicht „repariert"

- **Offener Punkt:** Der Auftrag nannte als Startpunkte (a) uneinheitlichen
  Decision-Log-Ort (CLAUDE.md → `docs/decisions/`, real angeblich top-level
  `decisions/`) und (b) untrackte `prompts/`- und Decision-Dateien.
- **Befund:** Beides bereits erledigt (Commits `256e8b2`, `f87f878`). Working
  Tree clean; alle Logs liegen getrackt unter `docs/decisions/`, das Scratch-
  Prompt unter `docs/prompts/`. CLAUDE.md-Verweis auf
  `docs/decisions/issue-13-split-option-module.md` ist korrekt.
- **Entscheidung:** Keine Aktion. Prämisse war stale; verifiziert statt blind
  „korrigiert".

## E2 — `Result.Ok` / `Result.Err` / `Option.null` existieren nicht (README)

- **Offener Punkt:** README-„Classes and Methods"-Beispiele referenzierten
  `Result.Ok(...)`, `Result.Err(...)`, `Option.null(...)`.
- **Befund (empirisch geprüft):** `Result` hat keine `Ok`/`Err`-Attribute,
  `Option` kein `null`. Kanonische Konstruktoren sind `Ok`/`Err`/`Some`/`Null`
  (top-level, in `__all__`). `Result.as_result`/`from_fn` und `Option.some`
  existieren.
- **Entscheidung:** README-Beispiele auf die reale API angeglichen und
  selbst-lauffähig gemacht (`Ok`/`Err` direkt, Inline-Lambda statt undefiniertem
  `sq_then_to_string`, `>>> @decorator` + `... def`). Alle Snippets laufen grün
  (manuell verifiziert).

## E3 — `Null("Error")` / `Null(10)`: toter Verweis statt Code-Bug

- **Offener Punkt:** CONTEXT.md (Z. 118–120) meldete fehlerhafte Docstrings mit
  `Null("Error")` / `Null(10)`; Auftrag: im Code fixen (`Null` nimmt keine
  Argumente).
- **Befund:** In `src/` existiert kein `Null(<arg>)` (alle Aufrufe arg-los) —
  die Docstrings wurden bereits in #7/forbid-some-none gefixt. Das einzige
  `Null("Error")` lebte in README Z. 65 (siehe E2). `Null(10)` nirgends.
- **Entscheidung:** Kein Code-Fix nötig. README-Beispiel ersetzt (E2). Die
  CONTEXT.md-Meta-Notiz „in einigen Docstrings … fehlerhaft" verweist damit ins
  Leere → entfernt. Die Kernaussage „`Null()` nimmt keine Argumente" bleibt
  (CONTEXT.md Z. 110).

## E4 — `unwrap_or_default`: bewusst nicht vorhanden

- **Offener Punkt:** CONTEXT.md-Scope (Z. 31–34, „bewusst kleine
  Methodenauswahl", „kein `unwrap_or_default`") in Spannung zur gewachsenen
  Fläche (`and_`/`or_`/`xor`/`zip`/`unzip`/`flatten`/`inspect`/…).
- **Befund (grep):** `unwrap_or_default` existiert nirgends im Code — die
  Negativ-Aussage stimmt. Die Fläche ist gewachsen, aber weiter ein kuratierter
  Rust-Subset.
- **Entscheidung:** `unwrap_or_default` bleibt absichtlich draußen — Python hat
  keinen universellen Default-Wert je Typ (kein `Default`-Trait); ein Standard
  drückt sich mit `unwrap_or(default)` aus. Scope-Formulierung von „bewusst
  kleine Methodenauswahl" auf „kuratierte Methodenauswahl, nicht die vollständige
  Rust-Oberfläche" justiert + Begründung inline ergänzt.

## E5 — Historische Artefakte nicht umschreiben

- **Entscheidung:** `docs/decisions/*` und `docs/prompts/seal-result-option.md`
  dokumentieren bewusst Entferntes (`OptionError`/`TransposeError`, alte
  `_content`-Variante, stale `Result.Ok`-Doctests). Das ist Historie, kein toter
  Verweis im Live-Code → unangetastet. Ebenso die *negativen* Invarianten in
  CONTEXT.md/CLAUDE.md („nie per `_content is None`") — die beschreiben korrekt,
  was der Code **nicht** tut.

## Abschluss

- Berührt: `README.md`, `CONTEXT.md`, dieser Log. Kein `.py` angefasst →
  Verhalten unverändert; `CLAUDE.md` nicht angefasst.
- Verifikation: korrigierte README-Snippets laufen real; Dead-Ref-Sweep über
  Prosa-Doku (Klassen/Methoden/Pfade/Log-Links) sauber; `graphify update .` als
  letzter Schritt.
