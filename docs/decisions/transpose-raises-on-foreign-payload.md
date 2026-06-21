# Entscheidungs-Log — `transpose` wirft `TransposeError` bei fremdem Inhalt

Datum: 2026-06-21
Auslöser: Code-Quality-Review der `transpose`-Implementierungen.

## E1 — Lenient Fallback → lautes `raise`

- **Offener Punkt:** `Option.transpose`/`Result.transpose` haben einen Inhalt, der
  nicht die erwartete `Result`/`Option`-Hülle ist (z. B. `Some("foo").transpose()`),
  bisher still in `Ok(self)`/`Some(self)` eingepackt (toleranter Fallback).
- **Entscheidung:** Der Fallback wird durch `raise TransposeError(...)` ersetzt. Ein
  fremder Inhalt ist ein **Programmierfehler** und wird laut abgewiesen, nicht still
  als Erfolg eingepackt.
- **Begründung:**
  - Stilles Einpacken versteckt einen Typfehler — genau das „silent-fallback /
    papering over an invariant"-Muster, das der Review markiert hat.
  - Das Argument „weicht von Rust ab" (siehe Verworfenes unten) trägt nicht: Rust
    kennt den Fall gar nicht, weil `transpose` dort auf `Option<Result<…>>` bzw.
    `Result<Option<…>>` typgebunden ist. Der **lenient Fallback wich selbst von Rust
    ab**; er war kein Rust-Verhalten, sondern eine Python-Erfindung.
  - Python kann die Hülle nicht auf Typ-Ebene erzwingen → ein Laufzeit-Guard an der
    Grenze ist die ehrliche Stelle, den Vertrag zu prüfen.
- **Verworfen:** lenient Fallback behalten (Konsistenz beider `transpose`-Methoden) —
  konsistent, aber konsistent **falsch**: beide schluckten den Typfehler.

## E2 — `TransposeError` wieder eingeführt

- **Offener Punkt:** Welche Ausnahme? Eingebautes `TypeError` oder eine
  bibliothekseigene Klasse?
- **Entscheidung:** `TransposeError(ResultError)` in `src/results/results.py`,
  exportiert über `results.__all__`. Reiht sich in die bestehende Fehlerhierarchie
  (`ResultError` → `UnwrapFailedError` | `TransposeError`) ein und ist gezielt
  abfangbar.
- **Hinweis:** Kehrt **issue #5** um, das `TransposeError`/`OptionError` als tote
  Klassen löschte und einen Guard-Test gegen ihren Re-Export hinterließ. `OptionError`
  bleibt gelöscht (weiterhin ungenutzt); nur `TransposeError` kehrt zurück, jetzt mit
  echtem `raise`-Aufrufer. Der Guard-Test wurde entsprechend aufgeteilt.

## E3 — Dispatch über `.map` der Gegenfamilie statt Inner-Variant-Match

- **Offener Punkt:** Beide `transpose` matchten die Variante des **inneren** Summentyps
  (`case Ok / case Err` bzw. `case Some / case Null`) — was CLAUDE.md („Dispatch per
  Polymorphie, nicht per `isinstance`/Variant-Match in einer Methode") widerspricht.
- **Entscheidung:** Die Ok/Err- bzw. Some/Null-Arme kollabieren zu **einem**
  polymorphen Aufruf auf der Gegenfamilie:
  - `Some(result).transpose()` → `result.map(Some)` (`Ok(v).map(Some)` = `Ok(Some(v))`,
    `Err(e).map(Some)` = `Err(e)`).
  - `Ok(option).transpose()` → `option.map(Ok)` (`Some(v).map(Ok)` = `Some(Ok(v))`,
    `Null().map(Ok)` = `Null()`).
- **Folge:** Nur noch **ein** `isinstance(…, Result/Option)`-Guard bleibt — die Frage
  „ist es die Hülle überhaupt?" (für E1). Die `Some(None)`-Sperre gilt unverändert:
  `Some(Ok(None)).transpose()` läuft über `Ok(None).map(Some)` → `Some(None)` →
  `ValueError`. Der entfernte `cast` in `Ok.transpose`/`Ok.map_err` fällt mit weg.

## Mitgeführte Doku

- `CONTEXT.md`: `transpose`-Einträge (Fallback → `raise`), „`transpose` wirft nie"
  relativiert, `UnwrapFailedError` nicht mehr „einzige" Ausnahme, neuer
  `### TransposeError`-Eintrag.
- Tests: Fallback-Fälle von „liefert `Some(self)`" zu „wirft `TransposeError`"
  umgestellt; `transpose_error_is_removed_from_public_api` → `…_is_exported`.
