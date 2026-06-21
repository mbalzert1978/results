# Entscheidungs-Log — Issue #7 (Option als versiegelter Zwei-Zustands-Typ)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
2. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default.

## E1 — `Some`/`Null` als `@final`-Subklassen statt Factory-Funktionen

- **Offener Punkt:** Das Issue lässt offen, ob `Some`/`Null` echte Subklassen werden oder dünne Factories bleiben, die auf Subklassen delegieren.
- **Entscheidung:** Echte `@final`-Subklassen von `Option[T]`: `Some[T]` (trägt `_value` im Slot) und `Null[T]` (slotlos, kein Wert).
- **Begründung:** (1) `CLAUDE.md`-Architektur — Verhalten per Polymorphie, nie per Flag/`isinstance`; exakt das `Result`/`Ok`/`Err`-Muster. (3) Rust modelliert `Some`/`None` als Varianten. Ermöglicht direktes Pattern-Matching `case Some(v)` / `case Null()`.
- **Verworfen:** Modul-Factory-Funktionen, die an Classmethods delegieren (das Alt-Muster) — hielten einen Konstruktionspfad für den Leerzustand offen und verkomplizieren `__match_args__`.

## E2 — `Option.some()` / `Option.none()` Classmethods behalten

- **Offener Punkt:** Entfernen oder behalten?
- **Entscheidung:** Als dünne Delegatoren an `Some`/`Null` behalten.
- **Begründung:** (2) Bestehende öffentliche API; ponytail: minimaler Eingriff, kein zusätzlicher Bruch über den Issue-Scope hinaus.
- **Verworfen:** Entfernen (unnötiger zweiter Breaking Change).

## E3 — Direkte Konstruktion des Leerzustands verhindern

- **Offener Punkt:** Wie „make illegal states unrepresentable" technisch umsetzen?
- **Entscheidung:** Basis `Option` = `abc.ABC` mit abstrakten Methoden → `Option()` wirft `TypeError`; kein öffentlicher `__init__`, der `None` als Leer-Sentinel speichert.
- **Begründung:** Issue-Kern + `CONTEXT.md`-Invariante „`Result` selbst wird nie instanziiert". Abwesenheit ist nun strukturell (eigener Typ), nicht der Wert `None`.
- **Verworfen:** Sentinel-basierte Einzelklasse (`_MISSING`-Objekt) — inspiziert weiterhin einen gespeicherten Wert, macht Abwesenheit nicht strukturell und widerspricht der vom Issue geforderten polymorphen Dispatch-Logik.

## E4 — `__match_args__`-Form

- **Offener Punkt:** Pattern-Matching-Form unter dem neuen Design.
- **Entscheidung:** `Some.__match_args__ = ("_value",)`, `Null.__match_args__ = ()`.
- **Begründung:** `case Some(v)` bindet den Wert, `case Null()` matcht den Leerzustand ohne Bindung — Spiegel von Rusts `Some(v)` / `None`. Ersetzt das alte `case Option(content)` der Einzelklassen-Ära.
- **Verworfen:** Weiter auf `_content` matchen.

## E5 — `transpose`-Semantik unter den neuen Semantiken

- **Offener Punkt:** `Null()` ist nun von `Some(None)` verschieden — ändert das `Option.transpose`?
- **Entscheidung:** Semantik unverändert: `Null() → Ok(Null())`, `Some(Ok(v)) → Ok(Some(v))`, `Some(Err(e)) → Err(e)`, sonst `Ok(Some(_))`. Umsetzung jetzt polymorph statt per `_content`-Match.
- **Begründung:** (3) entspricht Rust-`transpose`; (1) `CONTEXT.md` `transpose`-Eintrag (dessen Text #5/Bestand bleibt). Kein Sonderfall für `Some(None)` nötig — der Leerzustand ist ohnehin ein eigener Typ.
- **Verworfen:** Einen Sonderzweig für `Some(None)` einführen.

## E6 — Doku-Grenze zu #5

- **Offener Punkt:** Sowohl #5 als auch #7 fassen `CONTEXT.md`/`CLAUDE.md` an.
- **Entscheidung:** #7 ändert nur die Einträge `Option`/`Some`/`Null`/`unwrap_or`/`Cross-Conversion` + Beispieldialoge 1 & 2 bzw. die `Option`-Architektur- und Pattern-Matching-Absätze. `OptionError`/`TransposeError`/`transpose`-Einträge und der „Failure mode"-Satz bleiben #5.
- **Begründung:** Disjunkte Zeilenbereiche → unabhängig mergebare PRs (Koordinations-Konvention).

## E7 — Breaking Change kennzeichnen
>
> **Nachtrag:** Die Festlegung `Some(None) != Null()` wurde später umgekehrt —
> siehe [forbid-some-none.md](forbid-some-none.md). `Some(None)` ist nun verboten
> und wirft `ValueError`.

- **Offener Punkt:** Umfang der Verhaltensänderung.
- **Entscheidung:** Major-Bump; im PR-Body als Breaking Change vermerkt: `Some(None) != Null()`, falsy-`Some(...)` nicht mehr als „abwesend" behandelt, `Option(...)` nicht mehr direkt konstruierbar.
- **Begründung:** Konvention: sichtbare API-/Semantik-Brüche werden für Konsumenten dokumentiert.
