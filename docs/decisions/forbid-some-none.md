# Entscheidungs-Log — `Some(None)` verbieten

Zusätzliche Invariante: `Some` umschließt immer einen echten Wert `T`; `None` ist
ausschließlich das Absenz-Sentinel und wird allein durch `Null` repräsentiert.
`Some(None)` darf nicht konstruierbar sein. Offene Punkte autonom gemäß
Entscheidungsreihenfolge gelöst: 1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) ·
2. Code-Konventionen · 3. Rust-`Option`-Semantik · 4. ponytail-Default.

Kehrt die `#7`-Festlegung `Some(None) != Null()` um (siehe
[issue-7-seal-option-two-state.md](issue-7-seal-option-two-state.md) E7).

## E1 — Verhalten an der Some-Grenze: hart werfen (A)

- **Offener Punkt:** `Some(None)` → A) hart abweisen (wirft) oder B) zu `Null()`
  normalisieren.
- **Entscheidung:** **A** — `Some(None)` wirft `ValueError`. Eine Regel, überall
  gleich angewandt: jeder Pfad, der `None` in ein `Some` packen würde, wirft.
- **Begründung:**
  - Semantik der Kombinatoren: `map` ist `T -> U`. Hat man ein *optionales*
    Zwischenergebnis, ist `and_then` (`T -> Option[U]`) das richtige Werkzeug, nicht
    `map`. `Some(None)` — direkt oder über `map`, das `None` liefert — ist damit ein
    **Programmierfehler** und soll laut scheitern, nicht still verschwinden.
  - Gegen B: Normalisieren erzwang `cast("Some[T]", Null())` in `__new__` — das
    verbiegt nur den eingehenden Typ, um den Typechecker ruhigzustellen. Ein
    Cast, der eine `Null` als `Some[T]` ausgibt, ist der Beleg, dass das Design
    nicht stimmt; A braucht keinen.
  - `ValueError` als Fehlertyp (laziest, keine neue Klasse; idiomatisch „ungültiger
    Argumentwert").
- **Verworfen:** B (normalisieren). Versteckt den Fehler und verlangt den Typ-Cast.

## E2 — Durchsetzungsort: Guard in `Some.__init__`

- **Offener Punkt:** Wo den Wurf erzwingen — `Some.__init__`, `Option.some()` oder
  jede `Some(...)`-Aufrufstelle?
- **Entscheidung:** `if value is None: raise ValueError(...)` in `Some.__init__`.
- **Begründung:** ponytail — eine Stelle deckt **alle** Konstruktionspfade ab.
  `Option.some(None)`, `Ok(None).ok()`, `Some.map` → `None`, `Some.transpose` über
  `Some(None)` werfen dadurch automatisch — gewollt (eine Regel überall, kein
  Guard pro Aufrufstelle, kein Doppel-Verhalten).
- **Verworfen:** `__new__` (nötig nur für die verworfene Normalisierung); ein
  None-bewusster Privat-Konstruktor neben einem werfenden öffentlichen (zwei Regeln).

## E3 — Typprüfungs-Grenze

- **Offener Punkt:** „`T` ist nicht `None`" statisch ausdrücken.
- **Entscheidung:** Nicht möglich mit PEP-695-Generics; Durchsetzung ist
  **Laufzeit-only**, im Code per `ponytail:`-Kommentar benannt. Kein Cast nötig —
  `__init__` wirft, es findet kein Typwechsel statt.
- **Begründung:** Aufgaben-Vorgabe; `from_fn`/`as_option` bleiben unverändert konform
  (sie bildeten `None` → `Null` schon ab, bauen also nie `Some(None)`).

## E4 — Doku & Tests synchron

- **Entscheidung:** `Option`-Docstring umgekehrt; `CLAUDE.md`-Bullet und alle
  `CONTEXT.md`-Einträge (`Option`/`Some`/`Null`/`unwrap_or`/Cross-Conversion/
  `transpose`/`UnwrapFailedError` + Beispieldialoge 1 & 2) auf „wirft `ValueError`"
  umgestellt. Tests: alle `Some(None)`-Zeilen aus den Parametrize-Tabellen entfernt
  (sie würden bei der Collection werfen), stattdessen `test_some_none_is_forbidden`
  (direkt, `Option.some`, `map` → `None`, `transpose`) und
  `test_ok_when_ok_none_is_forbidden`.
- **Begründung:** `CLAUDE.md`-Mandat „Code ist Quelle der Wahrheit — Glossar folgt".
