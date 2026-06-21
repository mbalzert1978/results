# Prompt: `Result` und `Option` zu echten versiegelten Summentypen machen

> Konsolidierter Arbeits-Prompt (Sealing der Basis + `Some(None)`-Verbot).
> Quelle: iterative Prompt-Verbesserung; Stand vor `/compact`.

## Ziel

Make illegal states unrepresentable: Die einzigen bewohnbaren Varianten von
`Result` sind `Ok` und `Err`, von `Option` sind es `Some` und `Null` — exakt zwei
je Typ. Eine dritte Variante darf weder zur Laufzeit noch laut Typechecker
existieren. Zusätzlich gilt: `Some` umschließt immer einen echten Wert `T`,
niemals `None`.

## Problem heute (`src/results/results.py`)

- `Result`/`Option` sind offene `abc.ABC`. `Ok/Err/Some/Null` sind zwar `@final`,
  aber die Basis selbst ist nicht versiegelt: externer Code kann `class X(Result)`
  mit eigener Implementierung definieren und so eine dritte, ungültige Variante
  erzeugen → illegaler Zustand ist repräsentierbar.
- `Some(None)` ist konstruierbar; `Some.__init__` stellt den Wert ungeprüft ab.
- Der Klassen-Docstring von `Option` (Zeilen ~311–319) behauptet sogar fälschlich,
  `Some(None)` sei „a legal, present state distinct from `Null()`". Das ist falsch
  und kodifiziert den Bug als Feature.

## Kernanforderung 1: die Basis versiegeln (Laufzeit + Typecheck)

- `@final` auf der abstrakten Basis ist KEIN Weg: `typing.final` ist nur
  Typechecker-Advisory UND würde die internen Varianten `Ok/Err` selbst verbieten
  (genau der Widerspruch „abstrakt + final").
- Versiegele zur Laufzeit über `__init_subclass__` auf `Result` bzw. `Option`:
  jede Subklasse, die nicht in diesem Modul definiert ist, wirft `TypeError`. Das
  deckt auch indirektes Erben (`class X(Ok)`) ab, da der Guard für den ganzen
  Teilbaum feuert.
- `Ok/Err/Some/Null` bleiben öffentlich — Pattern-Matching (`case Ok(v)`),
  `isinstance` und Importe hängen daran.

## Kernanforderung 2: `Some(None)` verbieten

`Some` umschließt immer einen echten Wert `T`; `None` ist ausschließlich das
Absenz-Sentinel und wird allein durch `Null` repräsentiert. `Some(None)` ist damit
verboten und darf nicht konstruierbar sein — genau dafür existiert `Option`.

- FALSCH und zu korrigieren: der `Option`-Docstring (Zeilen ~311–319). Aussage
  entfernen und umkehren.
- Durchsetzen an der Konstruktionsgrenze (`Some.__init__` bzw. `Option.some()`):
  `None` wird abgewiesen.
- `from_fn`/`as_option` sind bereits konform (sie mappen `None` → `Null`, bauen also
  nie `Some(None)`); diese Pfade bleiben unverändert.

## Offene Designentscheidungen (autonom fällen, im Decision-Log festhalten)

### A. Versiegelungs-Mechanik

- **A) `__init_subclass__`-Versiegelung, Varianten bleiben öffentlich** — laziest,
  ein Guard pro Basis. **[Empfehlung]**
- B) private genestete Varianten + Smart-Constructor-Factories — nur, wenn es über
  A hinaus echten Mehrwert gibt; Pattern-Matching/Importe müssen weiter über
  öffentliche Namen laufen.

### B. Verhalten an der Some-Grenze bei `None`

- **A) hart abweisen: `Some(None)` wirft.** **[Empfehlung — entspricht „verboten"]**
- B) normalisieren: `None` kollabiert überall zu `Null()` (konsistent mit
  from_fn/as_option).
- Eine Regel wählen und überall gleich anwenden.

### C. Folge für `Some.map`/`transpose`

`Some(5).map(lambda _: None)` und `Some(Ok(None)).transpose()` laufen über die
Some-Grenze. Bei A werfen sie, bei B werden sie zu `Null` — bewusst festlegen,
nicht dem Zufall überlassen.

### D. Fehlertyp bei „werfen"

`ValueError` (laziest) oder ein dedizierter `OptionError` (passend zum
`ResultError`-Muster). Hinweis: `OptionError`/`TransposeError` werden in CLAUDE.md
erwähnt, existieren im Code aber NICHT — also neu anlegen oder die stale Doku
mitkorrigieren.

## Falls Factories (nur bei Mechanik B)

`Result.ok()`/`err()` sind bereits Instanzmethoden (→ `Option`). Ein Factory
`Result.ok(value)` kollidiert damit. Nutze die Modul-Klassen `Ok`/`Err` als
Konstruktoren oder einen anderen Factory-Namen. `Option.some()/none()` existieren
schon.

## Grenzen

- Typecheck-Grenze: „T ist nicht None" lässt sich mit PEP-695-Generics nicht sauber
  ausdrücken — Durchsetzung ist Laufzeit-only (Decke per `ponytail:`-Kommentar
  benennen).

## Verifikation & Abschluss

- Negativtest in `tests/results/`: eine Subklasse von `Result`/`Option` außerhalb
  des Moduls muss `TypeError` werfen (parametrisiert, mit `ids=`).
- Negativtest: `Some(None)` / `Option.some(None)` muss je nach Entscheidung werfen
  (A) bzw. `Null()` ergeben (B); als parametrisierter Fall mit `ids=`.
- Den falschen `Some(None)`-Doctest/Docstring in `Option` korrigieren.
- Stale Doctests, die `Result.Ok(...)` referenzieren, an die reale API angleichen.
- `uv run pytest`, `uv run mypy src tests`, `uv run ruff check` grün; Working Tree
  clean.
- CONTEXT.md (Begriff „versiegelter Summentyp"/„Variante") und die
  Architecture-Notiz in CLAUDE.md aktualisieren; Entscheidung im Decision-Log.

## Verifizierte Code-Fakten (Stand dieser Session)

- `Option` ist bereits ABC mit `@final` `Some`/`Null` — CLAUDE.md beschreibt noch
  die alte Single-Class-`_content`-Variante (stale).
- `OptionError`/`TransposeError` existieren im Code nicht (nur in CLAUDE.md).
- `Result`-Basis ist nicht versiegelt; externes Erben möglich.
- `ok()`/`err()` sind Instanzmethoden (→ `Option`) — Namenskollision mit Factories.
- `Some(None)` ist heute konstruierbar; der `Option`-Docstring behauptet das sei
  legal.
