# results — Ubiquitous Language

Dieses Dokument hält die *Ubiquitous Language* des `results`-Repositories fest:
die verbindlichen Fachbegriffe, ihre präzisen Definitionen und bewusste
Abgrenzungen (was ein Begriff **nicht** meint). Maßgeblich ist immer der Code in
[src/results/results.py](src/results/results.py); weicht dieses Dokument vom Code
ab, gilt der Code — und das Dokument ist zu korrigieren.

## Einleitung

`results` ist eine abhängigkeitsfreie, typisierte Python-Bibliothek (Python ≥ 3.13),
die zwei von Rust inspirierte Container-Typen bereitstellt:

- `Result[T, E]` — eine Operation ist **gelungen** (`Ok`) oder **gescheitert** (`Err`).
- `Option[T]` — ein Wert ist **vorhanden** (`Some`) oder **abwesend** (`Null`).

Leitidee: Fehlschläge und Abwesenheit sind **Werte**, keine Kontrollfluss-Ausnahmen.
Der Aufrufer entscheidet an jeder Stelle explizit, ob er einen Fehler weiterreicht,
einen Standardwert einsetzt oder per Pattern-Matching verzweigt.

Bewusst **nicht** Teil dieses Scopes:

- **Keine Validierungs-Bibliothek.** `results` sammelt keine Fehlerlisten und
  kennt keine Regeln/Constraints — es transportiert genau einen Erfolgs- oder
  genau einen Fehlerwert.
- **Kein Ersatz für `try`/`except` als Sprachmittel.** Ausnahmen werden nur an
  den Rändern eingefangen (siehe `as_result`/`from_fn`); innerhalb der Kette wird
  nicht geworfen, sondern ein `Err`/`Null` weitergereicht.
- **Kein vollständiger Port der Rust-API.** Es existiert nur eine bewusst kleine
  Methodenauswahl. Insbesondere gibt es **kein** `unwrap_or_default` und **kein**
  `flatten`/`zip`, und `TransposeError` wird nirgendwo geworfen.
- **Keine Go-artigen `(value, error)`-Tupel.** Ein Ergebnis ist immer ein einzelnes
  Objekt eines der beiden Typ-Familien, nie ein Paar.

## Language

### Result

Abstrakte Basis (`abc.ABC`) für genau zwei `@final` Varianten: `Ok` (Erfolg) und
`Err` (Fehlschlag). `Result[T, E]` parametrisiert den Erfolgstyp `T` und den
Fehlertyp `E`. Jede Methode ist auf der Basis abstrakt und auf beiden Varianten
implementiert; welche Variante vorliegt, entscheidet die **Polymorphie**, nie eine
`isinstance`- oder Flag-Abfrage im Methodenrumpf.

- Invariante: `Result` selbst wird nie instanziiert — eine Instanz ist immer
  **genau eine** der Varianten `Ok` oder `Err`, nie etwas Drittes und nie beides;
  `is_ok()` und `is_err()` spiegeln das komplementär wider.

*Avoid:* „Exception", „try/except-Wrapper", „Status-Code", „(value, error)-Tupel".
Ein `Result` ist ein Wert, kein Kontrollfluss.

### Ok

Die Erfolgs-Variante von `Result`; hält genau einen Erfolgswert vom Typ `T`.
Deklariert als `Result[T, Any]`.

- Invariante: `is_ok()` ist `True`, `is_err()` ist `False`.
- Wertzugriff (`unwrap`, `expect`) liefert den Wert; die fehlerseitigen Zugriffe
  (`unwrap_err`, `expect_err`) scheitern mit `UnwrapFailedError`.

*Avoid:* „True"/„Erfolg als Boolean", „der Wert selbst". `Ok(5)` ist ein Container
um `5`, nicht die Zahl `5`.

### Err

Die Fehler-Variante von `Result`; hält genau einen Fehlerwert vom Typ `E` (oft,
aber nicht zwingend, eine `Exception`). Deklariert als `Result[Any, E]`.

- Invariante: `is_err()` ist `True`, `is_ok()` ist `False`.
- `unwrap()` scheitert mit `UnwrapFailedError`; ist der Fehlerwert eine
  `BaseException`, wird sie über `raise ... from` als Ursache verkettet.

*Avoid:* „die geworfene Exception", „False". `Err(e)` **enthält** `e` und wird
herumgereicht, ohne selbst zu werfen — bis jemand `unwrap` aufruft.

### Option

Container für einen optionalen Wert. Anders als `Result` ist `Option` **eine
einzige konkrete Klasse** (keine Variantenpaare). Sie speichert `_content: T | None`
und benutzt `None` als „leeres" Sentinel.

- **None-Kollaps-Regel** (hier kanonisch definiert; andere Einträge verweisen
  darauf, statt sie zu wiederholen): Der leere Zustand ist ausschließlich
  `_content is None` — es gibt keinen separaten Leer-Typ. Folge: `Some(None)` ist
  von `Null()` **nicht** unterscheidbar (`Some(None) == Null()`).

*Avoid:* „`typing.Optional`", „nullable Referenz". `Option` ist ein eigenes
Wrapper-Objekt; `Optional[T]` ist bloß `T | None` ohne Methoden.

### Some

Modul-Funktion `Some(value)`, die ein `Option` mit vorhandenem Inhalt erzeugt
(delegiert an `Option.some`).

- Invariante: `Some(v).is_some()` ist `True` — **außer** für `v is None` (dann
  greift die None-Kollaps-Regel von `Option`).

*Avoid:* „Just" (Haskell), „present()". `Some` ist **keine** Garantie für
Anwesenheit (siehe None-Kollaps-Regel).

### Null

Modul-Funktion `Null()`, die ein leeres `Option` erzeugt (delegiert an
`Option.none`, setzt `_content = None`).

- Invariante: `Null().is_none()` ist `True`; nimmt **keine** Argumente (Gegenstück
  zu `Some` unter der None-Kollaps-Regel von `Option`).

*Avoid:* „Pythons `None`", „Nil", „Nothing". `Null()` ist ein `Option`-Objekt, das
ein `None` umhüllt — nicht das `None` selbst. Die in einigen Docstrings gezeigten
Aufrufe mit Argument (`Null("Error")`, `Null(10)`) sind fehlerhaft: `Null` nimmt
keine Parameter und würde mit `TypeError` scheitern.

### unwrap

Oberbegriff für den **wert-entpackenden Zugriff** auf der „guten" Seite:
`Result.unwrap`/`expect` (liefert den `Ok`-Wert) und `Option.unwrap`/`expect`
(liefert den `Some`-Wert). Auf der falschen Seite scheitert der Aufruf mit
`UnwrapFailedError`.

- Invariante: `unwrap` ist **partiell** — es wirft, wenn die Variante nicht passt.
- `expect(msg)` ist `unwrap` mit eigener Fehlermeldung.
- Zum Entpacken der Fehlerseite eines `Result` dienen `unwrap_err`/`expect_err`.

*Avoid:* „Getter", „sichere Lese-Funktion". `unwrap` darf scheitern; für sicheren
Zugriff dienen `unwrap_or`, `unwrap_or_else` oder Pattern-Matching.

### unwrap_or / unwrap_or_else

Entpacken mit Rückfallwert: `unwrap_or(default)` bzw. `unwrap_or_else(fn)` liefern
den enthaltenen Wert oder einen Ersatz, ohne je zu werfen.

- Invariante (`Result`): Der Rückfall greift genau bei `Err`.
- Invariante (`Option`): Hier wird per **Wahrheitswert** entschieden
  (`self._content or default`). Folge: Falsy-Inhalte wie `0`, `""`, `[]` liefern
  den Rückfallwert, obwohl sie eigentlich „vorhanden" sind. Dieselbe
  Truthiness-Logik gilt für die Iteration über ein `Option`.

*Avoid:* anzunehmen, `Option.unwrap_or` prüfe auf Anwesenheit (`is None`) — es prüft
Truthiness. Auf der `Result`-Seite gibt es diese Falle nicht.

### map

Transformiert den **enthaltenen Wert** und gibt einen Container desselben Typs
zurück, ohne die fehler-/leerseitige Variante anzufassen: `Result.map` wirkt auf
`Ok` (und `map_err` auf `Err`), `Option.map` wirkt auf `Some`.

- Invariante: Die übergebene Funktion liefert einen **rohen** Wert; `map` verpackt
  ihn wieder. `Err`/`Null` bleiben unverändert.

*Avoid:* `map` mit `and_then` verwechseln. Gibt deine Funktion bereits ein
`Result`/`Option` zurück, erzeugt `map` eine **doppelte** Verschachtelung.

### and_then

Verkettet eine Folgeoperation, die selbst wieder ein `Result`/`Option` liefert
(in anderen Sprachen *flatmap*): bei `Ok`/`Some` wird die Funktion aufgerufen, bei
`Err`/`Null` wird der vorhandene Container unverändert durchgereicht.

- Invariante: Die übergebene Funktion gibt einen **bereits verpackten** Wert
  zurück; es entsteht **keine** zusätzliche Schachtelung.
- Spiegelbild auf der anderen Seite: `or_else` (reagiert auf `Err`/`Null`).

*Avoid:* `and_then` als „map" beschreiben. Der Unterschied ist genau die
Verpackungs-Ebene des Rückgabewerts.

### Cross-Conversion

Brücken zwischen den beiden Familien, die einen Typ in den anderen überführen:

- `Result.ok()` → `Option[T]` (`Ok(v)` → `Some(v)`, `Err(_)` → `Null()`).
- `Result.err()` → `Option[E]` (`Err(e)` → `Some(e)`, `Ok(_)` → `Null()`).
- `Option.ok_or(err)` / `Option.ok_or_else(fn)` → `Result[T, E]` (`Some(v)` → `Ok(v)`,
  `Null()` → `Err(err)` bzw. `Err(fn())`).

- Invariante: `ok_or`/`ok_or_else` entscheiden per `is None` (nicht per Truthiness),
  daher bleibt `Some(0)` ein `Ok(0)`.
- Folge der `None`-Kollaps-Regel: `Ok(None).ok()` ergibt `Some(None)`, also `Null()`.

*Avoid:* „Cast"/„isinstance-Umwandlung". Es entsteht jeweils ein **neues** Objekt der
Zielfamilie; das Original wird nicht verändert.

### transpose

`Option.transpose()` vertauscht die Schachtelung eines `Option` **eines** `Result`
in ein `Result` **eines** `Option`:

- `Null()` → `Ok(Null())`
- `Some(Ok(v))` → `Ok(Some(v))`
- `Some(Err(e))` → `Err(e)`
- nicht-`Result`-Inhalt → `Ok(self)` (unverändert eingepackt)

*Avoid:* an eine Matrix-Transposition oder an `TransposeError` denken — `transpose`
wirft nie und meint ausschließlich das Tauschen der beiden Schachtelungs-Ebenen.

### as_result / from_fn

Die beiden **Result-Konstruktoren aus aufrufbaren Objekten**: `Result.as_result` ist
ein Dekorator, `Result.from_fn(fn, *args)` ein direkter Aufruf. Beide führen die
Funktion aus und fangen jede `Exception` als `Err(exc)`; ein normaler Rückgabewert
wird zu `Ok(value)`.

- Invariante: Gefangen wird `Exception` (nicht `BaseException`) — `KeyboardInterrupt`
  o. ä. propagiert weiter.

*Avoid:* das mit der Option-Seite verwechseln: hier ist das Auslöse-Kriterium eine
**geworfene Ausnahme**, nicht ein `None`-Rückgabewert.

### as_option / from_fn

Die beiden **Option-Konstruktoren aus aufrufbaren Objekten**: `Option.as_option`
(Dekorator) und `Option.from_fn(fn, *args)`. Beide rufen die Funktion auf und
bilden `None` → `Null()`, jeden anderen Rückgabewert → `Some(value)`.

- Invariante: Es wird **nicht** abgefangen. Der Aufrufer ist dafür verantwortlich,
  dass die Funktion keine Ausnahme wirft; Auslöse-Kriterium ist allein der
  `None`-Rückgabewert.

*Avoid:* annehmen, `as_option` fange Ausnahmen wie `as_result`. Tut es nicht.

### ResultError

Wurzel der Result-seitigen Fehlerhierarchie (`Exception`-Subklasse). Wird nie direkt
geworfen; dient als gemeinsamer Aufhänger zum Abfangen.

*Avoid:* `ResultError` mit `Err` gleichsetzen. `Err` ist eine **Result-Variante** (ein
Wert); `ResultError` ist eine **geworfene Ausnahme**.

### UnwrapFailedError

`ResultError`-Subklasse und die einzige tatsächlich geworfene Ausnahme der
Bibliothek: ausgelöst von fehlgeschlagenem `unwrap`/`expect`/`unwrap_err`/`expect_err`
— sowohl auf `Result` als auch auf `Option`.

- Invariante: Auch `Option.unwrap` wirft diese **Result-seitige** Klasse, nicht
  einen `OptionError`.

*Avoid:* eine eigene „OptionUnwrapError" erwarten — es gibt nur diese eine.

### OptionError

Wurzel der Option-seitigen Fehlerhierarchie (`Exception`-Subklasse). Wird nie direkt
geworfen.

*Avoid:* `OptionError` als Oberklasse von `UnwrapFailedError` annehmen — letztere
hängt unter `ResultError`, nicht unter `OptionError`.

### TransposeError

`OptionError`-Subklasse, deklariert für gescheiterte `transpose`-Aufrufe. Aktuell
**toter Begriff**: `transpose` gibt in allen Fällen ein `Ok` zurück und wirft diese
Ausnahme nirgends.

*Avoid:* `try`/`except TransposeError` um `transpose` schreiben — der Block fängt nie
etwas. Der Begriff existiert als reserviertes Vokabular, nicht als Laufzeitverhalten.

## Beispieldialog

**1 — `Some(None)` ist nicht „vorhanden"**

> **Entwickler:** Ich packe ein optionales Ergebnis in `Some(result)`. Wenn `result`
> mal `None` ist, behalte ich doch immer noch ein „vorhandenes" `Some`, oder?
>
> **Expertin:** Nein. `Option` benutzt `None` als Leer-Sentinel, deshalb kollabiert
> `Some(None)` zu `Null()` — `Some(None) == Null()` ist `True`. Wenn „vorhanden, aber
> None" ein gültiger Zustand sein muss, ist `Option` der falsche Typ. Für „gelungen
> mit Wert `None`" nimm `Ok(None)`.

**2 — `Option.unwrap_or` prüft Truthiness, nicht Anwesenheit**

> **Entwickler:** Dann hole ich den Wert eben sicher mit `Some(0).unwrap_or(42)` —
> das gibt `0` zurück.
>
> **Expertin:** Es gibt `42` zurück. `Option.unwrap_or` entscheidet per Wahrheitswert
> (`self._content or default`), und `0` ist falsy. Dieselbe Falle haben `0`, `""` und
> `[]`. Willst du nur auf Anwesenheit prüfen, nutze `ok_or` (prüft `is None`) oder
> Pattern-Matching. Auf der `Result`-Seite tritt das nicht auf: `Ok(0).unwrap_or(42)`
> ist `0`.

**3 — `map` vs. `and_then` (doppelte Verschachtelung)**

> **Entwickler:** Ich transformiere mit `parse(s).map(sq_then_to_string)` — `parse`
> und `sq_then_to_string` geben beide ein `Result` zurück.
>
> **Expertin:** Dann hast du am Ende `Ok(Ok("4"))` — `map` verpackt den Rückgabewert
> erneut. Weil deine Funktion bereits ein `Result` liefert, willst du `and_then`
> (flatmap): das reicht das innere `Result` flach durch. Faustregel: liefert die
> Funktion einen **rohen** Wert → `map`; liefert sie ein **verpacktes** → `and_then`.

**4 — `unwrap` ist kein Getter**

> **Entwickler:** Mein `unwrap()` hat die Funktion mit einer Exception verlassen,
> obwohl ich gar keine geworfen habe. Ich dachte, das ist ein Getter.
>
> **Expertin:** `unwrap` ist partiell: auf `Err`/`Null` wirft es `UnwrapFailedError`.
> Es ist kein sicherer Lesezugriff. War der `Err`-Wert selbst eine `Exception`, wird
> sie über `raise ... from` als Ursache verkettet. Für garantiert wurffreien Zugriff
> nimm `unwrap_or`, `unwrap_or_else` oder verzweige per `match` auf `Ok(v)`/`Err(e)`.
