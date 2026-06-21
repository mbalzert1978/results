# results — Ubiquitous Language

Dieses Dokument hält die *Ubiquitous Language* des `results`-Repositories fest:
die verbindlichen Fachbegriffe, ihre präzisen Definitionen und bewusste
Abgrenzungen (was ein Begriff **nicht** meint). Maßgeblich ist immer der Code in
[src/results/results.py](src/results/results.py) (Familie `Result`/`Ok`/`Err`)
und [src/results/option.py](src/results/option.py) (Familie `Option`/`Some`/`Null`);
weicht dieses Dokument vom Code ab, gilt der Code — und das Dokument ist zu
korrigieren.

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
  `flatten`/`zip`.
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

Abstrakte Basis (`abc.ABC`) für genau zwei `@final` Varianten: `Some` (vorhanden)
und `Null` (abwesend) — **strukturell** wie `Result`/`Ok`/`Err` modelliert. Die
Abwesenheit steckt im **Typ** (eine eigene `Null`-Variante), nicht in einem
gespeicherten Sentinel-Wert. Jede Methode ist auf der Basis abstrakt und auf beiden
Varianten implementiert; welche Variante vorliegt, entscheidet die **Polymorphie**,
nie eine `_content is None`- oder Truthiness-Abfrage im Methodenrumpf.

- Invariante: `Option` selbst wird nie instanziiert (die ABC ist nicht direkt
  konstruierbar) — eine Instanz ist immer **genau eine** der Varianten `Some` oder
  `Null`. `None` ist ausschließlich das Absenz-Sentinel mit genau **einer**
  Repräsentation, `Null()`. `Some(None)` ist daher verboten und wirft
  `ValueError`; ein lebendes `Some` umschließt nie `None`.

*Avoid:* „`typing.Optional`", „nullable Referenz". `Option` ist ein eigenes
Wrapper-Objekt; `Optional[T]` ist bloß `T | None` ohne Methoden.

### Some

Die vorhandene Variante von `Option`; `@final`-Subklasse, die genau einen Wert vom
Typ `T` hält. `Some(value)` ist ihr Konstruktor.

- Invariante: ein lebendes `Some` umschließt **nie** `None`. `Some(v).is_some()`
  ist `True` für jedes `v is not None`; `Some(None)` wirft `ValueError` (Guard in
  `Some.__init__`).

*Avoid:* „Just" (Haskell), „present()". `Some(5)` ist ein Container um `5`, nicht die
Zahl `5` selbst.

### Null

Die abwesende Variante von `Option`; `@final`-Subklasse ohne gespeicherten Wert.
`Null()` ist ihr Konstruktor und nimmt **keine** Argumente.

- Invariante: `Null().is_none()` ist `True`; alle Varianten sind untereinander
  gleich (`Null() == Null()`) und von jedem `Some(...)` verschieden. `Some(None)`
  existiert nicht — die Konstruktion wirft `ValueError`.

*Avoid:* „Pythons `None`", „Nil", „Nothing". `Null()` ist ein eigenständiger
`Option`-Typ für Abwesenheit — nicht das `None` selbst und kein `Some`, das ein
`None` umhüllt. Die in einigen Docstrings gezeigten Aufrufe mit Argument
(`Null("Error")`, `Null(10)`) sind fehlerhaft: `Null` nimmt keine Parameter und
würde mit `TypeError` scheitern.

### is_none_or / inspect

Zwei `Option`-Methoden für **nicht-transformierende** Interaktion mit dem
enthaltenen Wert:

- `is_none_or(fn)` — gibt `True` zurück, wenn die Option `Null` ist, oder wenn
  sie `Some(v)` ist und `fn(v)` wahr ergibt. Komplement zu `is_some_and`:
  `Null()` → immer `True`; `Some(v)` → `fn(v)`.
- `inspect(fn)` — ruft `fn(v)` auf (ausschließlich für Nebeneffekte wie Logging
  oder Debugging), wenn die Option `Some(v)` ist, und gibt **dasselbe Objekt**
  zurück (`result is self`). Für `Null` ist es ein No-op. Der Rückgabewert von
  `fn` wird ignoriert.

Beide Methoden sind polymorphisch implementiert (`@abc.abstractmethod` auf `Option`,
je eine Implementierung auf `Some` und `Null`); kein `isinstance`- oder
`_value is None`-Check im Körper. `inspect` erzeugt keine neuen Wrapper — weder
`Some(...)` noch `Null()` — und kann deshalb auch nie `Some(None)` erzeugen.

*Avoid:* `inspect` mit `map` verwechseln. `map` transformiert und gibt einen
**neuen** Container zurück; `inspect` gibt `self` zurück und ist für reine
Nebeneffekte gedacht.

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
- Invariante (`Option`): Der Rückfall greift **strukturell** genau bei `Null` —
  per Polymorphie auf der Variante, nicht per Wahrheitswert. Folge: Falsy-Inhalte
  wie `0`, `""`, `[]` sind **vorhanden** und werden zurückgegeben;
  `Some(0).unwrap_or(42)` ist `0`. `None` ist kein Wert, sondern Absenz:
  `Some(None)` ist verboten und wirft `ValueError`; Abwesenheit drückt man mit
  `Null()` aus.
  Dieselbe strukturelle Logik gilt für die Iteration über ein `Option`: `Some(0)`
  iteriert zu `[0]`, `Null()` zu `[None]`.

*Avoid:* anzunehmen, `Option.unwrap_or` prüfe Truthiness — der alte
`self._content or default`-Trick ist weg. Es entscheidet die Variante (`Some` vs.
`Null`), genau wie auf der `Result`-Seite.

### map

Transformiert den **enthaltenen Wert** und gibt einen Container desselben Typs
zurück, ohne die fehler-/leerseitige Variante anzufassen: `Result.map` wirkt auf
`Ok` (und `map_err` auf `Err`), `Option.map` wirkt auf `Some`.

- Invariante: Die übergebene Funktion liefert einen **rohen** Wert; `map` verpackt
  ihn wieder. `Err`/`Null` bleiben unverändert.

*Avoid:* `map` mit `and_then` verwechseln. Gibt deine Funktion bereits ein
`Result`/`Option` zurück, erzeugt `map` eine **doppelte** Verschachtelung.

### inspect / inspect_err

Seiteneffekt-Inspektoren, die den Container **unverändert** zurückgeben:
`Result.inspect(fn)` ruft `fn` mit dem `Ok`-Wert auf (Nebeneffekt) und gibt
`self` zurück; bei `Err` ist es ein No-op. `Result.inspect_err(fn)` spiegelt
das: `fn` wird mit dem `Err`-Wert aufgerufen, bei `Ok` kein Aufruf.

- Invariante: Rückgabe ist **dasselbe Objekt** (`inspect(fn) is self`) — kein
  neuer Container, keine Transformation. Der Rückgabewert von `fn` wird
  verworfen.
- Verwendungszweck: Logging, Metriken, Debuggen in einer Methodenkette, ohne
  den Datenfluss zu unterbrechen.

*Avoid:* `inspect` mit `map` verwechseln. `map` **transformiert** den Wert und
erzeugt einen neuen Container; `inspect` lässt den Container unangetastet und
dient allein dem Nebeneffekt.

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

- Invariante: `ok_or`/`ok_or_else` entscheiden **strukturell** über die Variante
  (`Some` vs. `Null`), nicht per Truthiness oder `is None`, daher bleibt `Some(0)`
  ein `Ok(0)`.
- `Ok(None).ok()` wirft `ValueError` — `Ok(_).ok()` würde `Some(_)` bauen, und
  `Some(None)` ist verboten (`Ok(v).ok()` ist `Some(v)` für `v is not None`).

*Avoid:* „Cast"/„isinstance-Umwandlung". Es entsteht jeweils ein **neues** Objekt der
Zielfamilie; das Original wird nicht verändert.

### transpose

`Option.transpose()` vertauscht die Schachtelung eines `Option` **eines** `Result`
in ein `Result` **eines** `Option`:

- `Null()` → `Ok(Null())`
- `Some(Ok(v))` → `Ok(Some(v))` (ist `v` `None`, wirft `Some(v)` → `ValueError`)
- `Some(Err(e))` → `Err(e)`
- nicht-`Result`-Inhalt → `Ok(self)` (unverändert eingepackt)

*Avoid:* an eine Matrix-Transposition denken — `transpose` wirft nie und meint
ausschließlich das Tauschen der beiden Schachtelungs-Ebenen.

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

`ResultError`-Subklasse und die einzige *bibliothekseigene* geworfene Ausnahme:
ausgelöst von fehlgeschlagenem `unwrap`/`expect`/`unwrap_err`/`expect_err` — sowohl
auf `Result` als auch auf `Option`. (Daneben wirft allein die verbotene
Konstruktion `Some(None)` das eingebaute `ValueError`.)

- Invariante: Auch `Option.unwrap` wirft diese **Result-seitige** Klasse; es gibt
  keine eigene Option-seitige Fehlerklasse.

*Avoid:* eine eigene „OptionUnwrapError" erwarten — es gibt nur diese eine.

## Beispieldialog

**1 — `Some(None)` ist verboten — `None` ist Absenz**

> **Entwickler:** Ich packe ein optionales Ergebnis in `Some(result)`. Wenn `result`
> mal `None` ist, behalte ich doch immer noch ein „vorhandenes" `Some`, oder?
>
> **Expertin:** Nein. `None` ist ausschließlich das Absenz-Sentinel und hat genau
> **eine** Repräsentation: `Null()`. `Some(None)` ist deshalb verboten und wirft
> `ValueError`. „Vorhanden, aber `None`" gibt es nicht: für einen echten Wert nimm
> etwas, das nicht `None` ist; für Abwesenheit `Null()`. Hast du ein optionales
> Zwischenergebnis (`T -> Option[U]`), nimm `and_then`, nicht `map` (`T -> U`).

**2 — `Option.unwrap_or` prüft die Variante, nicht Truthiness**

> **Entwickler:** Dann hole ich den Wert eben sicher mit `Some(0).unwrap_or(42)` —
> das gibt `0` zurück.
>
> **Expertin:** Richtig, es gibt `0` zurück. `Option.unwrap_or` entscheidet
> **strukturell** über die Variante (`Some` vs. `Null`), nicht per Wahrheitswert.
> Falsy-Werte wie `0`, `""`, `[]` bleiben „vorhanden" und werden geliefert; nur
> `Null()` fällt auf den Default zurück. `None` ist kein Wert — `Some(None)` ist
> verboten (`ValueError`). Genau wie auf der `Result`-Seite: `Ok(0).unwrap_or(42)`
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
