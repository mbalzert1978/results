# Entscheidungs-Log — Issue #13 (Option-Familie in eigenes Modul `option.py`)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default.

Phase 1: reiner Strukturschnitt. Kein neues Verhalten, keine Vertragsänderung —
nur Umzug der `Option`-Familie. Muss vor jeder Phase-2-Methodenarbeit mergen, die
auf disjunkten Dateien für `Result` und `Option` aufbaut (zwei parallele Lanes).

## E1 — Kein Rename `results.py → result.py`

- **Offener Punkt:** Beim Herausziehen von `Option` läge ein paralleles
  Umbenennen `results.py → result.py` nahe (symmetrische `result.py`/`option.py`).
- **Entscheidung:** `Result`/`Ok`/`Err` bleiben in `src/results/results.py`. Neu
  ist allein `src/results/option.py`.
- **Begründung:** (4) ponytail/minimaler Diff: ein Rename berührt jede
  importierende Zeile und vergrößert den Diff ohne Verhaltensgewinn. (2) Zwei
  Schwester-Lanes editieren konkurrierend `Ok.is_err_and` und `Err.unwrap` in
  `results.py` — ein Rename würde jeden ihrer Patches kollidieren lassen.
- **Verworfen:** `results.py → result.py` umbenennen.

## E2 — Import-Zyklus per funktionslokaler (deferred) Imports brechen

- **Offener Punkt:** Die Abhängigkeit ist bidirektional. `results → option`:
  `Result.ok()`/`err()` bauen `Some`/`Null`. `option → results`:
  `Option.transpose()`/`ok_or()`/`ok_or_else()` bauen `Ok`/`Err`,
  `Null.expect()`/`unwrap()` werfen das `Result`-seitige `UnwrapFailedError`.
- **Entscheidung:** `results.py` importiert `Some`/`Null` regulär am Modulkopf
  (`from .option import Null, Some`); `option.py` importiert `Ok`/`Err`/
  `UnwrapFailedError` **funktionslokal** in genau den Methoden, die sie
  konstruieren bzw. werfen (`Some.ok_or`/`ok_or_else`/`transpose`, `Null.ok_or`/
  `ok_or_else`/`transpose`/`expect`/`unwrap`). Jede Verschiebung ist mit
  `# ponytail:` markiert.
- **Begründung:** (3)/(4) Funktionslokale Imports sind das Standard-Python-Idiom
  gegen Zyklen — kein neues Modul, kein Mehrgewicht. Asymmetrie ist gewollt: weil
  die `Result`-Methodenkörper laut Disjunktheits-Constraint (E3) **byte-identisch**
  bleiben müssen, durfte `results.py` seine `Some`/`Null`-Nutzung **nicht** auf
  deferred Imports umstellen — also trägt `results.py` den Top-Level-Import und
  `option.py` die Latenz. So ist `option.py` in Isolation importierbar (kein
  Top-Level-`results`-Import), und `import results.results` lädt `option.py`
  vollständig, bevor es weiterläuft. Alle drei Importreihenfolgen (`results`,
  `results.results`, `results.option`) sind ohne `ImportError` getestet.
- **Verworfen:** Gemeinsames privates `_base.py` für Fehlerhierarchie/ABCs. Das
  Issue erlaubt diese höhere Sprosse nur, wenn deferred Imports unhandlich werden
  — bei sieben kleinen, kommentierten Call-Sites tun sie das nicht (YAGNI).

## E3 — Disjunktheits-Constraint: `Result`-Methodenkörper byte-identisch

- **Offener Punkt:** Zwei parallele Lanes editieren gleichzeitig
  `Ok.is_err_and` und `Err.unwrap` in `results.py`.
- **Entscheidung:** Der `results.py`-Diff ist begrenzt auf (a) die Importzeilen am
  Dateikopf und (b) die Löschung des verschobenen `Option`/`Some`/`Null`-Blocks.
  Kein `Result`/`Ok`/`Err`-Methodenkörper wird angefasst — die `Some(...)`/
  `Null()`-Aufrufe darin bleiben unverändert und werden vom Top-Level-Import
  gedeckt.
- **Begründung:** (2) Koordinations-Konvention: disjunkte Zeilenbereiche →
  unabhängig mergebare PRs. Die Annotationen `Option[...]` in den `Result`-Köpfen
  bleiben dank `from __future__ import annotations` reine Strings; ihr Typ wird via
  `if TYPE_CHECKING: from .option import Option` aufgelöst — kein Laufzeit-Import
  nötig.

## E4 — Invariante an der Konstruktionsgrenze unverändert mitumgezogen

- **Offener Punkt:** Schwächt der Umzug die Garantie „kein öffentlicher Pfad
  erzeugt einen ungültigen Zustand"?
- **Entscheidung:** Der `Some.__init__`-Guard (`Some(None)` → `ValueError`) zieht
  unverändert nach `option.py`. Keine zusätzlichen oder duplizierten Per-Methoden-
  `None`-Checks. Ein fokussierter Test (`test_public_api.py`) belegt, dass der
  Guard nach dem Umzug weiterhin feuert.
- **Begründung:** (1) `CLAUDE.md`/`CONTEXT.md`-Invariante: Abwesenheit ist
  strukturell (`Null()`), `None` ist allein der Abwesenheits-Sentinel; die Garantie
  wird an genau einer Grenze (Konstruktor) durchgesetzt, nicht verstreut.

## E5 — Doku-Synchronisation (nur Layout, keine Verträge)

- **Offener Punkt:** Welche Doku berührt ein reiner Umzug?
- **Entscheidung:** `CLAUDE.md`-Architekturabsatz („the entire library is one
  module" → Zwei-Modul-Layout + Zyklusbruch-Hinweis) und der „Note"-Absatz;
  README „Project Structure" (jetzt `option.py` statt `results.pyi`,
  `test_public_api.py` statt `test_factories.py`); `CONTEXT.md` nur die eine
  Modul-Referenz in der Präambel (Zeile 6) um `option.py` ergänzt.
- **Begründung:** (1) `CONTEXT.md` ist ein Glossar von Begriffen/Verträgen — ein
  reiner Umzug ändert keinen Vertrag und keinen Namen, also wird nur die
  Layout-Aussage korrigiert, kein Glossar-Eintrag. Der Doc-String-Verweis
  `results.results.UnwrapFailedError` in `Option.unwrap` wurde auf
  `results.option.UnwrapFailedError` aktualisiert (Teil des verschobenen Blocks,
  kein `Result`-Körper).
