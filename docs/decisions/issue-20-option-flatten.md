# Entscheidungs-Log — Issue #20 (Option: `flatten`)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Option`-Semantik (std) · 4. ponytail-Default.

Lane O: ausschließlich `src/results/option.py`, zugehöriger Testmodul und CONTEXT.md.
Kein `results.py`-Diff.

## E1 — `Some.flatten` gibt `self._value` direkt zurück (Identität, kein Re-Wrap)

- **Offener Punkt:** Soll `Some.flatten` den Inhalt neu in `Some(...)` einpacken
  oder direkt durchreichen?
- **Entscheidung:** `return self._value` — kein neues `Some`, kein neues `Null`.
  `self._value` ist bereits ein `Option[U]`, also das korrekte Ergebnis für alle
  drei Fälle:
  - `Some(Some(x))._value == Some(x)` → liefert `Some(x)`.
  - `Some(Null())._value == Null()` → liefert `Null()`.
- **Begründung:** (1) Aufgabenstellung: „Implement as `return self._value`". (3) Rust-
  Semantik: `Option::flatten` ist äquivalent zu `and_then(|x| x)` — die innere Option
  wird unverändert durchgereicht. (4) ponytail: kein neues Objekt, O(1), minimale
  Implementierung. Die Identitätseigenschaft (`Some(inner).flatten() is inner`) folgt
  direkt aus dem direkten Rückgabe.
- **Verworfen:** `Some(self._value.unwrap())` o. ä. (unnötiger Zwischenschritt,
  würde auf `Null()` als inner scheitern), `Null() if self._value.is_none() else
  Some(self._value.unwrap())` (instanceof/flag-Check, verletzt Polymorphie-Regel).

## E2 — Kein `None`-Check in `flatten`

- **Offener Punkt:** Muss `flatten` prüfen, ob das Ergebnis `None` ist?
- **Entscheidung:** Nein. `flatten` verpackt nichts neu — `self._value` war
  bereits beim Konstruieren von `Some(inner)` durch den Guard in `Some.__init__`
  validiert (kein `None` kommt durch). `Null()` ist kein `None`. Kein
  zusätzlicher `if result is None: raise ValueError(...)` notwendig.
- **Begründung:** (1) Aufgabenstellung: „Do NOT add any None handling." Das
  `Some(None)`-Risiko entsteht nur beim Einpacken (`Some(value)`); da `flatten`
  nichts einpackt, gibt es kein Risiko.
- **Konsequenz:** Kein `raise`-on-None-Test in der Testsuite — es gibt nichts,
  was `ValueError` auslösen könnte.

## E3 — Kein Raise-on-None-Test

- **Offener Punkt:** Soll ein Test `Some(None).flatten()` abdecken?
- **Entscheidung:** Nein. `Some(None)` kann nicht konstruiert werden
  (`Some.__init__` wirft sofort `ValueError`). Ein Test für
  `Some(None).flatten()` wäre tautologisch mit dem bestehenden
  `test_some_none_is_forbidden`-Test — er würde nicht `flatten` testen, sondern
  nur den Konstruktor-Guard. Kein neuer Test.
- **Begründung:** (2) Konvention: Tests decken das Verhalten der Methode ab,
  nicht erneut das der Konstruktoren.

## E4 — Selbst-Typ-Signatur mit PEP 695

- **Offener Punkt:** Wie soll die Signatur des Selbst-Typ-Parameters auf dem ABC
  und den konkreten Klassen aussehen?
- **Entscheidung:**
  - ABC: `def flatten[U](self: Option[Option[U]]) -> Option[U]`
  - `Some`: `def flatten[U](self: Some[Option[U]]) -> Option[U]`
  - `Null`: `def flatten[U](self: Null[Option[U]]) -> Option[U]`
- **Begründung:** (2) Konvention: alle anderen Self-Typ-Methoden (`unzip`,
  `transpose`) verwenden dieselbe PEP-695-Syntax mit `[U]` auf Methodenebene.
  Der Self-Typ auf dem Parameter bewirkt, dass mypy `flatten` nur dann als
  aufrufbar akzeptiert, wenn das äußere `Option` tatsächlich ein
  `Option[Option[U]]` ist — statische Typsicherheit ohne Laufzeit-Check.
- **Verworfen:** `TypeVar`-basierte Signaturen (wären inkonsistent mit dem
  restlichen Codebase-Stil).

## E5 — `flatten` ist äquivalent zu `and_then(identity)`

- **Notiz:** `Some(inner).flatten()` gibt `inner` zurück; dasselbe erreicht
  `Some(inner).and_then(lambda x: x)`. `flatten` ist also die benannte,
  idiomatische Form — kein `isinstance`, kein `is None`, sondern reines Flatmap
  mit der Identitätsfunktion. Die Eigenschaft wird in CONTEXT.md dokumentiert.

## E6 — TDD: Failing Tests vor der Implementierung

- **Vorgehen:** Alle vier neuen Testfälle (drei Mapping-Fälle in
  `test_flatten_collapses_one_level_of_nesting` + ein Identitäts-Pin in
  `test_flatten_some_returns_inner_option_identity`) wurden in
  `tests/results/test_option.py` eingefügt, **bevor** die Implementierung in
  `option.py` erfolgte. Vier rote Fehler (`AttributeError: 'Some'/'Null' object
  has no attribute 'flatten'`) bestätigt, dann alle 214 Tests grün.

## E7 — CONTEXT.md: neuer Abschnitt `### flatten` nach `### and_then`

- **Offener Punkt:** Wo in CONTEXT.md einfügen?
- **Entscheidung:** Unmittelbar vor `### Cross-Conversion`, nach `### and_then`.
  `flatten` ist eng mit `and_then` verwandt (es ist `and_then(identity)`);
  diese Nachbarschaft macht die Beziehung sichtbar. Außerdem wird
  `flatten` aus der „bewusst nicht in Scope"-Liste im Intro entfernt.
- **Begründung:** (2) Konvention: Methoden stehen thematisch gruppiert in
  CONTEXT.md; `flatten` gehört in die Combinator-Gruppe.
