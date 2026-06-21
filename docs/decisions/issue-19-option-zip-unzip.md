# Entscheidungs-Log — Issue #19 (Option: `zip` / `unzip`)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Option`-Semantik (std) · 4. ponytail-Default.

Lane O: ausschließlich `src/results/option.py`, zugehöriger Testmodul und CONTEXT.md
(Anker `### and_ / xor`). Kein `results.py`-Diff.

## E1 — `zip`: Dispatch via `other.map` statt Flag-Check

- **Offener Punkt:** `zip` muss auf beide Varianten von `other` reagieren (`Some` → Tupel
  wrappen, `Null` → `Null()` zurückgeben). Wie ohne `isinstance`-Check?
- **Entscheidung:** `Some.zip(other)` → `other.map(lambda b: (self._value, b))`.
  `map` auf `Some(b)` ergibt `Some((a, b))`; `map` auf `Null()` ergibt `Null()`.
  Kein Flag-Check, kein `isinstance`, kein `is None`.
- **Begründung:** (1) Dispatch-Invariante: welche Variante vorliegt, entscheidet die
  Polymorphie — hier die von `other`. Exakt dasselbe Muster wie `xor` via `map_or`.
  (4) ponytail: eine Zeile. Kommentiert mit `# ponytail:` im Code.
- **Verworfen:** `if other.is_some(): return Some((self._value, other.unwrap()))
  else: return Null()` (Truthiness-äquivalent, bricht die Dispatch-Invariante).

## E2 — `zip` auf `Null`: gibt direkt `Null()` zurück

- **Entscheidung:** `Null.zip(other)` → `return Null()`. Kein Blick auf `other`'s
  Variante nötig — ein `Null` auf der linken Seite ergibt immer `Null()`.
- **Begründung:** (3) Rust-Semantik: `Null.zip` ist immer `Null()`, unabhängig von
  `other`. (4) ponytail: eine Zeile, kein Branching.

## E3 — `unzip`: Typ-Annotation mit Self-Type-Generic

- **Offener Punkt:** `unzip` operiert nur sinnvoll auf `Option[tuple[A, B]]`. Wie
  annotiert man `self` korrekt ohne `isinstance`-Check und ohne TypeVar?
- **Entscheidung:** PEP 695 Self-Type-Generic auf der Implementierung:
  `def unzip[A, B](self: Some[tuple[A, B]]) -> tuple[Option[A], Option[B]]`.
  Auf der ABC: `def unzip[A, B](self: Option[tuple[A, B]]) -> tuple[Option[A], Option[B]]`.
- **Begründung:** (2) Projekt-Konvention — PEP 695 Generics durchgängig.
  (1) mypy akzeptiert Self-Type-Narrowing in `@abc.abstractmethod`-Stubs.
  Kein `TypeVar`, keine `Generic`-Umstellung nötig.
- **Verworfen:** `def unzip(self) -> tuple[Option[Any], Option[Any]]` (zu schwach
  für statische Analyse).

## E4 — `unzip`: Invarianten-Interaktion `Some(None)` — kein manueller None-Check

- **Offener Punkt:** Was passiert, wenn eine Tupelkomponente `None` ist, z. B.
  `Some((None, 5)).unzip()`? Braucht `unzip` einen eigenen `None`-Check?
- **Entscheidung:** **Kein** manueller `None`-Check in `unzip`. `Some.unzip` destrukturiert
  `a, b = self._value` und ruft `Some(a)` bzw. `Some(b)` auf. Ist eine Komponente
  `None`, wirft `Some.__init__` bereits `ValueError("Some(None) is forbidden; …")`.
  Der Guard in `Some.__init__` ist der **einzige** Enforcement-Punkt — `unzip`
  verlässt sich darauf.
- **Begründung:** (1) CLAUDE.md-Invariante: „Enforced EXACTLY ONCE at the construction
  boundary: `Some.__init__`." Jeder zusätzliche Check wäre Duplikation.
  (4) ponytail: weniger Code, gleiche Korrektheit. Explizit mit zwei Parametrized-Tests
  abgesichert: `Some((None, 5)).unzip()` und `Some((5, None)).unzip()` werfen beide
  `ValueError`.
- **Verworfen:** `if a is None or b is None: raise ValueError(...)` in `unzip` (verletzt
  das Single-Enforcement-Prinzip).

## E5 — Methodenplatzierung: alphabetisch nach `xor`

- **Entscheidung:** `zip` und `unzip` werden **nach** `xor` eingefügt — alphabetisch
  kommen `u` (unzip) und `z` (zip) nach `x` (xor). Reihenfolge im Körper: `unzip`
  vor `zip` (u < z). Identisch in `Option`-ABC, `Some` und `Null`.
- **Begründung:** (2) Bestehende Konvention — alle Methoden sind alphabetisch
  geordnet (siehe Issue #17, #18).

## E6 — CONTEXT.md: Abschnitt `### zip / unzip` + Korrektur im Scope-Abschnitt

- **Offener Punkt:** Wo genau in CONTEXT.md?
- **Entscheidung:** Unmittelbar nach `### and_ / xor`, vor `### unwrap`.
  Zusätzlich: der „Nicht-Teil-des-Scopes"-Abschnitt erwähnte `flatten`/`zip` als
  bewusst fehlend — `zip` ist jetzt vorhanden, daher wurde `zip` aus dieser Liste
  entfernt (nur `flatten` verbleibt).
- **Begründung:** (1) Aufgabenstellung: Anker `### and_ / xor`. (2) Konsistenz —
  das Glossar muss den Code widerspiegeln.

## E7 — TDD: Failing Tests vor der Implementierung

- **Vorgehen:** Acht neue Testfälle (vier für `zip`, zwei für `unzip` happy path,
  zwei für `unzip` None-Komponente raises) als parametrized-Einträge in
  `tests/results/test_option.py` eingefügt, **bevor** die Implementierung in
  `option.py` erfolgte. Acht rote Fehler bestätigt (`AttributeError: 'Some' object
  has no attribute 'zip'`), dann alle 205 Tests grün.
