# Entscheidungs-Log — Issue #18 (Option: `and_` / `xor`)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Option`-Semantik (std) · 4. ponytail-Default.

Lane O: ausschließlich `src/results/option.py`, zugehöriger Testmodul und CONTEXT.md
(Anker `### is_none_or / inspect`). Kein `results.py`-Diff.

## E1 — `and_`: Trailing-Underscore wegen Python-Keyword

- **Offener Punkt:** Rust nennt die Methode `and`; Python reserviert `and` als
  Schlüsselwort.
- **Entscheidung:** `and_` (trailing underscore), analog zu `or_` im selben Modul.
- **Begründung:** (2) Konvention im Projekt — `or_` ist bereits identisch benannt.
  (3) Rust-Konvention bei Keyword-Konflikten.
- **Verworfen:** `and_opt`, `and_option` (zu wortreich; Nachbarn heißen `or_`).

## E2 — `and_`: `Some` gibt `optb` direkt zurück (Identität)

- **Entscheidung:** `Some.and_(optb)` gibt `optb` direkt zurück — keine Kopie,
  kein neuer Wrapper. `Some(1).and_(optb) is optb` gilt.
- **Begründung:** (4) ponytail: das Einfachste, das korrekt ist. `optb` ist bereits
  eine Option-Instanz; es gibt nichts zu wrappen. Identitäts-Pin im Test schreibt
  das fest.

## E3 — `xor` auf `Null`: gibt `optb` direkt zurück

- **Entscheidung:** `Null.xor(optb)` gibt `optb` zurück — keine Inspektion von
  `optb`'s Variante, kein Branch. `Null().xor(optb) is optb` gilt.
- **Begründung:** (3) Rust-Semantik: `Null.xor` liefert `Some` iff `optb` `Some`
  ist, sonst `Null` — das ist genau `optb` selbst. (4) ponytail: eine Zeile,
  kein Branching.

## E4 — `xor` auf `Some`: Dispatch via `optb.map_or` statt Flag-Check

- **Offener Punkt:** `xor` muss auf beide Varianten von `optb` reagieren. Wie
  ohne `isinstance`-Check?
- **Entscheidung:** `Some.xor(optb)` → `optb.map_or(self, lambda _: Null())`.
  `map_or` ruft `lambda _ : Null()` auf (→ `Null()`), wenn `optb` `Some` ist;
  gibt `self` zurück (→ `self`), wenn `optb` `Null` ist. Keine Flag-Variable,
  kein `isinstance`, kein `is None`.
- **Begründung:** (1) Dispatch-Invariante: welche Variante vorliegt, entscheidet
  die Polymorphie — hier die von `optb`. (4) ponytail: kürzeste korrekte Zeile.
  Kommentiert mit `# ponytail:` im Code.
- **Verworfen:** `if optb.is_none(): return self else: return Null()` (Truthiness-
  äquivalent, bricht die Dispatch-Invariante).

## E5 — Methoden-Platzierung: alphabetisch

- **Entscheidung:** `and_` vor `and_then` (alphabetisch: `and_` < `and_then`);
  `xor` nach `unwrap_or_else` (kein alphabetischer Geschwister nach `x`).
  Identisch in `Option`-ABC, `Some` und `Null`.
- **Begründung:** (2) Bestehende Konvention — alle Methoden sind alphabetisch
  geordnet (siehe Issue #17).

## E6 — TDD: Failing Tests vor der Implementierung

- **Vorgehen:** Zehn neue Testfälle (vier für `and_`, vier für `xor`, zwei
  Identitäts-Pins) als parametrized-Einträge in `tests/results/test_option.py`
  eingefügt, **bevor** die Implementierung in `option.py` erfolgte. Zehn rote
  Fehler bestätigt, dann alle 188 grün.

## E7 — CONTEXT.md: neuer Abschnitt nach `### is_none_or / inspect`

- **Offener Punkt:** Wo genau in CONTEXT.md?
- **Entscheidung:** Unmittelbar nach `### is_none_or / inspect`, vor `### unwrap`.
  Kein anderer CONTEXT.md-Abschnitt berührt.
- **Begründung:** (1) Aufgabenstellung: Anker `### is_none_or / inspect`. (2)
  Disjunktheit: nachgelagerte Abschnitte gehören zu anderen Lanes.
