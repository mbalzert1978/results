# Entscheidungs-Log — Pythonic-/Declarative-Refactor-Audit

Vollautonomer Modus. DELIVERABLE = Issues (kein Code). Entscheidungsreihenfolge:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
2. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default (laziest funktionierend).

## E1 — Scope A (Mikro-Cleanups), nicht B (Paradigmenwechsel)

- **Entscheidung:** Nur Variante **A** — Mikro-Cleanups INNERHALB des bestehenden
  polymorphen Designs. Variante **B** (Union-Alias + zentraler `match`-Dispatch)
  ist OUT OF SCOPE.
- **Begründung:** B kehrt Commit `c7f3b3c` („sealed two-state type with polymorphic
  dispatch") und die CLAUDE.md/CONTEXT.md-Invariante um (Variantenverhalten via
  Polymorphie, nie Flag/`isinstance`/Truthiness im Rumpf). In diesem Codebase IST
  Polymorphie bereits die declarative Form. B gehört in eine separate, ausdrückliche
  ADR, nicht in einen „Optimierungs"-Pass.
- **Verworfen:** B hier einschmuggeln.

## E2 — Union-Alias (`type ResultLike[T,E] = Ok[T] | Err[E]`) verworfen

- **Entscheidung:** Kein Union-Alias.
- **Begründung:** Unions nützen auf Annotations-/Call-Site-Ebene nur, wenn ein
  echter *Consumer* exhaustives `match`-Narrowing braucht. `results` ist selbst die
  Bibliothek und hat hier keinen solchen Consumer (ponytail Sprosse 1: muss nicht
  existieren). Ändert die interne Architektur ohnehin nicht.

## E3 — Kandidaten-Inventar (real durchgegangen, nicht geraten)

Grep-belegt (`self.is_(ok|err|some|none)`, `is None`, Schleifen, `raise … from`):

**Aufgenommen (reißen die Latte: pythonischer ∧ verhaltensneutral ∧ keine Design-Regression):**

- **C1 — `Ok.is_err_and` (results.py:181-182):** `return not self.is_ok()`.
  Einziges Vorkommen eines Self-Prädikat-Dispatch im Rumpf einer Varianten-Impl.
  Pythonic-Fix = Polymorphie: konstantes `return False` (spiegelt `Err.is_ok_and`,
  results.py:269-270). KEIN `match` auf den eigenen Typ. Verhaltensneutral, da
  `Ok.is_ok()` `Literal[True]` ist und `fn` in alt wie neu ignoriert wird.
  Abgedeckt: `test_is_err_and`-Fall „…when Ok value should return False".

- **C2 — `Err.unwrap` (results.py:294-301):** `exc.__cause__ = self._inner_value`
  unmittelbar vor `raise exc from self._inner_value`. `raise X from Y` setzt
  `__cause__` (und `__suppress_context__`) bereits → die Zuweisung ist redundant.
  Reine Redundanz-Entfernung, Vertrag (CONTEXT.md, Err-Invariante l.69-71) bleibt.
  Abgedeckt: `test_unwrap_err`-Fall „…with exception" (BaseException-Zweig).

**Verworfen (ponytail Sprosse 1 / Cleverness-Churn):**

- `Some.transpose` — nutzt bereits `match` auf den Inner-Value (Daten-Match, der
  erlaubte Fall). Keine Änderung.
- `Result.from_fn` / `Option.from_fn` — bereits idiomatisch (`try/except/else` bzw.
  Walrus + Conditional-Expression). Keine Änderung.
- `Some.filter` — bereits Conditional-Expression. Keine Änderung.
- `hash(x) * 41`-Duplikat über Ok/Err/Some/Null — DRY-Reiz, aber ein gemeinsamer
  Helper/Mixin fügt Abstraktion hinzu, die der polymorphe Stil bewusst meidet. Skip.
- Imperative Schleifen mit Akkumulator → comprehension: **keine** im Code. Skip.

## E4 — Slicing & Doku

- **Entscheidung:** Zwei disjunkte Issues, PR-pro-Issue. Es gibt keine `option.py`;
  alles liegt in `results.py`. C1 (Klasse `Ok`, Z. 181-182) und C2 (Klasse `Err`,
  Z. 294-301) sind weit getrennt und überlappen nicht → kein Merge-Konflikt,
  unabhängig grabbar.
- **CONTEXT.md/CLAUDE.md:** unverändert — keine Begriffs-/Vertragsänderung; Code
  bleibt Source of Truth.
- **Anmerkung (ponytail):** C1 und C2 sind je eine Zeile; bündelbar wären sie auch.
  Getrennt gehalten, weil der Prompt „unabhängige Issues / PR-pro-Issue" explizit
  fordert und die Ursachen verschieden sind (Self-Dispatch vs. tote Zuweisung).
