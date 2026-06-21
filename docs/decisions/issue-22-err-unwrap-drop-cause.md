# Entscheidungs-Log — Issue #22 (Redundante `__cause__`-Zuweisung in `Err.unwrap` entfernen)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:

1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Python-Datenmodell (`raise ... from`) · 4. ponytail-Default (laziest funktionierend).

## E1 — Warum `exc.__cause__ = self._inner_value` toter Code ist

- **Offener Punkt:** Ist die explizite Zuweisung wirklich redundant, oder gibt es einen Seiteneffekt?
- **Entscheidung:** Redundant. `raise exc from self._inner_value` setzt per Python-Datenmodell (PEP 3134) sowohl `exc.__cause__ = self._inner_value` als auch `exc.__suppress_context__ = True` — beides atomar, bevor der Frame abgewickelt wird. Die vorangegangene manuelle Zuweisung überschreibt dasselbe Attribut unmittelbar danach mit identischem Wert.
- **Begründung:** CPython-Quellcode (`ceval.c`, `_PyException_SetCause`) und PEP 3134 sind eindeutig. Kein Interpreter-spezifisches Verhalten; Standard Python ≥3.0.
- **Verworfen:** Zeile beibehalten „zur Klarheit" — widerspricht ponytail und schafft falsche Suggestion, dass `raise ... from` allein nicht ausreicht.

## E2 — Scope: nur die eine Zeile

- **Offener Punkt:** Soll die `isinstance`-Branch zu `match/case` umgebaut werden?
- **Entscheidung:** Nein. Nur `exc.__cause__ = self._inner_value` löschen. Beide `raise`-Anweisungen und der `isinstance`-Check bleiben unberührt.
- **Begründung:** Issue #22 ist ausdrücklich auf diese eine Zeile beschränkt. Strukturumbau ist Scope-Creep; parallele Issues (#21 u. a.) arbeiten in Nachbarklassen. Ponytail-Prinzip: kürzeste Änderung, die das Problem löst.
- **Verworfen:** Konvertierung zu `match`-Statement, Inlining der `isinstance`-Prüfung.

## E3 — Testabsicherung vor der Löschung

- **Offener Punkt:** Der bestehende `test_unwrap_err`-Fall prüfte nur die Fehlermeldung (`match=`), nicht `__cause__`. Wo und wie die Invariante verankern?
- **Entscheidung:** Bestehende `test_unwrap_err`-Parametrisierungstabelle umstrukturieren: Parameter `expected_cause` (entweder das konkrete Exception-Objekt oder `None`) hinzugefügt; Testfunktion prüft nach dem `pytest.raises`-Block `excinfo.value.__cause__ is expected_cause`. Kein neuer Testfunktionsname.
- **Begründung:** Konvention (`CLAUDE.md`, Abschnitt *Tests*): Fälle zu bestehenden parametrisierten Tabellen mit `ids=` hinzufügen. TDD-Reihenfolge: Test zuerst grün, dann Löschung — bestätigt, dass die Verhaltensgarantie vor und nach der Änderung gilt.
- **Verworfen:** Neue eigenständige Testfunktion.

## E4 — `CONTEXT.md` bleibt unverändert

- **Offener Punkt:** Muss das Glossar angepasst werden?
- **Entscheidung:** Nein.
- **Begründung:** Der öffentliche Vertrag (`Err.unwrap` kettet `BaseException`-Werte via `__cause__`) ist identisch. Nur die interne Implementierung verliert eine überflüssige Zeile. Code ist Source of Truth; die Doku folgt nur bei Vertrags-/Verhaltensänderung (`CLAUDE.md`-Sync-Regel).
- **Verworfen:** Glossar anfassen (kein Vertragsbruch, kein Sync notwendig).
