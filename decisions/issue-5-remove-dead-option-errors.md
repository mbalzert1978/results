# Entscheidungs-Log — Issue #5 (Tote Option-Fehlerhierarchie entfernen)

Vollautonomer Modus. Offene/mehrdeutige Punkte gemäß Entscheidungsreihenfolge gelöst:
1. Projekt-Domäne (`CONTEXT.md`, `CLAUDE.md`) · 2. Code-Konventionen ·
3. Rust-`Result`/`Option`-Semantik (std) · 4. ponytail-Default.

## E1 — Löschen statt „`TransposeError` real machen"
- **Offener Punkt:** Issue #5 bietet zwei Wege: tote Hierarchie löschen ODER `TransposeError` tatsächlich in `Option.transpose` werfen.
- **Entscheidung:** Löschen (`OptionError` und `TransposeError` entfernt).
- **Begründung:** (3) Rust-`Option::transpose` wirft keine dedizierte Transpose-Ausnahme — es liefert immer ein `Result`. (4) ponytail: Löschen vor Hinzufügen. Die Klassen sind nachweislich tot (`grep`: kein `raise` irgendwo). `CONTEXT.md` hält `TransposeError` bereits als „toten Begriff" fest.
- **Verworfen:** `TransposeError` in den `case _`-Zweig von `transpose` einbauen — fügt nicht angefordertes Verhalten hinzu und weicht von Rust ab.

## E2 — README Zeile 11 (Feature-Liste)
- **Offener Punkt:** Nur `TransposeError` streichen oder den ganzen „Error Handling"-Bullet umschreiben?
- **Entscheidung:** Nur die `TransposeError`-Referenz entfernen, `UnwrapFailedError` behalten.
- **Begründung:** `UnwrapFailedError` ist laut `CONTEXT.md` „die einzige tatsächlich geworfene Ausnahme" der Bibliothek — der Bullet bleibt damit wahr.
- **Verworfen:** Ganzen Bullet löschen (würde eine korrekte Aussage mitentfernen).

## E3 — Reichweite der `CONTEXT.md`-Bereinigung
- **Offener Punkt:** Neben den beiden Glossar-Einträgen referenzieren auch die Einträge `transpose` und `UnwrapFailedError` die gelöschten Klassen.
- **Entscheidung:** Diese hängenden Erwähnungen ebenfalls bereinigt — innerhalb der „Fehlerhierarchie"-Ownership von #5. Die Verhaltens-Bullets des `transpose`-Eintrags bleiben unangetastet (Grenze zu #7 gewahrt).
- **Begründung:** Vollständigkeit/Konvention: das Glossar darf keine nicht mehr existierenden Typen benennen (Code = Source of Truth).
- **Verworfen:** Nur die zwei Haupteinträge entfernen und hängende Referenzen stehen lassen.

## E4 — Breaking Change explizit machen
- **Offener Punkt:** Stillschweigend entfernen oder kennzeichnen?
- **Entscheidung:** Entfernen exportierter Namen (`OptionError`, `TransposeError`) als Breaking Change im PR-Body für Release Notes vermerkt.
- **Begründung:** Konvention: Eingriffe in die öffentliche API werden für Konsumenten sichtbar dokumentiert.
