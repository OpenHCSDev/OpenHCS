# SCP Submission Metadata

## Title
Typing Discipline Selection for Object-Oriented Systems: A Formal Methodology with Empirical Validation

## Keywords
1. Nominal typing
2. Structural typing
3. Duck typing
4. Python metaprogramming
5. Type systems
6. Method Resolution Order (MRO)
7. Software architecture
8. Code quality metrics

## Highlights (3-5 bullet points for Elsevier)
- Duck typing is retrofit tooling; nominal typing is greenfield tooling—a correctness criterion, not style choice
- Four derivable code quality metrics: duck typing density, nominal typing ratio, provenance capability, resolution determinism
- Formal proof that duck typing cannot provide provenance (Lean 4 machine-checked)
- 13 case studies from production bioimage analysis platform demonstrating elimination of scattered hasattr() checks via nominal migration
- Methodology applicable to any language with explicit inheritance hierarchies

## Author Information
- Tristan Simas (corresponding author)
- Affiliation: [your institution]
- Email: tristan.simas@mail.mcgill.ca
- ORCID: [if you have one]

## CRediT Author Statement
Tristan Simas: Conceptualization, Methodology, Software, Formal analysis, Investigation, Writing – original draft, Writing – review and editing

## Funding Statement
This research did not receive any specific grant from funding agencies in the public, commercial, or not-for-profit sectors.

## Declaration of Competing Interest
The author declares no competing interests.

## Data Availability Statement
The OpenHCS codebase referenced in this paper is available at: https://github.com/trissim/openhcs
The Lean 4 proofs are included in the supplementary material.

---

## Submission Checklist

- [ ] Create account at https://www.editorialmanager.com/scico
- [ ] Select "Regular Article" as article type
- [ ] Upload PDF (print HTML to PDF from browser)
- [ ] Enter title, abstract, keywords
- [ ] Add CRediT statement
- [ ] Add funding statement
- [ ] Add competing interest declaration
- [ ] Upload supplementary material (Lean proofs: proofs/nominal_resolution.lean)
- [ ] Submit

## Suggested Cover Letter

Dear Editors,

We submit "Typing Discipline Selection for Object-Oriented Systems" for consideration in Science of Computer Programming.

This paper formalizes a methodology for choosing between typing disciplines (nominal, structural, duck) in object-oriented systems. The core contribution is proving that duck typing is retrofit tooling while nominal typing is greenfield tooling—a correctness criterion, not a style preference.

We derive four measurable code quality metrics from the formal model and validate through 13 case studies from a production bioimage analysis platform. The theoretical results are machine-checked in Lean 4.

This work fits SCP's scope of bridging formal foundations with practical software development. The methodology is directly applicable to practitioners and enables automated linting tools.

Thank you for your consideration.

Sincerely,
Tristan Simas

