# Joint thermodynamic compatibility of two autocatalytic cores is ∃ℝ-complete

Given a finite reversible reaction network and two supplied valid potential autocatalytic cores, joint compatibility asks for one positive activity vector that realizes the prescribed current directions and strictly produces every species in each core. The boxed and unboxed promise problems are complete for the existential theory of the reals under polynomial-time binary Turing reductions. The input factors are fixed positive rationals at most two. The boxed result has internal activities in `[1/4,1/2]`, external catalyst activities in `[1/2,1]` and maximum side molecularity six. The unboxed result allows arbitrary positive activities and has maximum side molecularity eight. Hardness outputs satisfy signed core minimality on both source verdicts.

The proof includes an independently encoded existential-real language, proved source hardness, actual polynomial-time Turing transducers, exact serialization of the original literal chemical model, and total-feasibility membership with repeated-squaring circuits for binary exponents. `CLAIM_MAP.md` identifies the exact statements and the manuscript's conventional refinements.

## Contents

- `Challenge.lean`: independent data, semantics, encoding, complexity model and the two classification statements. Its intentional proof holes are confined to theorem proofs and proof-valued fields.
- `Solution.lean`: proved classifications and selected axiom readback.
- `proofs/`: the exact needed proof closure, including preserved original semantic interfaces and attributed Complexitylib modules.
- `comparator.json`: exactly the two complete classification targets and the three permitted standard axioms.
- `paper/`: manuscript PDF, LaTeX source, bibliography and exact-arithmetic example script.
- `evidence/`, `EVIDENCE.md`: source identities and the distinction between reused native evidence and fresh checks.
- `.github/workflows/palomar-submission.yml`: pinned, manual-only official workflow; execution is a separate step.

## Reproduction

Use `leanprover/lean4:v4.35.0-rc2` and the committed `lake-manifest.json`. Mathlib is pinned at `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Preserve the manifest rather than updating dependencies.

```sh
lake exe cache get
lake build Solution Challenge
lake comparator --config comparator.json --paranoid
python paper/check_paper.py
```

Comparator requires Linux with its default bubblewrap sandbox and the bundled verification tools available. The three permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. The Challenge intentionally contains statement proof holes; they are not solution proof evidence. Manuscript compilation instructions are in `paper/BUILD.md`. Reproduction commands describe a fresh source build; the saved local evidence also reuses authenticated unchanged native artifacts, as detailed in `EVIDENCE.md`.

See `THIRD_PARTY_NOTICES.md` for upstream credits and licenses. Manuscript author and affiliation fields are deliberately blank and are separate from repository metadata.
