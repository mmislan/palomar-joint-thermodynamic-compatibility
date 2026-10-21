# Verification evidence

The complete boxed and unboxed classification is proved in Lean 4.35.0-rc2. The selected mathematical source closure contains 1,195 accepted modules. Each source and primary compiled artifact is authenticated against saved successful native evidence. `evidence/native-module-bindings.json` records those bindings; `evidence/source-manifest.json` records the exact included proof sources. Original sources and full receipts remain preserved separately.

The final `Solution.lean` wrapper was freshly compiled with warnings as errors, `-M8192` and `-j1`; it succeeded in 21.125 seconds. Both selected declarations report exactly `propext`, `Classical.choice` and `Quot.sound`. Its accepted imports and source bytes were unchanged before and after the run. The fresh independent `Challenge.lean` elaboration succeeded in 10.468 seconds with its explicit proof holes permitted. It is 813 physical lines and 34,497 bytes. The hard statement limits are met; its surface exceeds the preferred smaller-statement warning thresholds.

These checks reuse authenticated unchanged proof artifacts. They do not claim that every mathematical source or Mathlib was rebuilt during release preparation. `evidence/native-final.json` records exact source/artifact identities, the saved-receipt identities and portable command spellings. `evidence/selected-axioms.log` preserves the selected output.

The saved local evidence does not include Comparator statement comparison or independent kernel replay. Those checks belong to the separate full cloud verification record.

The manuscript was rebuilt successfully with the resolved bibliography and exact-arithmetic example script. Every page of the final 18-page PDF was rendered and visually inspected. The final build has no overfull boxes or unresolved references. Blank author and affiliation fields are preserved. `evidence/manuscript.json` records the source/PDF identities and visual review; `evidence/paper-arithmetic.log` records the arithmetic check.

The manual GitHub Actions workflow runs the official Palomar verifier pinned to `7a08c1da8e0558d330b9b3c244896c175d373303`. Exact-commit cloud results are recorded in GitHub Actions, separately from the local compilation evidence above.
