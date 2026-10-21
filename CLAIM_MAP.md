# Claim map

The submission selects exactly these two declarations:

- `JointThermoComplexity.Complexity.ChemicalCompleteness.boxed_complete`
- `JointThermoComplexity.Complexity.ChemicalCompleteness.unboxed_complete`

Each proves `.Complete` for the corresponding explicitly encoded `ChemicalPromiseProblem.problem`. Completeness combines an existential-real separating language with an actual polynomial-time binary Turing many-one reduction from existential-real satisfiability. The mathematical definitions and computational model are stated independently in `Challenge.lean`; `Solution.lean` imports proved implementations.

| Claim | Proved declaration or definition | Scope |
| --- | --- | --- |
| Boxed and unboxed full classifications | `ChemicalCompleteness.boxed_complete`, `unboxed_complete` | Selected statements |
| Actual binary Turing polynomial time | `ChemicalCompleteness.reduction_mem_FP` | Composed executable source and network transducers |
| Both source verdicts preserve the promise | `ChemicalCompleteness.etr_reduction`, `yes_of_source`, `no_of_source`, `output_domain` | Includes malformed source strings in the NO side |
| Exactly two signed PACs, factors in `(0,2]`, boxes and side molecularity | `ChemicalPromiseProblem.Domain`, `RationalPolynomialPromise.domain`, `RationalLiteralMolecularity.normalized_bounds` | Both YES and NO outputs; boxed internal `[1/4,1/2]`, external `[1/2,1]`, molecularity six; unboxed molecularity eight |
| Total supplied-motif feasibility belongs to existential-real complexity | `NetworkFormulaFP.totalFeasibility_mem_ExistsR` | Uses circuits for binary exponents, without PAC-recognition claims |
| Promise membership | `ChemicalPromiseMembership.member` | Total feasibility separates the promised YES and NO sets |
| Exact complete network serialization | `DenseCanonicalNetwork.word_code`, `DenseNetworkFP.word_mem_FP` | Includes literal complexes, all rational factors, supplied motifs, directions and interval fields |
| Strict-positivity source hardness | `StrictSourceHardness.etr_reduction` | Proved reduction from the independently encoded real-formula language, without a source-hardness axiom |
| Original arbitrary-real-polynomial semantic interfaces | `JointThermoComplexity.Emitted.full_boxed_reduction`, `full_unboxed_reduction` | Preserved support-based interfaces; separate from the executable ordered-list transducer |
| Additional original consequences | `JointThermoComplexity.Emitted.family_multiPAC`, `compatible_union_production`, `boxed_barriers_le_two`, `unboxed_barriers_le_two` | Preserved proved interfaces; selected final kernel targets remain the two full classifications |

Unless written in full, computational declarations in this table use namespace `JointThermoComplexity.Complexity`. The original six interfaces retain namespace `JointThermoComplexity.Emitted`.

The executable representation preserves repeated terms, zero coefficients and repeated variable occurrences. Its polynomial semantics and complete emitted bit string are proved to agree with the original finite coefficient-list chemical model. This does not assert graph identity with a support enumeration that drops zero terms.

The promise supplies valid signed potential autocatalytic cores. Minimality ranges over both species and reaction deletion, with arbitrary signed fluxes. Compatibility uses one global positive activity vector, fixed rational input factors, prescribed current directions and production separately in each supplied core. External catalysts have no core-production obligation. The unboxed offset is a species activity.

The manuscript's literature facts, LP arguments, annotation-recognition discussion, merged-channel refinement, mass-conserving food adapter, fixed-core-count extensions and denominator-growth family retain conventional proofs or citations. They are not additional selected Comparator targets. Section 8 of the manuscript gives the formal correspondence. The classification concerns compatibility at a state; it does not assert a dynamical stability or persistence result.
