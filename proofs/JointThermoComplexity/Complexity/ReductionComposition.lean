module
public import proofs.JointThermoComplexity.Complexity.RealComplexity
public import proofs.Complexitylib.Classes.P.Composition
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.CopyOutput

set_option autoImplicit false
@[expose] public section

/-!
# Composition of binary polynomial reductions and promise hardness

The machine-runtime composition theorem is proved in the adopted Complexitylib
closure. These results use that theorem directly, with no assumed composition
principle. The final hardness lemma still requires an actual polynomial-time
map from the independently encoded ETR language; it does not supply a chemical
hardness theorem or a degree-restricted hard source.
-/

namespace JointThermoComplexity.Complexity.RealComplexity

/-- The linear identity argument is adapted from Samuel Schlesinger's
Apache-2.0 Complexitylib `Classes/P.lean`, with its source pin and license
preserved in the adoption records and third-party attribution. -/
theorem identity_mem_FP : (id : List Bool → List Bool) ∈ _root_.Complexity.FP := by
  refine ⟨1, 0, _root_.Complexity.TM.copyInputToOutputTM, (fun n => n + 2), ?_, ?_⟩
  · exact _root_.Complexity.TM.copyInputToOutputTM_computesInTime 0
  · have hn : _root_.Complexity.BigO (fun n : ℕ => n) (fun n => n ^ 1) := by
      simpa only [pow_one] using _root_.Complexity.BigO.refl (fun n : ℕ => n)
    exact _root_.Complexity.BigO.add hn (_root_.Complexity.BigO.const_le_pow 2 1)

theorem PolyReduces.refl (L : BitLanguage) : PolyReduces L L :=
  ⟨id, identity_mem_FP, fun _ => Iff.rfl⟩

theorem ETR_mem_ExistsR : ExistsR RealSyntax.ETR := PolyReduces.refl RealSyntax.ETR

theorem PolyReduces.trans {L K J : BitLanguage}
    (hLK : PolyReduces L K) (hKJ : PolyReduces K J) : PolyReduces L J := by
  obtain ⟨f, hf, hfv⟩ := hLK
  obtain ⟨g, hg, hgv⟩ := hKJ
  refine ⟨g ∘ f, _root_.Complexity.mem_FP_comp hf hg, ?_⟩
  intro input
  exact (hfv input).trans (hgv (f input))

theorem ExistsR.of_polyReduces {L K : BitLanguage}
    (hLK : PolyReduces L K) (hK : ExistsR K) : ExistsR L :=
  hLK.trans hK

/-- Precomposition preserves both the YES and NO sides of a promise reduction. -/
theorem PolyReducesToPromise.precompose {L K : BitLanguage} {P : PromiseProblem}
    (hLK : PolyReduces L K) (hKP : PolyReducesToPromise K P) :
    PolyReducesToPromise L P := by
  obtain ⟨f, hf, hfv⟩ := hLK
  obtain ⟨g, hg, hyes, hno⟩ := hKP
  refine ⟨g ∘ f, _root_.Complexity.mem_FP_comp hf hg, ?_, ?_⟩
  · intro input hi
    exact hyes (f input) ((hfv input).mp hi)
  · intro input hi
    exact hno (f input) (fun hk => hi ((hfv input).mpr hk))

/-- A concrete ETR-to-promise transducer establishes universal class hardness.
Its existence and runtime must be proved for the intended target separately. -/
theorem hard_of_ETR_reduction {P : PromiseProblem}
    (h : PolyReducesToPromise RealSyntax.ETR P) : P.Hard := by
  intro L hL
  exact PolyReducesToPromise.precompose hL h

theorem hard_iff_ETR_reduction (P : PromiseProblem) :
    P.Hard ↔ PolyReducesToPromise RealSyntax.ETR P :=
  ⟨fun h => h RealSyntax.ETR ETR_mem_ExistsR, hard_of_ETR_reduction⟩

end JointThermoComplexity.Complexity.RealComplexity

#print axioms Complexity.mem_FP_comp
#print axioms JointThermoComplexity.Complexity.RealComplexity.ETR_mem_ExistsR
#print axioms JointThermoComplexity.Complexity.RealComplexity.PolyReduces.trans
#print axioms JointThermoComplexity.Complexity.RealComplexity.PolyReducesToPromise.precompose
#print axioms JointThermoComplexity.Complexity.RealComplexity.hard_of_ETR_reduction
#print axioms JointThermoComplexity.Complexity.RealComplexity.hard_iff_ETR_reduction
