module
public import proofs.JointThermoComplexity.Complexity.MonomialTraversal
public import proofs.JointThermoComplexity.Complexity.FiniteCodec

set_option autoImplicit false
@[expose] public section

/-! Dense monomial traversal consumes precisely the finite-function exponent codec in species order. -/

namespace JointThermoComplexity.Complexity.MonomialDenseCode
open MonomialTraversal FiniteCodec

theorem code_eq {n : ℕ} (γ : Fin n → ℕ) :
    code (MonomialCircuit.denseTerms γ) = functionCode natural γ := by
  rw [functionCode_eq_flatMap]
  have hm : (List.ofFn (fun i : Fin n => (i, γ i))).map Prod.snd = List.ofFn γ := by
    simp only [List.map_ofFn, Function.comp_def]
  change (List.ofFn (fun i : Fin n => (i, γ i))).flatMap (fun item => BitCodec.naturalCode item.2) =
    (List.ofFn γ).flatMap BitCodec.naturalCode
  rw [← hm, List.flatMap_map]

theorem count_eq {n : ℕ} (γ : Fin n → ℕ) : (MonomialCircuit.denseTerms γ).length = n := List.length_ofFn

theorem index_eq {n arity : ℕ} (γ : Fin n → ℕ) (inputs : Fin n → Fin arity)
    (hidx : ∀ j, (inputs j).val = j.val) :
    ∀ i (hi : i < (MonomialCircuit.denseTerms γ).length),
      (inputs (MonomialCircuit.denseTerms γ)[i].1).val = i := by
  intro i hi
  simp only [MonomialCircuit.denseTerms, List.getElem_ofFn, hidx]

theorem bits_bound {n L : ℕ} (γ : Fin n → ℕ) (h : ∀ i, (γ i).bits.length ≤ L) :
    ∀ item ∈ MonomialCircuit.denseTerms γ, item.2.bits.length ≤ L := by
  intro item hi
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
  exact h i

end JointThermoComplexity.Complexity.MonomialDenseCode

#print axioms JointThermoComplexity.Complexity.MonomialDenseCode.code_eq
