module
public import proofs.JointThermoComplexity.Complexity.NetworkCodec
public import proofs.JointThermoComplexity.Complexity.NetworkFormulaSize

set_option autoImplicit false
@[expose] public section

/-!
# Gate counts and literal sizes in the actual network input length

Repeated-squaring gate cost is charged to binary exponent payloads, not exponent
values. The complete circuit uses at most three times the encoded input length
many gates. Dimensions are charged to their explicit headers. Literal bounds
also account for the signed stoichiometric subtraction performed by translation.
-/

namespace JointThermoComplexity.Complexity.InputSize
open FiniteCodec BitCodec NetworkData NetworkCodec
open scoped BigOperators

variable {α : Type} {n r c : ℕ}

theorem functionCode_entry_le (A : Codec α) (f : Fin n → α) (i : Fin n) :
    (A.code (f i)).length ≤ (functionCode A f).length := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [functionCode, List.length_append]
      omega
    · have ht := ih (fun j => f j.succ) j
      simp only [functionCode, List.length_append]
      omega

theorem functionCode_length (A : Codec α) (f : Fin n → α) :
    (functionCode A f).length = ∑ i, (A.code (f i)).length := by
  rw [functionCode_eq_flatMap]
  simp [List.length_flatMap, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem reaction_code_length (q : ReactionCircuit.Reaction n) :
    ((DataCodec.reaction n).code q).length =
      (functionCode natural q.reactant).length + (functionCode natural q.product).length +
      (naturalCode q.numerator).length + (naturalCode q.denominator).length := by
  simp only [DataCodec.reaction, DataCodec.transport, DataCodec.reactionEquiv,
    Equiv.symm, Equiv.coe_fn_mk, product, positive, finiteFunction, List.length_append]
  omega

theorem network_code_length (Q : Network n r c) :
    ((DataCodec.network n r c).code Q).length =
      (functionCode (DataCodec.reaction n) Q.reactions).length +
      (functionCode (DataCodec.motif n r) Q.motifs).length +
      (functionCode boolean Q.forward).length +
      (functionCode (optional DataCodec.box) Q.boxes).length := by
  simp only [DataCodec.network, DataCodec.transport, DataCodec.networkEquiv,
    Equiv.symm, Equiv.coe_fn_mk, product, finiteFunction, List.length_append]
  omega

theorem monomial_cost_le (items : List (Fin n × ℕ)) :
    MonomialCircuit.gateCost items ≤
      3 * (items.map (fun item => (naturalCode item.2).length)).sum := by
  induction items with
  | nil => simp [MonomialCircuit.gateCost]
  | cons item items ih =>
    simp only [MonomialCircuit.gateCost, List.map_cons, List.sum_cons,
      naturalCode_length, Nat.mul_add] at ih ⊢
    omega

theorem dense_monomial_cost_le (γ : Fin n → ℕ) :
    MonomialCircuit.gateCost (MonomialCircuit.denseTerms γ) ≤
      3 * (functionCode natural γ).length := by
  have h := monomial_cost_le (MonomialCircuit.denseTerms γ)
  simpa only [MonomialCircuit.denseTerms, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, functionCode_length, natural] using h

theorem reaction_gateCost_le (q : ReactionCircuit.Reaction n) :
    q.gateCost ≤ 3 * ((DataCodec.reaction n).code q).length := by
  have ha := dense_monomial_cost_le q.reactant
  have hb := dense_monomial_cost_le q.product
  have hp : 1 ≤ (naturalCode q.numerator).length := by rw [naturalCode_length]; omega
  have hq : 1 ≤ (naturalCode q.denominator).length := by rw [naturalCode_length]; omega
  rw [reaction_code_length]
  simp only [ReactionCircuit.Reaction.gateCost, Nat.mul_add]
  omega

theorem reactions_gateCost_le (reactions : List (ReactionCircuit.Reaction n)) :
    NetworkCircuit.gateCost reactions ≤
      3 * (reactions.map (fun q => ((DataCodec.reaction n).code q).length)).sum := by
  induction reactions with
  | nil => simp [NetworkCircuit.gateCost]
  | cons q rest ih =>
    have hq := reaction_gateCost_le q
    simp only [NetworkCircuit.gateCost, List.map_cons, List.sum_cons, Nat.mul_add]
    omega

theorem gates_le_body_length (Q : Network n r c) :
    NetworkMembership.gates Q ≤ 3 * ((DataCodec.network n r c).code Q).length := by
  have hg := NetworkMembership.gates_le Q
  have hc := reactions_gateCost_le (List.ofFn Q.reactions)
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] at hc
  rw [← functionCode_length] at hc
  rw [network_code_length]
  omega

theorem body_length_le (Q : Input) :
    ((DataCodec.network Q.speciesCount Q.reactionCount Q.coreCount).code Q.network).length ≤
      Q.code.length := by
  simp only [Input.code, List.length_append]
  omega

theorem gates_le_input_length (Q : Input) : NetworkMembership.gates Q.network ≤ 3 * Q.code.length := by
  have hg := gates_le_body_length Q.network
  have hb := body_length_le Q
  omega

theorem arity_le_input_length (Q : Input) : NetworkMembership.arity Q.network ≤ 4 * Q.code.length := by
  have hd := dimensions_le_code_length Q
  have hg := gates_le_input_length Q
  change Q.speciesCount + Q.reactionCount + NetworkMembership.gates Q.network ≤ _
  omega

theorem reaction_length_le_input (Q : Input) (i : Fin Q.reactionCount) :
    ((DataCodec.reaction Q.speciesCount).code (Q.network.reactions i)).length ≤ Q.code.length := by
  have hi := functionCode_entry_le (DataCodec.reaction Q.speciesCount) Q.network.reactions i
  have hb := body_length_le Q
  rw [network_code_length] at hb
  omega

theorem complex_entries_le_input (Q : Input) (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) :
    (naturalCode ((Q.network.reactions i).reactant s)).length ≤ Q.code.length ∧
    (naturalCode ((Q.network.reactions i).product s)).length ≤ Q.code.length := by
  have ha := functionCode_entry_le natural (Q.network.reactions i).reactant s
  have hb := functionCode_entry_le natural (Q.network.reactions i).product s
  have hr := reaction_length_le_input Q i
  change (naturalCode ((Q.network.reactions i).reactant s)).length ≤
    (functionCode natural (Q.network.reactions i).reactant).length at ha
  change (naturalCode ((Q.network.reactions i).product s)).length ≤
    (functionCode natural (Q.network.reactions i).product).length at hb
  rw [reaction_code_length] at hr
  exact ⟨by omega, by omega⟩

theorem integer_difference_length_le (a b : ℕ) :
    (integerCode ((b : ℤ) - a)).length ≤ (naturalCode a).length + (naturalCode b).length := by
  by_cases hab : a ≤ b
  · have hAbs : ((b : ℤ) - a).natAbs ≤ b := by
      rw [Int.natAbs_sub_of_nonneg_of_le (by omega) (by exact_mod_cast hab)]
      simp only [Int.natAbs_natCast]
      omega
    have hbits := Nat.size_le_size hAbs
    rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len] at hbits
    simp only [integerCode_length, naturalCode_length]
    omega
  · have hAbs : ((b : ℤ) - a).natAbs ≤ a := by
      rw [← Int.natAbs_neg, neg_sub,
        Int.natAbs_sub_of_nonneg_of_le (by omega) (by exact_mod_cast (by omega : b ≤ a))]
      simp only [Int.natAbs_natCast]
      omega
    have hbits := Nat.size_le_size hAbs
    rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len] at hbits
    simp only [integerCode_length, naturalCode_length]
    omega

theorem stoich_length_le_input (Q : Input) (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) :
    (integerCode (stoich (Q.network.reactions i) s)).length ≤ 2 * Q.code.length := by
  have hc := complex_entries_le_input Q i s
  have hdiff := integer_difference_length_le ((Q.network.reactions i).reactant s)
    ((Q.network.reactions i).product s)
  simp only [stoich]
  omega

end JointThermoComplexity.Complexity.InputSize

#print axioms JointThermoComplexity.Complexity.InputSize.gates_le_input_length
#print axioms JointThermoComplexity.Complexity.InputSize.arity_le_input_length
#print axioms JointThermoComplexity.Complexity.InputSize.stoich_length_le_input
