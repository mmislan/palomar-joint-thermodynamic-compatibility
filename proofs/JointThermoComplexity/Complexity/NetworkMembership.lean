module
public import proofs.JointThermoComplexity.Complexity.NetworkCircuit
public import proofs.JointThermoComplexity.Complexity.NetworkFormula

set_option autoImplicit false
@[expose] public section

/-!
# Total supplied-motif feasibility as an existential-real formula

All activity, current and auxiliary variables belong to one finite assignment.
The generated integer formula is satisfiable exactly when the literal network
is feasible. The executable circuit uses repeated squaring for binary exponents.
This module proves semantic equivalence, not a polynomial machine-runtime bound
or an unconditional complexity-class membership theorem.
-/

namespace JointThermoComplexity.Complexity.NetworkMembership
open RealSyntax RealCircuit NetworkData NetworkFormula

variable {n r c : ℕ}

abbrev gates (Q : Network n r c) : ℕ := (NetworkCircuit.dense Q.reactions).size

abbrev arity (Q : Network n r c) : ℕ := (n + r) + gates Q

def activityIndex (Q : Network n r c) (s : Fin n) : Fin (arity Q) :=
  Fin.castAdd (gates Q) (Fin.castAdd r s)

def currentIndex (Q : Network n r c) (i : Fin r) : Fin (arity Q) :=
  Fin.castAdd (gates Q) (Fin.natAdd n i)

def auxiliaryIndex (Q : Network n r c) (g : Fin (gates Q)) : Fin (arity Q) :=
  Fin.natAdd (n + r) g

def circuitFormula (Q : Network n r c) : Formula (arity Q) :=
  (NetworkCircuit.dense Q.reactions).circuit.formula (activityIndex Q) (auxiliaryIndex Q)

def equationsFormula (Q : Network n r c) : Formula (arity Q) :=
  allFin (fun i => .eq
    (.mul (.int (Q.reactions i).denominator) (.var (currentIndex Q i)))
    (.var (auxiliaryIndex Q (NetworkCircuit.output Q.reactions i))))

def formula (Q : Network n r c) : Formula (arity Q) :=
  .conj (circuitFormula Q)
    (.conj (equationsFormula Q)
      (constraintsFormula Q (activityIndex Q) (currentIndex Q)))

theorem equations_eval_iff (Q : Network n r c) (η : Fin (arity Q) → ℝ)
    (hc : (circuitFormula Q).eval η) :
    (equationsFormula Q).eval η ↔
      Q.CurrentEquations (fun s => η (activityIndex Q s))
        (fun i => η (currentIndex Q i)) := by
  have hv := (NetworkCircuit.dense Q.reactions).circuit.formula_forces_values
    (activityIndex Q) (auxiliaryIndex Q) η hc
  have ho (i : Fin r) :
      η (auxiliaryIndex Q (NetworkCircuit.output Q.reactions i)) =
        NetworkCircuit.numeratorValue (Q.reactions i) (fun s => η (activityIndex Q s)) :=
    (congrFun hv (NetworkCircuit.output Q.reactions i)).trans
      (NetworkCircuit.output_value Q.reactions i (fun s => η (activityIndex Q s)))
  simp only [equationsFormula, eval_allFin, Formula.eval, Term.eval, Int.cast_natCast]
  change (∀ i, ((Q.reactions i).denominator : ℝ) * η (currentIndex Q i) =
    η (auxiliaryIndex Q (NetworkCircuit.output Q.reactions i))) ↔
    ∀ i, ((Q.reactions i).denominator : ℝ) * η (currentIndex Q i) =
      NetworkCircuit.numeratorValue (Q.reactions i) (fun s => η (activityIndex Q s))
  simp only [ho]

theorem formula_sound (Q : Network n r c) (η : Fin (arity Q) → ℝ)
    (h : (formula Q).eval η) : Q.Feasible := by
  change (circuitFormula Q).eval η ∧ (equationsFormula Q).eval η ∧
    (constraintsFormula Q (activityIndex Q) (currentIndex Q)).eval η at h
  apply Q.exists_currents_iff.mp
  exact ⟨_, _, (equations_eval_iff Q η h.1).mp h.2.1,
    (eval_constraintsFormula Q _ _ η).mp h.2.2⟩

theorem formula_complete (Q : Network n r c) (h : Q.Feasible) :
    ∃ η, (formula Q).eval η := by
  obtain ⟨z, hz⟩ := h
  let j : Fin r → ℝ := fun i => (Q.reactions i).current z
  let η : Fin (arity Q) → ℝ :=
    Fin.addCases (Fin.addCases z j) ((NetworkCircuit.dense Q.reactions).circuit.eval z)
  have hηz : (fun s => η (activityIndex Q s)) = z := by
    funext s
    simp [η, activityIndex]
  have hηj : (fun i => η (currentIndex Q i)) = j := by
    funext i
    simp [η, currentIndex]
  have hηg : (fun g => η (auxiliaryIndex Q g)) =
      (NetworkCircuit.dense Q.reactions).circuit.eval z := by
    funext g
    simp [η, auxiliaryIndex]
  have hc : (circuitFormula Q).eval η := by
    apply (Circuit.formula_eval_iff _ _ _ η).mpr
    rw [hηz, hηg]
    exact Circuit.satisfies_eval _ z
  refine ⟨η, ?_⟩
  change (circuitFormula Q).eval η ∧ (equationsFormula Q).eval η ∧
    (constraintsFormula Q (activityIndex Q) (currentIndex Q)).eval η
  refine ⟨hc, (equations_eval_iff Q η hc).mpr ?_,
    (eval_constraintsFormula Q _ _ η).mpr ?_⟩
  · rw [hηz, hηj]
    exact (Q.currentEquations_iff z j).mpr rfl
  · simpa only [hηz, hηj] using hz

def sentence (Q : Network n r c) : Sentence := ⟨arity Q, formula Q⟩

theorem sentence_satisfiable_iff (Q : Network n r c) :
    (sentence Q).Satisfiable ↔ Q.Feasible :=
  ⟨fun ⟨η, h⟩ => formula_sound Q η h, formula_complete Q⟩

theorem code_mem_ETR_iff (Q : Network n r c) :
    (sentence Q).code ∈ ETR ↔ Q.Feasible :=
  (RealSyntax.code_mem_ETR_iff (sentence Q)).trans (sentence_satisfiable_iff Q)

theorem gates_le (Q : Network n r c) :
    gates Q ≤ NetworkCircuit.gateCost (List.ofFn Q.reactions) :=
  NetworkCircuit.build_size_le _

end JointThermoComplexity.Complexity.NetworkMembership

#print axioms JointThermoComplexity.Complexity.NetworkMembership.sentence_satisfiable_iff
#print axioms JointThermoComplexity.Complexity.NetworkMembership.code_mem_ETR_iff
#print axioms JointThermoComplexity.Complexity.NetworkMembership.gates_le
