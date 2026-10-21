module
public import proofs.JointThermoComplexity.Complexity.SparseQuadraticLiftSemantics
public import proofs.JointThermoComplexity.Complexity.ScaledQuadraticSystem

set_option autoImplicit false
@[expose] public section

/-! # Executable sparse equations with one exact positive scale chain -/

namespace JointThermoComplexity.Complexity.SparseScaledSystem
open SparseInteger
variable {V A : Type}

def chain (m : ℕ) : Unit ⊕ Fin m → Poly (Fin (m + 1)) :=
  Sum.elim (fun _ => sub (scale 4 (atom 0)) (constant 1))
    (fun j => sub (atom j.succ) (square (atom j.castSucc)))

def family (q : A → Poly V) (m : ℕ) : A ⊕ (Unit ⊕ Fin m) → Poly (V ⊕ Fin (m + 1)) :=
  Sum.elim (fun j => relabel (ScaledQuadraticSystem.liftPorts m) (SparseQuadraticLift.lift (q j)))
    (fun j => relabel Sum.inr (chain m j))

theorem interpret_chain (m : ℕ) (j : Unit ⊕ Fin m) :
    interpret (chain m j) = ExactScaleChain.equation m j := by
  cases j with
  | inl u => simp only [chain, ExactScaleChain.equation, Sum.elim_inl, interpret_sub,
      interpret_scale, interpret_atom, interpret_constant, map_one]
  | inr j => simp only [chain, ExactScaleChain.equation, Sum.elim_inr, interpret_sub, interpret_atom, interpret_square]

theorem interpret_family (q : A → Poly V) (m : ℕ) (j : A ⊕ (Unit ⊕ Fin m)) :
    interpret (family q m j) = ScaledQuadraticSystem.family (fun j => interpret (q j)) m j := by
  cases j with
  | inl j => simp only [family, ScaledQuadraticSystem.family, Sum.elim_inl,
      interpret_relabel, SparseQuadraticLift.interpret_lift]
  | inr j => simp only [family, ScaledQuadraticSystem.family, Sum.elim_inr,
      interpret_relabel, interpret_chain]

private theorem degree_mono {a b : ℕ} {p : Poly V} (hab : a ≤ b) (hp : DegreeLE a p) : DegreeLE b p :=
  fun t ht => (hp t ht).trans hab

theorem chain_degree (m : ℕ) (j : Unit ⊕ Fin m) : DegreeLE 2 (chain m j) := by
  cases j with
  | inl _ =>
    exact degree_sub (degree_scale 4 (degree_mono (by decide : 1 ≤ 2) (degree_atom 0)))
      (degree_mono (by decide : 0 ≤ 2) (degree_constant 1))
  | inr j => exact degree_sub (degree_mono (by decide : 1 ≤ 2) (degree_atom j.succ)) (degree_square (degree_atom j.castSucc))

theorem family_degree (q : A → Poly V) (m : ℕ) (j : A ⊕ (Unit ⊕ Fin m)) : DegreeLE 2 (family q m j) := by
  cases j with
  | inl j => exact degree_relabel _ (SparseQuadraticLift.lift_degree (q j))
  | inr j => exact degree_relabel _ (chain_degree m j)

theorem chain_length (m : ℕ) (j : Unit ⊕ Fin m) : (chain m j).length = 2 := by
  cases j with
  | inl _ => simp [chain]
  | inr j => simp [chain, length_square]

theorem family_length (q : A → Poly V) (B : ℕ) (hB : ∀ j, (q j).length ≤ B)
    (m : ℕ) (j : A ⊕ (Unit ⊕ Fin m)) : (family q m j).length ≤ max B 2 := by
  cases j with
  | inl j =>
    change (relabel (ScaledQuadraticSystem.liftPorts m) (SparseQuadraticLift.lift (q j))).length ≤ _
    rw [length_relabel]
    exact (SparseQuadraticLift.lift_length (q j)).trans ((hB j).trans (Nat.le_max_left _ _))
  | inr j =>
    change (relabel (Sum.inr : Fin (m + 1) → V ⊕ Fin (m + 1)) (chain m j)).length ≤ _
    rw [length_relabel, chain_length]
    exact Nat.le_max_right _ _

theorem common_root_iff (q : A → Poly V) (hq : ∀ j, (interpret (q j)).totalDegree ≤ 2) (m : ℕ) :
    (∃ v, ∀ j, (interpret (family q m j)).eval₂ (Int.castRingHom ℝ) v = 0) ↔
      ∃ x, ∀ j, (interpret (q j)).eval₂ (Int.castRingHom ℝ) x = 0 := by
  simp only [interpret_family]
  exact ScaledQuadraticSystem.common_root_iff (fun j => interpret (q j)) hq m

end JointThermoComplexity.Complexity.SparseScaledSystem

#print axioms JointThermoComplexity.Complexity.SparseScaledSystem.family
#print axioms JointThermoComplexity.Complexity.SparseScaledSystem.interpret_family
#print axioms JointThermoComplexity.Complexity.SparseScaledSystem.family_degree
#print axioms JointThermoComplexity.Complexity.SparseScaledSystem.family_length
#print axioms JointThermoComplexity.Complexity.SparseScaledSystem.common_root_iff
