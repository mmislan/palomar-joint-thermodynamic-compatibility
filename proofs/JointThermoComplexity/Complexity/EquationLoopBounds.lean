module
public import proofs.JointThermoComplexity.Complexity.EquationFuelFrame

set_option autoImplicit false
@[expose] public section

/-! Raw cursor conservation gives one uniform state bound throughout the emission loop. -/

namespace JointThermoComplexity.Complexity.EquationLoopBounds

def bound (arity L : ℕ) (s : PreorderEmissionControl.State) : ℕ :=
  arity + s.scan.terms + s.scan.formulas + s.scan.coordinates + s.scan.before.length + 5 * L

theorem run_succ_last (L arity i : ℕ) (s : PreorderEmissionControl.State) :
    PreorderEmissionControl.run L arity (i + 1) s =
      PreorderEmissionControl.step L arity (PreorderEmissionControl.run L arity i s) := by
  rw [PreorderEmissionControl.run_add]
  rfl

theorem current_bounds (arity L i : ℕ) (s : PreorderEmissionControl.State) (hi : i ≤ L) (hlen : s.scan.input.length ≤ L) :
    let q := PreorderEmissionControl.run L arity i s
    let N := bound arity L s
    arity ≤ N ∧ L ≤ N ∧ q.scan.terms ≤ N ∧ q.scan.formulas ≤ N ∧ q.scan.coordinates ≤ N ∧
      q.scan.before.length ≤ N ∧ q.scan.input.length ≤ L := by
  obtain ⟨ht, hf, hc, hinput, hword⟩ := FormulaSpanControl.run_bounds i s.scan
  have hw := congrArg List.length hword
  simp only [List.length_append] at hw
  simp only [PreorderEmissionControl.run_scan]
  dsimp only [bound]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, hinput.trans hlen⟩

def size (arity L : ℕ) (s : PreorderEmissionControl.State) : ℕ :=
  arity + s.scan.terms + s.scan.formulas + s.scan.coordinates + s.scan.before.length + L

theorem length_le_size (arity L : ℕ) (s : PreorderEmissionControl.State) : L ≤ size arity L s := by
  dsimp [size]
  omega

theorem bound_le_size (arity L : ℕ) (s : PreorderEmissionControl.State) : bound arity L s ≤ 5 * size arity L s := by
  dsimp [bound, size]
  omega

end JointThermoComplexity.Complexity.EquationLoopBounds

#print axioms JointThermoComplexity.Complexity.EquationLoopBounds.current_bounds
