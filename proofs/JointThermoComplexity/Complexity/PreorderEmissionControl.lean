module
public import proofs.JointThermoComplexity.Complexity.PreorderLocalRows

set_option autoImplicit false
@[expose] public section

/-! Bounded forward row emission. Term-mode addresses discount the three witness slots reserved early. -/

namespace JointThermoComplexity.Complexity.PreorderEmissionControl
open RealSyntax PreorderLocalRows

structure State where
  scan : FormulaSpanControl.State
  emitted : Rows

def address (arity : ℕ) (s : FormulaSpanControl.State) : ℕ :=
  arity + match s.terms with
    | 0 => s.coordinates
    | _ + 1 => s.coordinates - 3

def localRows (L arity : ℕ) (s : FormulaSpanControl.State) : Rows := match s.terms, s.formulas with
  | 0, 0 => []
  | 0, _ + 1 => formulaRows L (address arity s) s.input
  | _ + 1, _ => termRows L (address arity s) s.input

def step (L arity : ℕ) (s : State) : State := ⟨FormulaSpanControl.step s.scan, s.emitted ++ localRows L arity s.scan⟩
def run (L arity : ℕ) : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => run L arity fuel (step L arity s)

theorem run_add (L arity a b : ℕ) (s : State) : run L arity (a + b) s = run L arity b (run L arity a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (step L arity s)

theorem run_scan (L arity fuel : ℕ) (s : State) : (run L arity fuel s).scan = FormulaSpanControl.run fuel s.scan := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => exact ih (step L arity s)

@[simp] theorem step_finished (L arity : ℕ) (before input : List Bool) (coordinates : ℕ) (rows : Rows) :
    step L arity ⟨⟨before, input, 0, 0, coordinates⟩, rows⟩ = ⟨⟨before, input, 0, 0, coordinates⟩, rows⟩ := by
  simp only [step, localRows, FormulaSpanControl.step_finished, List.append_nil]

@[simp] theorem run_finished (L arity fuel : ℕ) (before input : List Bool) (coordinates : ℕ) (rows : Rows) :
    run L arity fuel ⟨⟨before, input, 0, 0, coordinates⟩, rows⟩ = ⟨⟨before, input, 0, 0, coordinates⟩, rows⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step_finished] using ih

theorem term_address (arity v formulas offset : ℕ) (before input : List Bool) :
    address arity ⟨before, input, v + 1, formulas, offset + 3⟩ = arity + offset := by
  simp only [address, Nat.add_sub_cancel_right]

theorem formula_step {n : ℕ} (L forms offset : ℕ) (p : Formula n) (before suffix : List Bool) (rows : Rows)
    (hlen : (p.code ++ suffix).length ≤ L) :
    step L n ⟨⟨before, p.code ++ suffix, 0, forms + 1, offset⟩, rows⟩ =
      ⟨FormulaSpanControl.formulaStep forms ⟨before, p.code ++ suffix, 0, forms + 1, offset⟩,
        rows ++ words (formulaLocal p (n + offset))⟩ := by
  simp only [step, localRows, address, FormulaSpanControl.step]
  rw [PreorderLocalRows.formula_code L (n + offset) p suffix hlen]

end JointThermoComplexity.Complexity.PreorderEmissionControl

#print axioms JointThermoComplexity.Complexity.PreorderEmissionControl.run_scan
#print axioms JointThermoComplexity.Complexity.PreorderEmissionControl.term_address
#print axioms JointThermoComplexity.Complexity.PreorderEmissionControl.formula_step
