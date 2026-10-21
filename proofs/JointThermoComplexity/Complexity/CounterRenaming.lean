module
public import proofs.JointThermoComplexity.Complexity.CounterPlacement

set_option autoImplicit false
@[expose] public section

/-! Exact evaluation, untouched registers and cost under injective instruction renaming. -/

namespace JointThermoComplexity.Complexity.CounterRenaming
open DInstabilityComplexity.MachineConstruction
variable {n w : ℕ}

theorem update_comp (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (v : Fin w → ℕ) (r : Fin n) (a : ℕ) :
    (Function.update v (ports r) a) ∘ ports = Function.update (v ∘ ports) r a := by
  funext j
  by_cases hj : j = r
  · subst j
    simp only [Function.comp_apply, Function.update_self]
  · have hp := hinj.ne hj
    simp only [Function.comp_apply, Function.update_of_ne hp, Function.update_of_ne hj]

theorem instruction_eval (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (i : CounterInstruction n) (v : Fin w → ℕ) :
    (CounterPlacement.instruction ports hinj i).eval v ∘ ports = i.eval (v ∘ ports) := by
  cases i <;> exact update_comp ports hinj v _ _

theorem instruction_outside (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (i : CounterInstruction n) (v : Fin w → ℕ) (j : Fin w) (hj : ∀ k, j ≠ ports k) :
    (CounterPlacement.instruction ports hinj i).eval v j = v j := by
  cases i <;> exact Function.update_of_ne (hj _) _ _

theorem instruction_time (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (i : CounterInstruction n) (v : Fin w → ℕ) :
    (CounterPlacement.instruction ports hinj i).time v = i.time (v ∘ ports) := by
  cases i <;> rfl

def program (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (p : CounterProgram n) : CounterProgram w := p.map (CounterPlacement.instruction ports hinj)

theorem eval (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (p : CounterProgram n) (v : Fin w → ℕ) :
    counterProgramEval (program ports hinj p) v ∘ ports = counterProgramEval p (v ∘ ports) := by
  induction p generalizing v with
  | nil => rfl
  | cons i rest ih =>
    change counterProgramEval (program ports hinj rest) ((CounterPlacement.instruction ports hinj i).eval v) ∘ ports = _
    rw [ih, instruction_eval]
    rfl

theorem outside (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (p : CounterProgram n) (v : Fin w → ℕ) (j : Fin w) (hj : ∀ k, j ≠ ports k) :
    counterProgramEval (program ports hinj p) v j = v j := by
  induction p generalizing v with
  | nil => rfl
  | cons i rest ih =>
    change counterProgramEval (program ports hinj rest) ((CounterPlacement.instruction ports hinj i).eval v) j = _
    rw [ih, instruction_outside ports hinj i v j hj]

theorem time (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (p : CounterProgram n) (v : Fin w → ℕ) :
    counterProgramTime (program ports hinj p) v = counterProgramTime p (v ∘ ports) := by
  induction p generalizing v with
  | nil => rfl
  | cons i rest ih =>
    change (CounterPlacement.instruction ports hinj i).time v + 1 +
      counterProgramTime (program ports hinj rest) ((CounterPlacement.instruction ports hinj i).eval v) = _
    rw [instruction_time, ih, instruction_eval]
    rfl

end JointThermoComplexity.Complexity.CounterRenaming

#print axioms JointThermoComplexity.Complexity.CounterRenaming.eval
#print axioms JointThermoComplexity.Complexity.CounterRenaming.outside
#print axioms JointThermoComplexity.Complexity.CounterRenaming.time
