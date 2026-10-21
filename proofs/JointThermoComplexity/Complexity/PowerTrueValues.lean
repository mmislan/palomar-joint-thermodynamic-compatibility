module
public import proofs.JointThermoComplexity.Complexity.PowerPorts

set_option autoImplicit false
@[expose] public section

/-! Typed intermediate register addresses after the first gate of a true exponent bit. -/

namespace JointThermoComplexity.Complexity.PowerTrueValues
open PowerPorts

variable {arity : ℕ}

def afterFirst (m : ℕ) (values : Fin (m + 13) → Fin arity)
    (room : (values (next m)).val + 1 < arity) : Fin (m + 13) → Fin arity :=
  Function.update (Function.update values (next m) ⟨(values (next m)).val + 1, room⟩)
    (accumulator m) (values (next m))

theorem next_value (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity) :
    afterFirst m values room (next m) = ⟨(values (next m)).val + 1, room⟩ := by
  simp only [afterFirst, Function.update_of_ne (next_ne_accumulator m), Function.update_self]

theorem accumulator_value (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity) :
    afterFirst m values room (accumulator m) = values (next m) := by
  simp only [afterFirst, Function.update_self]

theorem power_value (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity) :
    afterFirst m values room (power m) = values (power m) := by
  simp only [afterFirst, Function.update_of_ne (accumulator_ne_power m).symm,
    Function.update_of_ne (next_ne_power m).symm]

end JointThermoComplexity.Complexity.PowerTrueValues

#print axioms JointThermoComplexity.Complexity.PowerTrueValues.power_value
