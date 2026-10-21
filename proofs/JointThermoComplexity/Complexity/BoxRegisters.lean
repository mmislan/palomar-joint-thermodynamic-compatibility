module
public import proofs.JointThermoComplexity.Complexity.BoxState
public import proofs.JointThermoComplexity.Complexity.CurrentPorts
public import proofs.JointThermoComplexity.Complexity.ArityValue

set_option autoImplicit false
@[expose] public section

/-! Keep the bounded raw/previous registers available for later motif arithmetic while boxes reuse other work tapes. -/

namespace JointThermoComplexity.Complexity.BoxRegisters
open _root_.Complexity
open _root_.Complexity.TM
open BoxState PowerPorts MonomialPorts CurrentPorts

def State (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  IsReg (ArityValue.arity input) (work (raw m)) ∧
    ∃ old, old ≤ 4 * input.length ∧ IsReg old (work (previous (m + 1)))

theorem frame (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : Unchanged m work work') : State m input work → State m input work' := by
  have hx : ∀ j : Fin (m + 15), j.val = 6 ∨ j.val = m + 14 → work' j = work j := by
    intro j hj
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  rintro ⟨hr, ⟨old, hold, hp⟩⟩
  exact ⟨by simpa only [hx (raw m) (Or.inr rfl)] using hr,
    ⟨old, hold, by simpa only [hx (previous (m + 1)) (Or.inl rfl)] using hp⟩⟩

end JointThermoComplexity.Complexity.BoxRegisters

#print axioms JointThermoComplexity.Complexity.BoxRegisters.frame
