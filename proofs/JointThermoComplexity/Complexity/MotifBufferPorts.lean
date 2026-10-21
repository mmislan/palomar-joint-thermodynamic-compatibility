module
public import proofs.JointThermoComplexity.Complexity.BooleanFieldAt
public import proofs.JointThermoComplexity.Complexity.BoxState
public import Mathlib.Tactic.FinCases

set_option autoImplicit false
@[expose] public section

/-! Three fixed nonmetadata buffers retain species masks, reaction masks and shared orientations. -/

namespace JointThermoComplexity.Complexity.MotifBufferPorts
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState PowerPorts MonomialPorts ReactionPorts

def buffer (m : ℕ) (k : Fin 3) : Fin (m + 15) := ⟨k.val + 2, by have hk := k.isLt; omega⟩

theorem buffer_value (m : ℕ) (k : Fin 3) : (buffer m k).val = k.val + 2 := rfl

theorem reusable (m L idx : ℕ) (k : Fin 3) (R : (Fin (m + 15) → Tape) → Prop)
    (work : Fin (m + 15) → Tape) (h : BoxState.Ready m L idx R work) : Reusable L (work (buffer m k)) := by
  fin_cases k
  · exact h.2.2.2.1.1
  · exact h.2.2.2.1.2.1
  · exact h.2.2.2.1.2.2.1

theorem frame_ready (m L idx : ℕ) (k : Fin 3) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer m k → work' j = work j) → R work → R work')
    (work work' : Fin (m + 15) → Tape) (hw : ∀ j, j ≠ buffer m k → work' j = work j)
    (hsafe : ∀ j, Parked (work' j)) (hnew : Reusable L (work' (buffer m k)))
    (h : BoxState.Ready m L idx R work) : BoxState.Ready m L idx R work' := by
  have hbuffer (j : Fin (m + 15)) (hj : Reusable L (work j)) : Reusable L (work' j) := by
    by_cases he : j = buffer m k
    · simpa only [he] using hnew
    · simpa only [hw j he] using hj
  have hscratch : scratch (m + 2) ≠ buffer m k := by
    intro he
    have hv := congrArg Fin.val he
    change 5 = k.val + 2 at hv
    have hk := k.isLt
    omega
  have hsource : species (m + 1) ≠ buffer m k := by
    intro he
    have hv := congrArg Fin.val he
    change 7 = k.val + 2 at hv
    have hk := k.isLt
    omega
  exact ⟨hsafe, by simpa only [hw _ hscratch] using h.2.1,
    by simpa only [hw _ hsource] using h.2.2.1,
    ⟨hbuffer _ h.2.2.2.1.1, hbuffer _ h.2.2.2.1.2.1,
      hbuffer _ h.2.2.2.1.2.2.1, hbuffer _ h.2.2.2.1.2.2.2⟩,
    hR work work' hw h.2.2.2.2⟩

end JointThermoComplexity.Complexity.MotifBufferPorts

#print axioms JointThermoComplexity.Complexity.MotifBufferPorts.reusable
#print axioms JointThermoComplexity.Complexity.MotifBufferPorts.frame_ready
