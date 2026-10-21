module
public import proofs.JointThermoComplexity.Complexity.OuterFuelFreshEntry
public import proofs.JointThermoComplexity.Complexity.ProductionReactionState
public import proofs.JointThermoComplexity.Complexity.MotifPassFrame

set_option autoImplicit false
@[expose] public section

/-! Initialized copied outer-loop counts survive motif preparation and complete inner production work. -/

namespace JointThermoComplexity.Complexity.OuterFuelRegisters
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt OuterFuelPorts

def State (m n c : ℕ) (work : Fin (m + 22) → Tape) : Prop :=
  IsReg n (work (destination m 0)) ∧ IsReg c (work (destination m 1))

theorem of_advanced (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 22) → Tape) (h : OuterFuelFreshEntry.Advanced m input work) : State m Q.speciesCount Q.coreCount work := by
  have h' : MotifPreparedMasks.Ready (m + 7) input Q work ∧ ProductionBank.State (m + 2) work ∧
      IsReg Q.speciesCount (work (destination m 0)) ∧ IsReg Q.coreCount (work (destination m 1)) := by
    simpa only [OuterFuelFreshEntry.Advanced, hd] using h
  exact h'.2.2

theorem motif_frame (m n c : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : MotifPassFrame.Unchanged (m + 7) work work') : State m n c work → State m n c work' := by
  have hx (k : Fin 2) : work' (destination m k) = work (destination m k) :=
    MotifPassFrame.outside (m + 7) work work' hw _ (Or.inr (by change 8 ≤ 14 + k.val; omega))
  rintro ⟨hn, hc⟩
  exact ⟨by simpa only [hx 0] using hn, by simpa only [hx 1] using hc⟩

theorem production_outside (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ProductionReactionState.Unchanged (m + 2) work work') (j : Fin (m + 22)) (hj : 12 ≤ j.val) : work' j = work j := by
  apply hw j
  · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 5 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 9 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 10 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 11 at hv; omega

theorem production_frame (m n c : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ProductionReactionState.Unchanged (m + 2) work work') : State m n c work → State m n c work' := by
  have hx (k : Fin 2) : work' (destination m k) = work (destination m k) :=
    production_outside m work work' hw _ (by change 12 ≤ 14 + k.val; omega)
  rintro ⟨hn, hc⟩
  exact ⟨by simpa only [hx 0] using hn, by simpa only [hx 1] using hc⟩

theorem start_frame (m n c : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ ProductionPorts.reaction (m + 2) → j ≠ ProductionPorts.current (m + 2) → work' j = work j) :
    State m n c work → State m n c work' := by
  have hx (k : Fin 2) : work' (destination m k) = work (destination m k) := by
    apply hw
    · intro he; have hv := congrArg Fin.val he; change 14 + k.val = 6 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change 14 + k.val = 7 at hv; omega
  rintro ⟨hn, hc⟩
  exact ⟨by simpa only [hx 0] using hn, by simpa only [hx 1] using hc⟩

end JointThermoComplexity.Complexity.OuterFuelRegisters

#print axioms JointThermoComplexity.Complexity.OuterFuelRegisters.of_advanced
#print axioms JointThermoComplexity.Complexity.OuterFuelRegisters.motif_frame
#print axioms JointThermoComplexity.Complexity.OuterFuelRegisters.production_frame
#print axioms JointThermoComplexity.Complexity.OuterFuelRegisters.start_frame
