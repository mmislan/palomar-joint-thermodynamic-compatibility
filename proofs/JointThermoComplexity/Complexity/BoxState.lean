module
public import proofs.JointThermoComplexity.Complexity.BoxBufferState
public import proofs.JointThermoComplexity.Complexity.ActivityState
public import proofs.JointThermoComplexity.Complexity.ReactionPorts

set_option autoImplicit false
@[expose] public section

/-! A minimal box-loop state lets metadata live on a restored fuel view instead of a moving physical head. -/

namespace JointThermoComplexity.Complexity.BoxState
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts BoxBufferState

def Buffers (m L : ℕ) (work : Fin (m + 15) → Tape) : Prop :=
  Reusable L (work (next (m + 2))) ∧ Reusable L (work (accumulator (m + 2))) ∧
    Reusable L (work (power (m + 2))) ∧ Reusable L (work (saved m))

def Ready (m L idx : ℕ) (R : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    IsReg idx (work (species (m + 1))) ∧ Buffers m L work ∧ R work

def Unchanged (m : ℕ) (work work' : Fin (m + 15) → Tape) : Prop :=
  ∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) → j ≠ power (m + 2) → j ≠ saved m →
    j ≠ species (m + 1) → work' j = work j

structure Separate (m : ℕ) (r : Fin (m + 15)) : Prop where
  source : r ≠ species (m + 1)
  zero : r ≠ scratch (m + 2)
  loNum : r ≠ next (m + 2)
  loDen : r ≠ accumulator (m + 2)
  hiNum : r ≠ power (m + 2)
  hiDen : r ≠ saved m

theorem replace (m L idx : ℕ) (R S : (Fin (m + 15) → Tape) → Prop) (r : Fin (m + 15))
    (sep : Separate m r) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ r → work' j = work j) (ht : Parked (work' r))
    (hr : R work → S work') (h : Ready m L idx R work) : Ready m L idx S work' := by
  rcases h with ⟨hs, hz, hi, ⟨hln, hld, hhn, hhd⟩, hp⟩
  exact ⟨MonomialRestore.safe_replace r work work' hw hs ht,
    by simpa only [hw _ sep.zero.symm] using hz,
    by simpa only [hw _ sep.source.symm] using hi,
    ⟨by simpa only [hw _ sep.loNum.symm] using hln,
      by simpa only [hw _ sep.loDen.symm] using hld,
      by simpa only [hw _ sep.hiNum.symm] using hhn,
      by simpa only [hw _ sep.hiDen.symm] using hhd⟩, hr hp⟩

end JointThermoComplexity.Complexity.BoxState

#print axioms JointThermoComplexity.Complexity.BoxState.replace
