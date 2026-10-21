module
public import proofs.JointThermoComplexity.Complexity.ProductionPorts
public import proofs.JointThermoComplexity.Complexity.MotifBufferMeta

set_option autoImplicit false
@[expose] public section

/-! Arithmetic changes only its two operands, sign and magnitude; validated metadata, masks and loop registers survive. -/

namespace JointThermoComplexity.Complexity.ProductionFrame
open _root_.Complexity
open _root_.Complexity.TM
open ProductionPorts

def Unchanged (m : ℕ) (work work' : Fin (m + 20) → Tape) : Prop :=
  ∀ j, j ≠ left m → j ≠ right m → j ≠ sign m → j ≠ magnitude m → work' j = work j

theorem outside (m : ℕ) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work')
    (j : Fin (m + 20)) (hj : j.val < 8 ∨ 12 ≤ j.val) : work' j = work j := by
  apply hw j
  · intro h; have hv := congrArg Fin.val h; change j.val = 9 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change j.val = 10 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change j.val = 11 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change j.val = 8 at hv; omega

theorem kept (m : ℕ) (input : List Bool) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') :
    CurrentPins.Kept (m + 5) input work → CurrentPins.Kept (m + 5) input work' := by
  have ho := outside m work work' hw (CountLayout.offset (m + 12)) (by left; change (0 : ℕ) < 8; omega)
  have hb := outside m work work' hw (CountLayout.binder (m + 12)) (by left; change (1 : ℕ) < 8; omega)
  have hm := outside m work work' hw (RoutedNetworkParser.master (m + 14)) (by right; change 12 ≤ m + 14; omega)
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 14) i) = work (RoutedNetworkParser.count (m + 14) i) := by
    intro i
    exact outside m work work' hw _ (by right; change 12 ≤ m + 14 + 1 + i.val; omega)
  intro hp
  change IsReg _ (work' (CountLayout.offset (m + 12))) ∧ IsReg _ (work' (CountLayout.binder (m + 12))) ∧
    (work' (RoutedNetworkParser.master (m + 14))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 14))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 14) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 14) 1)) ∧ IsReg _ (work' (RoutedNetworkParser.count (m + 14) 2))
  rw [ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

theorem registers (m : ℕ) (input : List Bool) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') :
    BoxRegisters.State (m + 5) input work → BoxRegisters.State (m + 5) input work' := by
  have hr := outside m work work' hw (CurrentPorts.raw (m + 5)) (by right; change 12 ≤ m + 19; omega)
  have hp := outside m work work' hw (MonomialPorts.previous (m + 6)) (by left; change (6 : ℕ) < 8; omega)
  rintro ⟨hraw, ⟨old, hold, hprev⟩⟩
  exact ⟨by simpa only [hr] using hraw, ⟨old, hold, by simpa only [hp] using hprev⟩⟩

theorem metadata (m : ℕ) (input : List Bool) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') :
    MotifBufferMeta.State (m + 5) input work → MotifBufferMeta.State (m + 5) input work' := by
  rintro ⟨hk, hr⟩
  exact ⟨kept m input work work' hw hk, registers m input work work' hw hr⟩

theorem mask_eq (m : ℕ) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') (k : Fin 3) :
    work' (MotifBufferPorts.buffer (m + 5) k) = work (MotifBufferPorts.buffer (m + 5) k) := by
  apply outside m work work' hw
  left
  change k.val + 2 < 8
  have hk := k.isLt
  omega

theorem indices_eq (m : ℕ) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') :
    work' (reaction m) = work (reaction m) ∧ work' (current m) = work (current m) ∧
      work' (species m) = work (species m) ∧ work' (core m) = work (core m) :=
  ⟨outside m work work' hw _ (Or.inl (by change (6 : ℕ) < 8; omega)),
    outside m work work' hw _ (Or.inl (by change (7 : ℕ) < 8; omega)),
    outside m work work' hw _ (Or.inr (by change 12 ≤ (12 : ℕ); omega)),
    outside m work work' hw _ (Or.inr (by change 12 ≤ (13 : ℕ); omega))⟩

end JointThermoComplexity.Complexity.ProductionFrame

#print axioms JointThermoComplexity.Complexity.ProductionFrame.metadata
#print axioms JointThermoComplexity.Complexity.ProductionFrame.mask_eq
