module
public import proofs.JointThermoComplexity.Complexity.ProductionCoefficient
public import proofs.JointThermoComplexity.Complexity.ProductionStart

set_option autoImplicit false
@[expose] public section

/-! Exact production term output may use arithmetic ports and the reusable variable source/scratch; masks and loop indices survive. -/

namespace JointThermoComplexity.Complexity.ProductionTermFrame
open _root_.Complexity
open _root_.Complexity.TM
open ProductionPorts

def Unchanged (m : ℕ) (work work' : Fin (m + 20) → Tape) : Prop :=
  ∀ j, j ≠ left m → j ≠ right m → j ≠ sign m → j ≠ magnitude m →
    j ≠ current m → j ≠ PowerPorts.scratch (m + 7) → work' j = work j

theorem of_arithmetic (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ProductionFrame.Unchanged m work work') : Unchanged m work work' :=
  fun j hl hr hs hm _ _ => hw j hl hr hs hm

theorem of_variable (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ current m → j ≠ PowerPorts.scratch (m + 7) → work' j = work j) : Unchanged m work work' :=
  fun j _ _ _ _ hc hz => hw j hc hz

theorem outside (m : ℕ) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work')
    (j : Fin (m + 20)) (hj : j.val < 5 ∨ j.val = 6 ∨ 12 ≤ j.val) : work' j = work j := by
  apply hw j
  · intro he; have hv := congrArg Fin.val he; change j.val = 9 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 10 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 11 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 5 at hv; omega

theorem kept (m : ℕ) (input : List Bool) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') :
    CurrentPins.Kept (m + 5) input work → CurrentPins.Kept (m + 5) input work' := by
  have ho := outside m work work' hw (CountLayout.offset (m + 12)) (by left; change (0 : ℕ) < 5; omega)
  have hb := outside m work work' hw (CountLayout.binder (m + 12)) (by left; change (1 : ℕ) < 5; omega)
  have hm := outside m work work' hw (RoutedNetworkParser.master (m + 14)) (by right; right; change 12 ≤ m + 14; omega)
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 14) i) = work (RoutedNetworkParser.count (m + 14) i) := by
    intro i
    exact outside m work work' hw _ (by right; right; change 12 ≤ m + 14 + 1 + i.val; omega)
  intro hp
  change IsReg _ (work' (CountLayout.offset (m + 12))) ∧ IsReg _ (work' (CountLayout.binder (m + 12))) ∧
    (work' (RoutedNetworkParser.master (m + 14))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 14))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 14) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 14) 1)) ∧ IsReg _ (work' (RoutedNetworkParser.count (m + 14) 2))
  rw [ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

theorem metadata (m : ℕ) (input : List Bool) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') :
    MotifBufferMeta.State (m + 5) input work → MotifBufferMeta.State (m + 5) input work' := by
  have hraw := outside m work work' hw (CurrentPorts.raw (m + 5)) (by right; right; change 12 ≤ m + 19; omega)
  have hprev := outside m work work' hw (reaction m) (Or.inr (Or.inl rfl))
  rintro ⟨hk, hr, old, hold, hp⟩
  exact ⟨kept m input work work' hw hk, by simpa only [hraw] using hr,
    old, hold, by change IsReg old (work' (reaction m)); rw [hprev]; exact hp⟩

theorem mask_eq (m : ℕ) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') (k : Fin 3) :
    work' (MotifBufferPorts.buffer (m + 5) k) = work (MotifBufferPorts.buffer (m + 5) k) := by
  apply outside m work work' hw
  left
  change k.val + 2 < 5
  have hk := k.isLt
  omega

end JointThermoComplexity.Complexity.ProductionTermFrame

#print axioms JointThermoComplexity.Complexity.ProductionTermFrame.metadata
#print axioms JointThermoComplexity.Complexity.ProductionTermFrame.mask_eq
