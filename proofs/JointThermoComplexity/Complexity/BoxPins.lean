module
public import proofs.JointThermoComplexity.Complexity.BoxState
public import proofs.JointThermoComplexity.Complexity.CurrentPins

set_option autoImplicit false
@[expose] public section

/-! Validated metadata survives all four box-buffer updates and advancement of the activity index. -/

namespace JointThermoComplexity.Complexity.BoxPins
open _root_.Complexity
open _root_.Complexity.TM
open PowerPorts MonomialPorts ReactionPorts BoxState

theorem frame (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : Unchanged m work work') : CurrentPins.Kept m input work → CurrentPins.Kept m input work' := by
  have hx : ∀ j : Fin (m + 15), j.val < 2 ∨ (m + 9 ≤ j.val ∧ j.val ≤ m + 12) → work' j = work j := by
    intro j hj
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  have ho := hx (CountLayout.offset (m + 7)) (by left; change (0 : ℕ) < 2; omega)
  have hb := hx (CountLayout.binder (m + 7)) (by left; change (1 : ℕ) < 2; omega)
  have hm := hx (RoutedNetworkParser.master (m + 9)) (by right; change m + 9 ≤ m + 9 ∧ m + 9 ≤ m + 12; omega)
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 9) i) = work (RoutedNetworkParser.count (m + 9) i) := by
    intro i
    apply hx
    right
    change m + 9 ≤ m + 9 + 1 + i.val ∧ m + 9 + 1 + i.val ≤ m + 12
    have hi := i.isLt
    omega
  intro hp
  change IsReg _ (work' (CountLayout.offset (m + 7))) ∧ IsReg _ (work' (CountLayout.binder (m + 7))) ∧
    (work' (RoutedNetworkParser.master (m + 9))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 9))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 1)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 2))
  rw [ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

end JointThermoComplexity.Complexity.BoxPins

#print axioms JointThermoComplexity.Complexity.BoxPins.frame
