module
public import proofs.JointThermoComplexity.Complexity.NetworkPins
public import proofs.JointThermoComplexity.Complexity.CurrentPorts

set_option autoImplicit false
@[expose] public section

/-! Retain validation, dimensions, offset and arity while the old gate count becomes a running address tally. -/

namespace JointThermoComplexity.Complexity.CurrentPins
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MonomialPorts CurrentPorts

def Kept (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  IsReg (ArityValue.offset input) (work (CountLayout.offset (m + 7))) ∧
  IsReg (ArityValue.arity input) (work (CountLayout.binder (m + 7))) ∧
  ParserRegisters.Kept (m + 9) input (CountAppend.oldWork work)

theorem of_network (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) (h : NetworkPins.Kept m input work) :
    Kept m input work := h.2

theorem frame (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) → work' j = work j) :
    Kept m input work → Kept m input work' := by
  have hx : ∀ j : Fin (m + 15), j.val < 2 ∨ (m + 9 ≤ j.val ∧ j.val ≤ m + 12) → work' j = work j := by
    intro j hj
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = m + 14 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; omega
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

theorem counts (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 15) → Tape) (h : Kept m input work) :
    IsReg Q.speciesCount (work (MonomialFuel.slot (m + 1))) ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)) := by
  have hc := ParserRegisters.decoded_counts (m + 9) input (CountAppend.oldWork work) h.2.2 hd
  exact ⟨hc.1, hc.2.1⟩

theorem flag (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) (h : Kept m input work) :
    (work (RoutedNetworkParser.master (m + 9))).read = Γ.ofBool (NetworkInputControl.accepted input) := h.2.2.2.1

end JointThermoComplexity.Complexity.CurrentPins

#print axioms JointThermoComplexity.Complexity.CurrentPins.frame
