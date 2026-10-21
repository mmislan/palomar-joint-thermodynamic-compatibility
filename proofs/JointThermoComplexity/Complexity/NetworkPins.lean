module
public import proofs.JointThermoComplexity.Complexity.FormulaStart
public import proofs.JointThermoComplexity.Complexity.ReactionFuel

set_option autoImplicit false
@[expose] public section

/-! Gate emission preserves the actual arity, offset, validation flag and three dimension registers. -/

namespace JointThermoComplexity.Complexity.NetworkPins
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts

def Kept (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  IsReg (GateCountValue.count input) (work (CountLayout.raw (m + 7))) ∧
  IsReg (ArityValue.offset input) (work (CountLayout.offset (m + 7))) ∧
  IsReg (ArityValue.arity input) (work (CountLayout.binder (m + 7))) ∧
  ParserRegisters.Kept (m + 9) input (CountAppend.oldWork work)

def Protected (m : ℕ) (j : Fin (m + 15)) : Prop :=
  j.val < 2 ∨ (m + 9 ≤ j.val ∧ j.val ≤ m + 12) ∨ j.val = m + 14

theorem protected_frame (m : ℕ) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j)
    (j : Fin (m + 15)) (hj : Protected m j) : work' j = work j := by
  apply hw j
  · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; unfold Protected at hj; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; unfold Protected at hj; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; unfold Protected at hj; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = m + 2 + 11 at hv; unfold Protected at hj; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; unfold Protected at hj; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; unfold Protected at hj; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; unfold Protected at hj; omega

theorem frame (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) : Kept m input work → Kept m input work' := by
  have hx := protected_frame m work work' hw
  have hr := hx (CountLayout.raw (m + 7)) (by right; right; rfl)
  have ho := hx (CountLayout.offset (m + 7)) (by left; change (0 : ℕ) < 2; omega)
  have hb := hx (CountLayout.binder (m + 7)) (by left; change (1 : ℕ) < 2; omega)
  have hm := hx (RoutedNetworkParser.master (m + 9)) (by right; left; change m + 9 ≤ m + 9 ∧ m + 9 ≤ m + 12; omega)
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 9) i) = work (RoutedNetworkParser.count (m + 9) i) := by
    intro i
    apply hx
    right; left
    change m + 9 ≤ m + 9 + 1 + i.val ∧ m + 9 + 1 + i.val ≤ m + 12
    have hi := i.isLt
    omega
  intro hp
  change IsReg _ (work' (CountLayout.raw (m + 7))) ∧ IsReg _ (work' (CountLayout.offset (m + 7))) ∧
    IsReg _ (work' (CountLayout.binder (m + 7))) ∧
    (work' (RoutedNetworkParser.master (m + 9))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 9))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 1)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 2))
  rw [hr, ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

theorem counts (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 15) → Tape) (h : Kept m input work) :
    IsReg Q.speciesCount (work (MonomialFuel.slot (m + 1))) ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)) := by
  have hc := ParserRegisters.decoded_counts (m + 9) input (CountAppend.oldWork work) h.2.2.2 hd
  exact ⟨hc.1, hc.2.1⟩

end JointThermoComplexity.Complexity.NetworkPins

#print axioms JointThermoComplexity.Complexity.NetworkPins.frame
