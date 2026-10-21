module
public import proofs.JointThermoComplexity.Complexity.CountSumAt
public import proofs.JointThermoComplexity.Complexity.ParserRegisters
public import proofs.JointThermoComplexity.Complexity.NetworkParserFree

set_option autoImplicit false
@[expose] public section

/-! Reserve two actual spare ports for the auxiliary offset and total binder count. -/

namespace JointThermoComplexity.Complexity.CountLayout
open _root_.Complexity
open _root_.Complexity.TM

def offsetOld (m : ℕ) : Fin (m + 7) := ⟨0, by omega⟩
def binderOld (m : ℕ) : Fin (m + 7) := ⟨1, by omega⟩
def offset (m : ℕ) : Fin (m + 8) := (offsetOld m).castSucc
def binder (m : ℕ) : Fin (m + 8) := (binderOld m).castSucc
def raw (m : ℕ) : Fin (m + 8) := RoutedNetworkParser.raw (m + 2)

def offsetPermutation (m : ℕ) : Fin (m + 8) ≃ Fin (m + 8) := Equiv.swap (Fin.last (m + 7)) (offset m)
def binderPermutation (m : ℕ) : Fin (m + 8) ≃ Fin (m + 8) := Equiv.swap (Fin.last (m + 7)) (binder m)

theorem offset_ne_binder (m : ℕ) : offset m ≠ binder m := by
  intro h
  have hv := congrArg Fin.val h
  change (0 : ℕ) = 1 at hv
  omega

theorem raw_ne_offset (m : ℕ) : raw m ≠ offset m := by
  intro h
  have hv := congrArg Fin.val h
  change m + 7 = 0 at hv
  omega

theorem raw_ne_binder (m : ℕ) : raw m ≠ binder m := by
  intro h
  have hv := congrArg Fin.val h
  change m + 7 = 1 at hv
  omega

theorem count_ne_offset (m : ℕ) (j : Fin 3) : (NetworkParser.count (m + 2) j).castSucc ≠ offset m := by
  intro h
  have hv := congrArg Fin.val h
  change (m + 2 + 1) + j.val = 0 at hv
  omega

theorem offset_destination (m : ℕ) : CountSumAt.destination (offsetPermutation m) = offset m := by
  simp only [CountSumAt.destination, offsetPermutation, Equiv.swap_apply_left]

theorem binder_destination (m : ℕ) : CountSumAt.destination (binderPermutation m) = binder m := by
  simp only [CountSumAt.destination, binderPermutation, Equiv.swap_apply_left]

theorem offset_source (m : ℕ) (j : Fin 3) :
    offsetPermutation m (NetworkParser.count (m + 2) j).castSucc = RoutedNetworkParser.count (m + 2) j := by
  exact Equiv.swap_apply_of_ne_of_ne (CountOffset.cast_ne_destination _) (count_ne_offset m j)

theorem binder_gate_source (m : ℕ) : binderPermutation m (binderOld m).castSucc = raw m := by
  exact Equiv.swap_apply_right _ _

theorem binder_offset_source (m : ℕ) : binderPermutation m (offsetOld m).castSucc = offset m := by
  exact Equiv.swap_apply_of_ne_of_ne (raw_ne_offset m).symm (offset_ne_binder m)

theorem zeros (m : ℕ) (work : Fin (m + 8) → Tape)
    (h : NetworkParserFree.Free (m + 2) (CountAppend.oldWork work)) : IsReg 0 (work (offset m)) ∧ IsReg 0 (work (binder m)) := by
  have ho : work (offset m) = DimensionEntry.blankRegister := h ⟨0, by omega⟩
  have hb : work (binder m) = DimensionEntry.blankRegister := h ⟨1, by omega⟩
  exact ⟨by rw [ho]; exact DimensionEntry.blank_register, by rw [hb]; exact DimensionEntry.blank_register⟩

theorem kept_frame (m : ℕ) (input : List Bool) (target : Fin (m + 8)) (ht : target.val < 2)
    (work work' : Fin (m + 8) → Tape) (hw : ∀ j, j ≠ target → work' j = work j)
    (hk : ParserRegisters.Kept (m + 2) input (CountAppend.oldWork work)) :
    ParserRegisters.Kept (m + 2) input (CountAppend.oldWork work') := by
  have hm : RoutedNetworkParser.master (m + 2) ≠ target := by
    intro h
    have hv := congrArg Fin.val h
    simp only [RoutedNetworkParser.master, NetworkParser.master, Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hv
    omega
  have hc : ∀ j, RoutedNetworkParser.count (m + 2) j ≠ target := by
    intro j h
    have hv := congrArg Fin.val h
    simp only [RoutedNetworkParser.count, NetworkParser.count, DimensionMachine.slot, Fin.val_castSucc] at hv
    omega
  change (work' (RoutedNetworkParser.master (m + 2))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 2))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg (DimensionHeaders.species input) (work' (RoutedNetworkParser.count (m + 2) 0)) ∧
    IsReg (DimensionHeaders.reactions input) (work' (RoutedNetworkParser.count (m + 2) 1)) ∧
    IsReg (DimensionHeaders.cores input) (work' (RoutedNetworkParser.count (m + 2) 2))
  rw [hw _ hm, hw _ (hc 0), hw _ (hc 1), hw _ (hc 2)]
  exact hk

end JointThermoComplexity.Complexity.CountLayout

#print axioms JointThermoComplexity.Complexity.CountLayout.kept_frame
