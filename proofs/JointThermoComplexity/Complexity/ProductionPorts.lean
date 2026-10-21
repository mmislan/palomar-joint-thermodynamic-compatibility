module
public import proofs.JointThermoComplexity.Complexity.ReactionOperandsLoad
public import proofs.JointThermoComplexity.Complexity.BinarySignedOutput
public import proofs.JointThermoComplexity.Complexity.BoxBufferPorts
public import proofs.JointThermoComplexity.Complexity.FreshArity

set_option autoImplicit false
@[expose] public section

/-! Fixed arithmetic and loop ports in the existing family instantiated with five reserved work tapes. -/

namespace JointThermoComplexity.Complexity.ProductionPorts
open _root_.Complexity
open _root_.Complexity.TM

def leftOld (m : ℕ) : Fin (m + 19) := ⟨9, by omega⟩
def rightOld (m : ℕ) : Fin (m + 19) := ⟨10, by omega⟩
def signOld (m : ℕ) : Fin (m + 19) := ⟨11, by omega⟩
def left (m : ℕ) : Fin (m + 20) := (leftOld m).castSucc
def right (m : ℕ) : Fin (m + 20) := (rightOld m).castSucc
def sign (m : ℕ) : Fin (m + 20) := (signOld m).castSucc
def magnitude (m : ℕ) : Fin (m + 20) := BoxBufferPorts.hiDen (m + 5)
def species (m : ℕ) : Fin (m + 20) := ⟨12, by omega⟩
def core (m : ℕ) : Fin (m + 20) := ⟨13, by omega⟩
def reaction (m : ℕ) : Fin (m + 20) := MonomialPorts.previous (m + 6)
def current (m : ℕ) : Fin (m + 20) := MonomialPorts.species (m + 6)
def count (m : ℕ) : Fin (m + 20) := MonomialFuel.slot (m + 6)

theorem operand_separate (m : ℕ) : ReactionOperandsLoad.Separate (left m) (right m) (count m) (reaction m) (species m) := by
  constructor
  · intro h; have hv := congrArg Fin.val h; change (9 : ℕ) = 10 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 15 = 9 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 15 = 10 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 9 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 10 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (12 : ℕ) = 9 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (12 : ℕ) = 10 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 15 = 6 at hv; omega

theorem arithmetic_separate (m : ℕ) : BinaryDifferenceCursor.Separate (leftOld m) (rightOld m) (signOld m) := by
  constructor
  · intro h; have hv := congrArg Fin.val h; change (9 : ℕ) = 10 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (11 : ℕ) = 9 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (11 : ℕ) = 10 at hv; omega

def permutation (m : ℕ) : Fin (m + 20) ≃ Fin (m + 20) := Equiv.swap (Fin.last (m + 19)) (magnitude m)

theorem magnitude_route (m : ℕ) : permutation m (Fin.last (m + 19)) = magnitude m := Equiv.swap_apply_left _ _

theorem left_route (m : ℕ) : permutation m (leftOld m).castSucc = left m := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; have hv := congrArg Fin.val h; change (9 : ℕ) = m + 19 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (9 : ℕ) = 8 at hv; omega

theorem right_route (m : ℕ) : permutation m (rightOld m).castSucc = right m := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; have hv := congrArg Fin.val h; change (10 : ℕ) = m + 19 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (10 : ℕ) = 8 at hv; omega

theorem sign_route (m : ℕ) : permutation m (signOld m).castSucc = sign m := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; have hv := congrArg Fin.val h; change (11 : ℕ) = m + 19 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (11 : ℕ) = 8 at hv; omega

theorem reserved_blank (m : ℕ) (work : Fin (m + 20) → Tape) (h : FreshArity.Spare (m + 12) work)
    (j : Fin (m + 20)) (hlo : 9 ≤ j.val) (hhi : j.val ≤ 13) : work j = DimensionEntry.blankRegister := by
  let i : Fin (m + 14) := ⟨j.val, by omega⟩
  have he : (NetworkParserFree.port (m + 14) i).castSucc = j := by apply Fin.ext; rfl
  rw [← he]
  exact h i (by change 2 ≤ j.val; omega)

end JointThermoComplexity.Complexity.ProductionPorts

#print axioms JointThermoComplexity.Complexity.ProductionPorts.operand_separate
#print axioms JointThermoComplexity.Complexity.ProductionPorts.reserved_blank
