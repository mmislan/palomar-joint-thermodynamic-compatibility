module
public import proofs.JointThermoComplexity.Complexity.CanonicalBits

set_option autoImplicit false
@[expose] public section

/-! Little-endian carry control agrees with the existing canonical natural codec. -/

namespace JointThermoComplexity.Complexity.BinaryIncrementControl
open BitCodec CanonicalBits

def increment : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: increment rest

theorem increment_ne_nil (bits : List Bool) : increment bits ≠ [] := by
  cases bits with
  | nil => simp [increment]
  | cons bit rest => cases bit <;> simp [increment]

theorem read_increment (bits : List Bool) : readBits (increment bits) = readBits bits + 1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false => simp [increment, readBits, Nat.bit]
    | true =>
      change Nat.bit false (readBits (increment rest)) = Nat.bit true (readBits rest) + 1
      rw [ih]
      simp [Nat.bit]
      omega

theorem valid_increment (bits : List Bool) (h : validPayload bits = true) :
    validPayload (increment bits) = true := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false =>
      cases rest with
      | nil => rfl
      | cons b rest => exact h
    | true =>
      have ht : validPayload rest = true := by
        cases rest with
        | nil => rfl
        | cons b bs => exact h
      have hv := ih ht
      cases he : increment rest with
      | nil => exact (increment_ne_nil rest he).elim
      | cons b bs => simpa only [increment, he, validPayload] using hv

theorem increment_bits (n : ℕ) : increment n.bits = (n + 1).bits := by
  have h := bits_readBits_of_valid (increment n.bits) (valid_increment n.bits (valid_bits n))
  rw [read_increment, readBits_bits] at h
  exact h.symm

theorem length_increment (bits : List Bool) : (increment bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [increment]
  | cons bit rest ih =>
    cases bit with
    | false => simp [increment]
    | true => simpa only [increment, List.length_cons] using Nat.add_le_add_right ih 1

theorem bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← increment_bits]
    exact (length_increment n.bits).trans (Nat.add_le_add_right ih 1)

end JointThermoComplexity.Complexity.BinaryIncrementControl

#print axioms JointThermoComplexity.Complexity.BinaryIncrementControl.increment_bits
#print axioms JointThermoComplexity.Complexity.BinaryIncrementControl.bits_length_le
