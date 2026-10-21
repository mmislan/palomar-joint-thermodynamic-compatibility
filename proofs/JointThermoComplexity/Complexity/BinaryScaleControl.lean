module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementControl
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! Small-carry control for multiplying a little-endian binary word by a fixed
natural constant. The carry stays at most that constant, independently of the
numeric magnitude of the input word. -/

namespace JointThermoComplexity.Complexity.BinaryScaleControl
open BitCodec

def total (k carry : ℕ) (b : Bool) : ℕ := carry + if b then k else 0
def next (k carry : ℕ) (b : Bool) : ℕ := total k carry b / 2
def digit (k carry : ℕ) (b : Bool) : Bool := decide (total k carry b % 2 = 1)

def scale (k : ℕ) : ℕ → List Bool → List Bool
  | carry, [] => carry.bits
  | carry, b :: rest => digit k carry b :: scale k (next k carry b) rest

theorem digit_value (x tail : ℕ) : Nat.bit (decide (x % 2 = 1)) tail = x % 2 + 2 * tail := by
  have hm : x % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hx : x % 2 = 1 <;> simp [hx, Nat.bit] <;> omega

theorem next_le (k carry : ℕ) (b : Bool) (hc : carry ≤ k) : next k carry b ≤ k := by
  cases b <;> simp [next, total] <;> omega

theorem read_scale (k carry : ℕ) (bits : List Bool) :
    readBits (scale k carry bits) = carry + k * readBits bits := by
  induction bits generalizing carry with
  | nil =>
    change readBits carry.bits = carry + k * 0
    rw [readBits_bits]
    omega
  | cons b rest ih =>
    change Nat.bit (digit k carry b) (readBits (scale k (next k carry b) rest)) =
      carry + k * Nat.bit b (readBits rest)
    unfold digit
    rw [digit_value, ih]
    unfold next
    calc
      _ = (total k carry b % 2 + 2 * (total k carry b / 2)) + k * (2 * readBits rest) := by ring
      _ = total k carry b + k * (2 * readBits rest) := by rw [Nat.mod_add_div]
      _ = carry + k * Nat.bit b (readBits rest) := by
        cases b
        · simp [total, Nat.bit]
        · simp [total, Nat.bit]
          ring

theorem length_scale (k carry : ℕ) (bits : List Bool) (hc : carry ≤ k) :
    (scale k carry bits).length ≤ bits.length + k := by
  induction bits generalizing carry with
  | nil => simpa only [scale, List.length_nil, Nat.zero_add] using (BinaryIncrementControl.bits_length_le carry).trans hc
  | cons b rest ih =>
    have h := ih (next k carry b) (next_le k carry b hc)
    simp only [scale, List.length_cons]
    omega

end JointThermoComplexity.Complexity.BinaryScaleControl

#print axioms JointThermoComplexity.Complexity.BinaryScaleControl.scale
#print axioms JointThermoComplexity.Complexity.BinaryScaleControl.next_le
#print axioms JointThermoComplexity.Complexity.BinaryScaleControl.read_scale
#print axioms JointThermoComplexity.Complexity.BinaryScaleControl.length_scale
