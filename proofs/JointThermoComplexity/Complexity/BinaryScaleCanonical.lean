module
public import proofs.JointThermoComplexity.Complexity.BinaryScaleControl

set_option autoImplicit false
@[expose] public section

/-! Canonical binary output for the bounded-carry scaling specification.
These word-control lemmas precede the separate actual tape transducer. -/

namespace JointThermoComplexity.Complexity.BinaryScaleCanonical
open BinaryScaleControl BitCodec CanonicalBits

theorem valid_cons (b : Bool) (bits : List Bool) (hn : bits ≠ []) :
    validPayload (b :: bits) = validPayload bits := by
  cases bits with
  | nil => exact (hn rfl).elim
  | cons c rest => rfl

theorem finish_bits (x : ℕ) (hx : 0 < x) :
    decide (x % 2 = 1) :: (x / 2).bits = x.bits := by
  have hc : x / 2 = 0 → decide (x % 2 = 1) = true := by
    intro hd
    apply decide_eq_true
    have hm := Nat.mod_lt x (by decide : 0 < 2)
    have he := Nat.mod_add_div x 2
    omega
  have he : Nat.bit (decide (x % 2 = 1)) (x / 2) = x := by
    rw [digit_value]
    exact Nat.mod_add_div x 2
  have hb := Nat.bits_append_bit (x / 2) (decide (x % 2 = 1)) hc
  rw [he] at hb
  exact hb.symm

theorem scale_nonempty (k carry : ℕ) (bits : List Bool) (hk : 0 < k) (hb : 0 < readBits bits) :
    scale k carry bits ≠ [] := by
  intro he
  have hv := read_scale k carry bits
  rw [he] at hv
  have hp : 0 < k * readBits bits := Nat.mul_pos hk hb
  change 0 = carry + k * readBits bits at hv
  omega

theorem valid_scale (k : ℕ) (hk : 0 < k) (carry : ℕ) (bits : List Bool)
    (hb : validPayload bits = true) : validPayload (scale k carry bits) = true := by
  induction bits generalizing carry with
  | nil => exact valid_bits carry
  | cons b rest ih =>
    cases rest with
    | nil =>
      change b = true at hb
      subst b
      have hp : 0 < total k carry true := by dsimp [total]; omega
      change validPayload (decide (total k carry true % 2 = 1) :: (total k carry true / 2).bits) = true
      rw [finish_bits _ hp]
      exact valid_bits _
    | cons c rest =>
      have ht : validPayload (c :: rest) = true := hb
      have hn := scale_nonempty k (next k carry b) (c :: rest) hk
        ((positive_payload_iff ht).mpr (by simp))
      change validPayload (digit k carry b :: scale k (next k carry b) (c :: rest)) = true
      rw [valid_cons _ _ hn]
      exact ih _ ht

theorem scale_bits (k v : ℕ) (hk : 0 < k) : scale k 0 v.bits = (k * v).bits := by
  have h := bits_readBits_of_valid (scale k 0 v.bits) (valid_scale k hk 0 v.bits (valid_bits v))
  rw [read_scale, readBits_bits, Nat.zero_add] at h
  exact h.symm

def multiply (k : ℕ) (bits : List Bool) : List Bool := if k = 0 then [] else scale k 0 bits

theorem multiply_bits (k v : ℕ) : multiply k v.bits = (k * v).bits := by
  by_cases hk : k = 0
  · subst k
    simp [multiply]
  · simpa only [multiply, ite_eq_right hk] using scale_bits k v (Nat.pos_of_ne_zero hk)

theorem length_multiply (k : ℕ) (bits : List Bool) : (multiply k bits).length ≤ bits.length + k := by
  unfold multiply
  split_ifs
  · simp
  · exact length_scale k 0 bits (Nat.zero_le _)

end JointThermoComplexity.Complexity.BinaryScaleCanonical

#print axioms JointThermoComplexity.Complexity.BinaryScaleCanonical.valid_scale
#print axioms JointThermoComplexity.Complexity.BinaryScaleCanonical.scale_bits
#print axioms JointThermoComplexity.Complexity.BinaryScaleCanonical.multiply_bits
#print axioms JointThermoComplexity.Complexity.BinaryScaleCanonical.length_multiply
