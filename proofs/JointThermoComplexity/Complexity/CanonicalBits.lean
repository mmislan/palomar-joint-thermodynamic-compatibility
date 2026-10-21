module
public import proofs.JointThermoComplexity.Complexity.FiniteCodec

set_option autoImplicit false
@[expose] public section

/-!
# Canonical binary payloads can be checked by a finite flag

A little-endian natural payload is canonical exactly when it is empty or its
last bit is true. Thus validation can remember the last payload bit; it need
not construct a unary representation of the natural. The fast parser below is
proved equal to the existing canonical parser. This module supplies semantic
lemmas for the machine validator, not a complete machine-runtime theorem.
-/

namespace JointThermoComplexity.Complexity.CanonicalBits
open BitCodec

def validPayload : List Bool → Bool
  | [] => true
  | [b] => b
  | _ :: c :: rest => validPayload (c :: rest)

theorem validPayload_eq_last (payload : List Bool) :
    validPayload payload = payload.getLast?.getD true := by
  induction payload with
  | nil => rfl
  | cons b rest ih =>
    cases rest with
    | nil => rfl
    | cons c rest => simpa only [validPayload, List.getLast?_cons_cons] using ih

theorem bits_ne_nil {n : ℕ} (hn : n ≠ 0) : n.bits ≠ [] := by
  intro h
  have hv := congrArg readBits h
  simp only [readBits_bits, show readBits [] = 0 from rfl] at hv
  exact hn hv

theorem valid_bits (n : ℕ) : validPayload n.bits = true := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    by_cases hn : n = 0
    · subst n
      have hb := h rfl
      subst b
      rfl
    · have hne := bits_ne_nil hn
      cases he : n.bits with
      | nil => exact (hne he).elim
      | cons c rest => simpa only [he, validPayload] using ih

theorem bits_readBits_of_valid (payload : List Bool) (h : validPayload payload = true) :
    (readBits payload).bits = payload := by
  induction payload with
  | nil => rfl
  | cons b rest ih =>
    cases rest with
    | nil =>
      change b = true at h
      subst b
      rfl
    | cons c rest =>
      have ht : validPayload (c :: rest) = true := h
      have hv := ih ht
      have hn : readBits (c :: rest) ≠ 0 := by
        intro hz
        rw [hz, Nat.zero_bits] at hv
        contradiction
      change (Nat.bit b (readBits (c :: rest))).bits = b :: c :: rest
      rw [Nat.bits_append_bit _ _ (fun hz => (hn hz).elim), hv]

theorem fixed_iff_valid (payload : List Bool) :
    payload = (readBits payload).bits ↔ validPayload payload = true := by
  constructor
  · intro h
    rw [h]
    exact valid_bits _
  · intro h
    exact (bits_readBits_of_valid payload h).symm

theorem readBits_zero_iff {payload : List Bool} (h : validPayload payload = true) :
    readBits payload = 0 ↔ payload = [] := by
  constructor
  · intro hz
    have hv := bits_readBits_of_valid payload h
    rw [hz, Nat.zero_bits] at hv
    exact hv.symm
  · intro hz
    subst payload
    rfl

def parseNaturalFast (input : List Bool) : Option (ℕ × List Bool) := do
  let (payload, suffix) ← parseBits input
  if validPayload payload then pure (readBits payload, suffix) else none

theorem parseNaturalFast_eq (input : List Bool) : parseNaturalFast input = parseNatural input := by
  cases hp : parseBits input with
  | none => simp [parseNaturalFast, parseNatural, hp]
  | some pair =>
    obtain ⟨payload, suffix⟩ := pair
    simp [parseNaturalFast, parseNatural, hp, fixed_iff_valid]

theorem positive_payload_iff {payload : List Bool} (h : validPayload payload = true) :
    0 < readBits payload ↔ payload ≠ [] := by
  rw [Nat.pos_iff_ne_zero]
  exact not_congr (readBits_zero_iff h)

theorem reject_noncanonical (payload suffix : List Bool) (h : validPayload payload = false) :
    parseNatural (encodeBits payload ++ suffix) = none := by
  rw [← parseNaturalFast_eq]
  simp [parseNaturalFast, h]

end JointThermoComplexity.Complexity.CanonicalBits

#print axioms JointThermoComplexity.Complexity.CanonicalBits.fixed_iff_valid
#print axioms JointThermoComplexity.Complexity.CanonicalBits.parseNaturalFast_eq
#print axioms JointThermoComplexity.Complexity.CanonicalBits.positive_payload_iff
