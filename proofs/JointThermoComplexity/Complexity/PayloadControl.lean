module
public import proofs.JointThermoComplexity.Complexity.CanonicalBits
public import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
@[expose] public section

/-!
# Finite control for canonical natural payloads

Only four reading states are needed: empty, last payload zero, last payload one,
and awaiting a payload bit. The same control validates positive factors by
rejecting the empty payload. Its verdict is proved equal to the existing parser's
acceptance predicate, including malformed and noncanonical inputs.
-/

namespace JointThermoComplexity.Complexity.PayloadControl
open BitCodec CanonicalBits

inductive ReadState where
  | empty | zero | one | payload
  deriving DecidableEq

instance : Fintype ReadState where
  elems := {.empty, .zero, .one, .payload}
  complete p := by cases p <;> simp

def flag : List Bool → ReadState
  | [] => .empty
  | b :: rest => if validPayload (b :: rest) then .one else .zero

def next (p : ReadState) (bit : Bool) : Option ReadState :=
  match p with
  | .payload => some (flag [bit])
  | _ => if bit then some .payload else none

def accept (requirePositive : Bool) : ReadState → Bool
  | .empty => !requirePositive
  | .one => true
  | _ => false

def validity (requirePositive : Bool) (payload : List Bool) : Bool :=
  validPayload payload && (!requirePositive || !payload.isEmpty)

def verdict (requirePositive : Bool) : ReadState → List Bool → Bool
  | _, [] => false
  | p, b :: rest =>
    match next p b with
    | none => accept requirePositive p
    | some q => verdict requirePositive q rest

def copied : ReadState → List Bool → List Bool
  | _, [] => []
  | p, b :: rest => b ::
      match next p b with
      | none => []
      | some q => copied q rest

theorem flag_append (seen : List Bool) (b : Bool) : flag (seen ++ [b]) = flag [b] := by
  have hv : validPayload (seen ++ [b]) = b := by rw [validPayload_eq_last]; simp
  cases hs : seen ++ [b] with
  | nil => simp at hs
  | cons c rest =>
    rw [hs] at hv
    simp only [flag, hv, show validPayload [b] = b from rfl]

theorem next_payload (b : Bool) : next .payload b = some (flag [b]) := rfl

theorem next_flag_false (seen : List Bool) : next (flag seen) false = none := by
  cases seen with
  | nil => rfl
  | cons b rest => cases h : validPayload (b :: rest) <;> simp [flag, next, h]

theorem next_flag_true (seen : List Bool) : next (flag seen) true = some .payload := by
  cases seen with
  | nil => rfl
  | cons b rest => cases h : validPayload (b :: rest) <;> simp [flag, next, h]

theorem accept_flag (requirePositive : Bool) (seen : List Bool) :
    accept requirePositive (flag seen) = validity requirePositive seen := by
  cases seen with
  | nil => cases requirePositive <;> rfl
  | cons b rest =>
    cases h : validPayload (b :: rest) <;> simp [flag, accept, validity, h]

theorem verdict_encoded (requirePositive : Bool) (seen payload suffix : List Bool) :
    verdict requirePositive (flag seen) (encodeBits payload ++ suffix) =
      validity requirePositive (seen ++ payload) := by
  induction payload generalizing seen with
  | nil => simp only [encodeBits, List.singleton_append, verdict, next_flag_false,
      accept_flag, List.append_nil]
  | cons b rest ih =>
    simp only [encodeBits, List.cons_append, verdict, next_flag_true, next_payload]
    rw [← flag_append seen b, ih]
    simp only [List.append_assoc, List.singleton_append]

theorem copied_encoded (seen payload suffix : List Bool) :
    copied (flag seen) (encodeBits payload ++ suffix) = encodeBits payload := by
  induction payload generalizing seen with
  | nil => simp only [encodeBits, List.singleton_append, copied, next_flag_false]
  | cons b rest ih =>
    simp only [encodeBits, List.cons_append, copied, next_flag_true, next_payload]
    rw [← flag_append seen b, ih]

theorem verdict_eq_parseBits (requirePositive : Bool) (seen input : List Bool) :
    verdict requirePositive (flag seen) input =
      match parseBits input with
      | none => false
      | some (payload, _) => validity requirePositive (seen ++ payload) := by
  induction input using parseBits.induct generalizing seen with
  | case1 => rfl
  | case2 rest => simp [parseBits, verdict, next_flag_false, accept_flag]
  | case3 => simp [parseBits, verdict, next_flag_true]
  | case4 b rest ih =>
    simp only [verdict, next_flag_true, next_payload]
    rw [← flag_append seen b, ih]
    cases hp : parseBits rest with
    | none => simp [parseBits, hp]
    | some pair =>
      obtain ⟨payload, suffix⟩ := pair
      simp [parseBits, hp, List.append_assoc]

theorem accepts_natural (input : List Bool) :
    verdict false .empty input = true ↔ ∃ value suffix, parseNatural input = some (value, suffix) := by
  have hv := verdict_eq_parseBits false [] input
  simp only [flag, List.nil_append] at hv
  rw [hv]
  rw [← parseNaturalFast_eq]
  cases hp : parseBits input with
  | none => simp [parseNaturalFast, hp]
  | some pair =>
    obtain ⟨payload, suffix⟩ := pair
    cases hc : validPayload payload <;> simp [parseNaturalFast, hp, validity, hc]

theorem accepts_positive (input : List Bool) :
    verdict true .empty input = true ↔
      ∃ value suffix, FiniteCodec.positive.parse input = some (value, suffix) := by
  have hv := verdict_eq_parseBits true [] input
  simp only [flag, List.nil_append] at hv
  rw [hv]
  cases hp : parseBits input with
  | none => simp [FiniteCodec.positive, ← parseNaturalFast_eq, parseNaturalFast, hp]
  | some pair =>
    obtain ⟨payload, suffix⟩ := pair
    cases hc : validPayload payload with
    | false => simp [FiniteCodec.positive, ← parseNaturalFast_eq, parseNaturalFast, hp, validity, hc]
    | true =>
      by_cases hz : payload = []
      · subst payload
        simp [FiniteCodec.positive, ← parseNaturalFast_eq, parseNaturalFast, hp, validity, validPayload, readBits]
      · have hpos := (positive_payload_iff hc).mpr hz
        simp [FiniteCodec.positive, ← parseNaturalFast_eq, parseNaturalFast, hp, validity, hc, hpos,
          hz]

end JointThermoComplexity.Complexity.PayloadControl

#print axioms JointThermoComplexity.Complexity.PayloadControl.verdict_eq_parseBits
#print axioms JointThermoComplexity.Complexity.PayloadControl.accepts_natural
#print axioms JointThermoComplexity.Complexity.PayloadControl.accepts_positive
