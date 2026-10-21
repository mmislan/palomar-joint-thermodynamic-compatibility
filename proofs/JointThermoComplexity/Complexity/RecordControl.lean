module
public import proofs.JointThermoComplexity.Complexity.FieldControl
public import proofs.JointThermoComplexity.Complexity.MaskCodecBridge

set_option autoImplicit false
@[expose] public section

/-!
# Literal record-control composition

Products, finite arrays, transported data and optional boxes preserve the exact
field-control contract. These definitions provide the semantic targets for TM
composition; they do not assert a runtime for the whole network scanner.
-/

namespace JointThermoComplexity.Complexity.RecordControl
open FiniteCodec FieldControl

variable {α β : Type} {A : Codec α} {B : Codec β}

def product (SA : Control A) (SB : Control B) : Control (FiniteCodec.product A B) where
  taken input := SA.taken input ++ SB.taken (SA.rest input)
  rest input := SB.rest (SA.rest input)
  valid input := SA.valid input && SB.valid (SA.rest input)
  split input := by simpa only [List.append_assoc, SB.split] using SA.split input
  parsed := by
    intro input tail value h
    cases ha : A.parse input with
    | none => simp [FiniteCodec.product, ha] at h
    | some pair =>
      obtain ⟨a, next⟩ := pair
      cases hb : B.parse next with
      | none => simp [FiniteCodec.product, ha, hb] at h
      | some pair =>
        obtain ⟨b, rest⟩ := pair
        simp [FiniteCodec.product, ha, hb] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hca, hra⟩ := SA.parsed ha
        obtain ⟨hcb, hrb⟩ := SB.parsed hb
        simp only [hra, hca, hcb, hrb, FiniteCodec.product]
        trivial
  accepts input := by
    cases ha : A.parse input with
    | none =>
      have hv : SA.valid input ≠ true := by
        intro h
        obtain ⟨a, tail, hp⟩ := (SA.accepts input).mp h
        simp [ha] at hp
      simp [hv, FiniteCodec.product, ha]
    | some pair =>
      obtain ⟨a, next⟩ := pair
      have hva : SA.valid input = true := (SA.accepts input).mpr ⟨a, next, ha⟩
      have hra := (SA.parsed ha).2
      cases hb : B.parse next with
      | none =>
        have hvb : SB.valid next ≠ true := by
          intro h
          obtain ⟨b, tail, hp⟩ := (SB.accepts next).mp h
          simp [hb] at hp
        simp [hva, hra, hvb, FiniteCodec.product, ha, hb]
      | some pair =>
        obtain ⟨b, tail⟩ := pair
        have hvb : SB.valid next = true := (SB.accepts next).mpr ⟨b, tail, hb⟩
        simp [hva, hra, hvb, FiniteCodec.product, ha, hb]

def array (S : Control A) (v : ℕ) : Control (finiteFunction A v) where
  taken := S.copied v
  rest := S.tail v
  valid := S.accepted v
  split := S.split_batch v
  parsed := S.parsed_batch
  accepts := S.accepted_iff v

def transport (S : Control A) (e : α ≃ β) : Control (DataCodec.transport A e) where
  taken := S.taken
  rest := S.rest
  valid := S.valid
  split := S.split
  parsed := by
    intro input tail value h
    cases ha : A.parse input with
    | none => simp [DataCodec.transport, ha] at h
    | some pair =>
      obtain ⟨a, next⟩ := pair
      simp [DataCodec.transport, ha] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa only [DataCodec.transport, Equiv.symm_apply_apply] using S.parsed ha
  accepts input := (S.accepts input).trans (MaskCodecBridge.transport_parse_iff A e input).symm

def booleans (v : ℕ) : Control (finiteFunction boolean v) where
  taken input := input.take v
  rest input := input.drop v
  valid := BooleanVector.accepted v
  split := List.take_append_drop v
  parsed h := by
    obtain ⟨hc, hr⟩ := BooleanVector.parsed_prefix h
    exact ⟨hc.symm, hr.symm⟩
  accepts := BooleanVector.status_iff v

def finset (v : ℕ) : Control (DataCodec.finset v) := transport (booleans v) (DataCodec.finsetEquiv v)

def optional (S : Control A) : Control (FiniteCodec.optional A) where
  taken
    | [] => []
    | false :: _ => [false]
    | true :: rest => true :: S.taken rest
  rest
    | [] => []
    | false :: rest => rest
    | true :: rest => S.rest rest
  valid
    | [] => false
    | false :: _ => true
    | true :: rest => S.valid rest
  split input := by
    cases input with
    | nil => rfl
    | cons bit rest =>
      cases bit with
      | false => rfl
      | true => exact congrArg (List.cons true) (S.split rest)
  parsed := by
    intro input tail value h
    cases input with
    | nil => simp [FiniteCodec.optional] at h
    | cons bit rest =>
      cases bit with
      | false =>
        simp [FiniteCodec.optional] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
      | true =>
        cases ha : A.parse rest with
        | none => simp [FiniteCodec.optional, ha] at h
        | some pair =>
          obtain ⟨a, next⟩ := pair
          simp [FiniteCodec.optional, ha] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hc, hr⟩ := S.parsed ha
          exact ⟨congrArg (List.cons true) hc, hr⟩
  accepts input := by
    cases input with
    | nil => simp [FiniteCodec.optional]
    | cons bit rest =>
      cases bit with
      | false => simp [FiniteCodec.optional]
      | true =>
        cases ha : A.parse rest with
        | none =>
          have hv : S.valid rest ≠ true := by
            intro h
            obtain ⟨a, tail, hp⟩ := (S.accepts rest).mp h
            simp [ha] at hp
          simp [hv, FiniteCodec.optional, ha]
        | some pair =>
          obtain ⟨a, tail⟩ := pair
          have hv : S.valid rest = true := (S.accepts rest).mpr ⟨a, tail, ha⟩
          simp [hv, FiniteCodec.optional, ha]

def reaction (n : ℕ) : Control (DataCodec.reaction n) :=
  transport (product (product (array FieldControl.natural n) (array FieldControl.natural n))
    (product FieldControl.positive FieldControl.positive)) (DataCodec.reactionEquiv n)

def motif (n r : ℕ) : Control (DataCodec.motif n r) :=
  transport (product (finset n) (finset r)) (DataCodec.motifEquiv n r)

def rational : Control DataCodec.rational :=
  transport (product FieldControl.integer FieldControl.positive) DataCodec.rationalEquiv

def box : Control DataCodec.box := transport (product rational rational) DataCodec.boxEquiv

def network (n r c : ℕ) : Control (DataCodec.network n r c) :=
  transport (product (product (array (reaction n) r) (array (motif n r) c))
    (product (booleans r) (array (optional box) n))) (DataCodec.networkEquiv n r c)

theorem network_status_iff (n r c : ℕ) (input : List Bool) :
    (network n r c).valid input = true ↔ ∃ Q tail, (DataCodec.network n r c).parse input = some (Q, tail) :=
  (network n r c).accepts input

end JointThermoComplexity.Complexity.RecordControl

#print axioms JointThermoComplexity.Complexity.RecordControl.network_status_iff
#print axioms JointThermoComplexity.Complexity.RecordControl.network
