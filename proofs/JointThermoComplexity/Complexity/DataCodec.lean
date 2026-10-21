module
public import proofs.JointThermoComplexity.Complexity.FiniteCodec
public import proofs.JointThermoComplexity.Complexity.NetworkData

set_option autoImplicit false
@[expose] public section

/-!
# Literal network data codecs at fixed dimensions

Finite complexes are binary natural tables. Positive rational factors retain
their input numerator and denominator. Motifs are finite membership vectors,
so no duplicate-index or out-of-range annotation can be decoded. This codec
does not recognize PAC status or impose side incidence. Distinct reaction
identities remain separate positions, even when all their data coincide.
-/

namespace JointThermoComplexity.Complexity.DataCodec
open FiniteCodec NetworkData ReactionCircuit

variable {α β : Type}

def transport (A : Codec α) (e : α ≃ β) : Codec β where
  code b := A.code (e.symm b)
  parse input := do
    let (a, suffix) ← A.parse input
    pure (e a, suffix)
  roundtrip := by
    intro b suffix
    simp [A.roundtrip]
  sound := by
    intro input b suffix h
    cases ha : A.parse input with
    | none => simp [ha] at h
    | some pair =>
      obtain ⟨a, rest⟩ := pair
      simp [ha] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa only [Equiv.symm_apply_apply] using A.sound ha

abbrev PositiveNatural := {a : ℕ // 0 < a}

def rationalEquiv : (ℤ × PositiveNatural) ≃ RationalPoint where
  toFun v := ⟨v.1, v.2.val, v.2.property⟩
  invFun q := (q.numerator, ⟨q.denominator, q.denominator_pos⟩)
  left_inv := by rintro ⟨z, ⟨d, hd⟩⟩; rfl
  right_inv := by rintro ⟨z, d, hd⟩; rfl

def rational : Codec RationalPoint :=
  transport (product integer positive) rationalEquiv

def boxEquiv : (RationalPoint × RationalPoint) ≃ ClosedBox where
  toFun v := ⟨v.1, v.2⟩
  invFun b := (b.lower, b.upper)
  left_inv := by rintro ⟨lo, hi⟩; rfl
  right_inv := by rintro ⟨lo, hi⟩; rfl

def box : Codec ClosedBox := transport (product rational rational) boxEquiv

def finsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun f := Finset.univ.filter (fun i => f i = true)
  invFun s i := decide (i ∈ s)
  left_inv := by
    intro f
    funext i
    cases h : f i <;> simp [h]
  right_inv := by
    intro s
    ext i
    simp

def finset (n : ℕ) : Codec (Finset (Fin n)) :=
  transport (finiteFunction boolean n) (finsetEquiv n)

def reactionEquiv (n : ℕ) :
    (((Fin n → ℕ) × (Fin n → ℕ)) × (PositiveNatural × PositiveNatural)) ≃ Reaction n where
  toFun v := ⟨v.1.1, v.1.2, v.2.1.val, v.2.2.val, v.2.1.property, v.2.2.property⟩
  invFun r := ((r.reactant, r.product),
    (⟨r.numerator, r.numerator_pos⟩, ⟨r.denominator, r.denominator_pos⟩))
  left_inv := by rintro ⟨⟨a, b⟩, ⟨⟨p, hp⟩, ⟨q, hq⟩⟩⟩; rfl
  right_inv := by rintro ⟨a, b, p, q, hp, hq⟩; rfl

def reaction (n : ℕ) : Codec (Reaction n) :=
  transport (product (product (finiteFunction natural n) (finiteFunction natural n))
    (product positive positive)) (reactionEquiv n)

def motifEquiv (n r : ℕ) : (Finset (Fin n) × Finset (Fin r)) ≃ Motif n r where
  toFun v := ⟨v.1, v.2⟩
  invFun a := (a.species, a.reactions)
  left_inv := by rintro ⟨species, reactions⟩; rfl
  right_inv := by rintro ⟨species, reactions⟩; rfl

def motif (n r : ℕ) : Codec (Motif n r) :=
  transport (product (finset n) (finset r)) (motifEquiv n r)

def networkEquiv (n r c : ℕ) :
    (((Fin r → Reaction n) × (Fin c → Motif n r)) ×
      ((Fin r → Bool) × (Fin n → Option ClosedBox))) ≃ Network n r c where
  toFun v := ⟨v.1.1, v.1.2, v.2.1, v.2.2⟩
  invFun Q := ((Q.reactions, Q.motifs), (Q.forward, Q.boxes))
  left_inv := by rintro ⟨⟨reactions, motifs⟩, ⟨forward, boxes⟩⟩; rfl
  right_inv := by rintro ⟨reactions, motifs, forward, boxes⟩; rfl

def network (n r c : ℕ) : Codec (Network n r c) :=
  transport (product
    (product (finiteFunction (reaction n) r) (finiteFunction (motif n r) c))
    (product (finiteFunction boolean r) (finiteFunction (optional box) n)))
    (networkEquiv n r c)

theorem network_roundtrip (n r c : ℕ) (Q : Network n r c) (suffix : List Bool) :
    (network n r c).parse ((network n r c).code Q ++ suffix) = some (Q, suffix) :=
  (network n r c).roundtrip Q suffix

theorem network_parse_sound (n r c : ℕ) {input suffix : List Bool} {Q : Network n r c}
    (h : (network n r c).parse input = some (Q, suffix)) :
    input = (network n r c).code Q ++ suffix := (network n r c).sound h

theorem positive_rejects_zero (suffix : List Bool) :
    positive.parse (BitCodec.naturalCode 0 ++ suffix) = none := by
  simp [positive]

end JointThermoComplexity.Complexity.DataCodec

#print axioms JointThermoComplexity.Complexity.DataCodec.network_roundtrip
#print axioms JointThermoComplexity.Complexity.DataCodec.network_parse_sound
#print axioms JointThermoComplexity.Complexity.DataCodec.positive_rejects_zero
