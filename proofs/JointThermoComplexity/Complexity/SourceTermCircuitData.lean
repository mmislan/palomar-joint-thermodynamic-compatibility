module
public import proofs.JointThermoComplexity.Complexity.RealSyntaxSize
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Linarith

@[expose] public section

/- Adapted from DInstabilityComplexity/TermCircuitData.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Explicit quadratic operation equations for every real-formula term

There is one auxiliary coordinate per syntax node. Child circuits retain the
same input coordinates. The construction does not expand products of terms.
-/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open RealSyntax MvPolynomial

variable {n : ℕ}

@[reducible] def TermSlot : Term n → Type
  | .int _ | .var _ => Unit
  | .add s t | .mul s t => Unit ⊕ (TermSlot s ⊕ TermSlot t)
  | .neg s => Unit ⊕ TermSlot s

def termSlotDecidableEq : (t : Term n) → DecidableEq (TermSlot t)
  | .int _ | .var _ => inferInstance
  | .add s t | .mul s t =>
    letI := termSlotDecidableEq s
    letI := termSlotDecidableEq t
    inferInstance
  | .neg s =>
    letI := termSlotDecidableEq s
    inferInstance

instance (t : Term n) : DecidableEq (TermSlot t) := termSlotDecidableEq t

@[instance_reducible] def termSlotFintype : (t : Term n) → Fintype (TermSlot t)
  | .int _ | .var _ => inferInstance
  | .add s t | .mul s t =>
    letI := termSlotFintype s
    letI := termSlotFintype t
    inferInstance
  | .neg s =>
    letI := termSlotFintype s
    inferInstance

instance (t : Term n) : Fintype (TermSlot t) := termSlotFintype t

def termRoot : (t : Term n) → TermSlot t
  | .int _ | .var _ => ()
  | .add _ _ | .mul _ _ | .neg _ => .inl ()

def binaryLeft (s t : Term n) : Fin n ⊕ TermSlot s → Fin n ⊕ (Unit ⊕ (TermSlot s ⊕ TermSlot t)) :=
  Sum.elim Sum.inl (fun a => Sum.inr (.inr (.inl a)))

def binaryRight (s t : Term n) : Fin n ⊕ TermSlot t → Fin n ⊕ (Unit ⊕ (TermSlot s ⊕ TermSlot t)) :=
  Sum.elim Sum.inl (fun a => Sum.inr (.inr (.inr a)))

def unaryChild (s : Term n) : Fin n ⊕ TermSlot s → Fin n ⊕ (Unit ⊕ TermSlot s) :=
  Sum.elim Sum.inl (fun a => Sum.inr (.inr a))

noncomputable def termEquations : (t : Term n) → List (MvPolynomial (Fin n ⊕ TermSlot t) ℤ)
  | .int z => [X (.inr ()) - C z]
  | .var v => [X (.inr ()) - X (.inl v)]
  | .add s t =>
    ((termEquations s).map (rename (binaryLeft s t)) ++
      (termEquations t).map (rename (binaryRight s t))) ++
      [X (.inr (.inl ())) -
        (X (.inr (.inr (.inl (termRoot s)))) + X (.inr (.inr (.inr (termRoot t)))))]
  | .mul s t =>
    ((termEquations s).map (rename (binaryLeft s t)) ++
      (termEquations t).map (rename (binaryRight s t))) ++
      [X (.inr (.inl ())) -
        X (.inr (.inr (.inl (termRoot s)))) * X (.inr (.inr (.inr (termRoot t))))]
  | .neg s =>
    (termEquations s).map (rename (unaryChild s)) ++
      [X (.inr (.inl ())) + X (.inr (.inr (termRoot s)))]

theorem card_termSlot (t : Term n) : Fintype.card (TermSlot t) = t.size := by
  induction t with
  | int z => exact Fintype.card_unit
  | var v => exact Fintype.card_unit
  | add s t hs ht | mul s t hs ht =>
    change Fintype.card (Unit ⊕ (TermSlot s ⊕ TermSlot t)) = 1 + s.size + t.size
    simp only [Fintype.card_sum, Fintype.card_unit, hs, ht]
    omega
  | neg s hs =>
    change Fintype.card (Unit ⊕ TermSlot s) = 1 + s.size
    simp only [Fintype.card_sum, Fintype.card_unit, hs]

theorem termEquations_length (t : Term n) : (termEquations t).length = t.size := by
  induction t with
  | int z => rfl
  | var v => rfl
  | add s t hs ht | mul s t hs ht =>
    simp only [termEquations, Term.size]
    rw [List.length_append, List.length_append, List.length_map, List.length_map, hs, ht]
    change s.size + t.size + 1 = 1 + s.size + t.size
    omega
  | neg s hs =>
    simp only [termEquations, Term.size]
    rw [List.length_append, List.length_map, hs]
    change s.size + 1 = 1 + s.size
    omega

#print axioms card_termSlot
#print axioms termEquations_length

end JointThermoComplexity.Complexity.QuadraticCircuit
