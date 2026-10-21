module
public import proofs.JointThermoComplexity.Complexity.SourceTermCircuitData
public import proofs.JointThermoComplexity.Complexity.SourceQuadraticActivationPolynomials

@[expose] public section

/- Adapted from DInstabilityComplexity/FormulaCircuitData.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Literal activated quadratic circuits for the complete source formula syntax

Each formula node has an activation coordinate. An atomic node includes two
term circuits and three sign-witness coordinates; the equality case may leave
those three unused. Conjunction and disjunction share the original inputs.
-/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open RealSyntax MvPolynomial

variable {n : ℕ}

@[reducible] def FormulaSlot : Formula n → Type
  | .truth | .falsity => Unit
  | .eq s t | .lt s t => Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3)
  | .conj p q | .disj p q => Unit ⊕ (FormulaSlot p ⊕ FormulaSlot q)

@[instance_reducible] def formulaSlotFintype : (p : Formula n) → Fintype (FormulaSlot p)
  | .truth | .falsity => inferInstance
  | .eq _ _ | .lt _ _ => inferInstance
  | .conj p q | .disj p q =>
    letI := formulaSlotFintype p
    letI := formulaSlotFintype q
    inferInstance

instance (p : Formula n) : Fintype (FormulaSlot p) := formulaSlotFintype p

def formulaRoot : (p : Formula n) → FormulaSlot p
  | .truth | .falsity => ()
  | .eq _ _ | .lt _ _ | .conj _ _ | .disj _ _ => .inl ()

def atomLeft (s t : Term n) : Fin n ⊕ TermSlot s → Fin n ⊕ (Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3)) :=
  Sum.elim Sum.inl (fun x => .inr (.inr (.inl (.inl x))))

def atomRight (s t : Term n) : Fin n ⊕ TermSlot t → Fin n ⊕ (Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3)) :=
  Sum.elim Sum.inl (fun x => .inr (.inr (.inl (.inr x))))

def atomPorts (s t : Term n) : Fin 6 → Fin n ⊕ (Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3)) :=
  ![.inr (.inl ()), .inr (.inr (.inl (.inl (termRoot s)))),
    .inr (.inr (.inl (.inr (termRoot t)))), .inr (.inr (.inr 0)),
    .inr (.inr (.inr 1)), .inr (.inr (.inr 2))]

def atomEqualityPorts (s t : Term n) (i : Fin 3) :
    Fin n ⊕ (Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3)) := atomPorts s t (Fin.castLE (by decide) i)

def formulaLeft (p q : Formula n) : Fin n ⊕ FormulaSlot p → Fin n ⊕ (Unit ⊕ (FormulaSlot p ⊕ FormulaSlot q)) :=
  Sum.elim Sum.inl (fun x => .inr (.inr (.inl x)))

def formulaRight (p q : Formula n) : Fin n ⊕ FormulaSlot q → Fin n ⊕ (Unit ⊕ (FormulaSlot p ⊕ FormulaSlot q)) :=
  Sum.elim Sum.inl (fun x => .inr (.inr (.inr x)))

noncomputable def formulaEquations : (p : Formula n) → List (MvPolynomial (Fin n ⊕ FormulaSlot p) ℤ)
  | .truth => [X (.inr ()) * (X (.inr ()) - 1)]
  | .falsity => [X (.inr ())]
  | .eq s t =>
    ((termEquations s).map (rename (atomLeft s t)) ++
      (termEquations t).map (rename (atomRight s t))) ++
      equalityActivationEquations.map (rename (atomEqualityPorts s t))
  | .lt s t =>
    ((termEquations s).map (rename (atomLeft s t)) ++
      (termEquations t).map (rename (atomRight s t))) ++
      strictSignEquations.map (rename (atomPorts s t))
  | .conj p q =>
    ((formulaEquations p).map (rename (formulaLeft p q)) ++
      (formulaEquations q).map (rename (formulaRight p q))) ++
      [X (.inr (.inl ())) * (X (.inr (.inl ())) - 1),
        X (.inr (.inr (.inl (formulaRoot p)))) - X (.inr (.inl ())),
        X (.inr (.inr (.inr (formulaRoot q)))) - X (.inr (.inl ()))]
  | .disj p q =>
    ((formulaEquations p).map (rename (formulaLeft p q)) ++
      (formulaEquations q).map (rename (formulaRight p q))) ++
      [X (.inr (.inl ())) * (X (.inr (.inl ())) - 1),
        X (.inr (.inr (.inl (formulaRoot p)))) +
          X (.inr (.inr (.inr (formulaRoot q)))) - X (.inr (.inl ()))]

theorem card_formulaSlot_le (p : Formula n) : Fintype.card (FormulaSlot p) ≤ 4 * p.size := by
  induction p with
  | truth => exact Fintype.card_unit.le.trans (by decide : 1 ≤ 4)
  | falsity => exact Fintype.card_unit.le.trans (by decide : 1 ≤ 4)
  | eq s t | lt s t =>
    change Fintype.card (Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3)) ≤ 4 * (1 + s.size + t.size)
    rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_sum, Fintype.card_sum,
      card_termSlot, card_termSlot, Fintype.card_fin]
    omega
  | conj p q hp hq | disj p q hp hq =>
    change Fintype.card (Unit ⊕ (FormulaSlot p ⊕ FormulaSlot q)) ≤ 4 * (1 + p.size + q.size)
    rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_sum]
    omega

theorem formulaEquations_length_le (p : Formula n) : (formulaEquations p).length ≤ 4 * p.size := by
  induction p with
  | truth => change 1 ≤ 4 * 1; decide
  | falsity => change 1 ≤ 4 * 1; decide
  | eq s t =>
    simp only [formulaEquations, Formula.size]
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_map, termEquations_length, termEquations_length]
    change s.size + t.size + 2 ≤ 4 * (1 + s.size + t.size)
    omega
  | lt s t =>
    simp only [formulaEquations, Formula.size]
    rw [List.length_append, List.length_append, List.length_map, List.length_map,
      List.length_map, termEquations_length, termEquations_length]
    change s.size + t.size + 4 ≤ 4 * (1 + s.size + t.size)
    omega
  | conj p q hp hq | disj p q hp hq =>
    simp only [formulaEquations, Formula.size]
    rw [List.length_append, List.length_append, List.length_map, List.length_map]
    simp only [List.length_cons, List.length_nil]
    omega

#print axioms card_formulaSlot_le
#print axioms formulaEquations_length_le

end JointThermoComplexity.Complexity.QuadraticCircuit
