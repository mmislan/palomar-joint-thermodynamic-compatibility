module
public import proofs.JointThermoComplexity.Complexity.SourceClosedQuadratic
public import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
@[expose] public section

/-! # Computable finite numbering of all source circuit coordinates

These equivalences are assembled from explicit unit and finite-sum maps.
Both directions are executable; Fintype.equivFin and choice are not used in
their definitions. The old source arity is retained exactly.
-/

namespace JointThermoComplexity.Complexity.SourceCoordinateEnumeration
open RealSyntax QuadraticCircuit
variable {n : ℕ} {V W : Type} {a b : ℕ}

def unitEnumeration : Unit ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => ()
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => Subsingleton.elim _ _

def sumEnumeration (ea : V ≃ Fin a) (eb : W ≃ Fin b) : V ⊕ W ≃ Fin (a + b) :=
  (Equiv.sumCongr ea eb).trans finSumFinEquiv

def termEnumeration : (t : Term n) → TermSlot t ≃ Fin t.size
  | .int _ | .var _ => unitEnumeration
  | .add s t | .mul s t =>
    (sumEnumeration unitEnumeration (sumEnumeration (termEnumeration s) (termEnumeration t))).trans
      (finCongr (by change 1 + (s.size + t.size) = 1 + s.size + t.size; omega))
  | .neg s => sumEnumeration unitEnumeration (termEnumeration s)

def formulaCount : Formula n → ℕ
  | .truth | .falsity => 1
  | .eq s t | .lt s t => 1 + ((s.size + t.size) + 3)
  | .conj p q | .disj p q => 1 + (formulaCount p + formulaCount q)

def formulaEnumeration : (p : Formula n) → FormulaSlot p ≃ Fin (formulaCount p)
  | .truth | .falsity => unitEnumeration
  | .eq s t | .lt s t =>
    sumEnumeration unitEnumeration
      (sumEnumeration (sumEnumeration (termEnumeration s) (termEnumeration t)) (Equiv.refl (Fin 3)))
  | .conj p q | .disj p q =>
    sumEnumeration unitEnumeration (sumEnumeration (formulaEnumeration p) (formulaEnumeration q))

theorem formulaCount_eq_card (p : Formula n) : formulaCount p = Fintype.card (FormulaSlot p) := by
  have h := Fintype.card_congr (formulaEnumeration p)
  simpa only [Fintype.card_fin] using h.symm

theorem formulaCount_le_size (p : Formula n) : formulaCount p ≤ 4 * p.size := by
  rw [formulaCount_eq_card]
  exact card_formulaSlot_le p

def sourceCount (s : Sentence) : ℕ := s.arity + formulaCount s.formula

def sourceEnumeration (s : Sentence) : SourceVariables s ≃ Fin (sourceCount s) :=
  sumEnumeration (Equiv.refl (Fin s.arity)) (formulaEnumeration s.formula)

theorem sourceCount_eq_arity (s : Sentence) : sourceCount s = sourceArity s := by
  have h := Fintype.card_congr (sourceEnumeration s)
  simpa only [Fintype.card_fin, sourceArity] using h.symm

def numericReindex (s : Sentence) : SourceVariables s ≃ Fin (sourceArity s) :=
  (sourceEnumeration s).trans (finCongr (sourceCount_eq_arity s))

theorem sourceCount_le_code_length (s : Sentence) : sourceCount s ≤ 5 * s.code.length := by
  rw [sourceCount_eq_arity]
  exact sourceArity_le_code_length s

end JointThermoComplexity.Complexity.SourceCoordinateEnumeration

#print axioms JointThermoComplexity.Complexity.SourceCoordinateEnumeration.termEnumeration
#print axioms JointThermoComplexity.Complexity.SourceCoordinateEnumeration.formulaEnumeration
#print axioms JointThermoComplexity.Complexity.SourceCoordinateEnumeration.numericReindex
#print axioms JointThermoComplexity.Complexity.SourceCoordinateEnumeration.sourceCount_le_code_length
