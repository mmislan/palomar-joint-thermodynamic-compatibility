module
public import proofs.JointThermoComplexity.Complexity.StrictGeneratedBytes
public import proofs.JointThermoComplexity.Complexity.FiniteRowSquare

set_option autoImplicit false
@[expose] public section

/-! Exact generated components of the finite strict polynomial, with raw
address values and actual byte-emitter specialization. These identify literal
data, including repeated cross terms and the distinct error-chain weight.
-/

namespace JointThermoComplexity.Complexity.FiniteGeneratedEnergy
open _root_.Complexity _root_.Complexity.TM SparseInteger EquationSystemCodec FiniteStrictData FiniteStrictNumbering
open NumberedTermEquations
open StrictGeneratedTemplates
open HeaderAt (Cursor)
variable {w : ℕ}

def paddedRow (p : Data) (i : Fin (paddedEquationCount p)) : Poly (Fin (variableCount p)) :=
  relabel (fun v => variableEnumeration p (.inl v)) (energyFamily p i)
def paddedContribution (p : Data) (i : Fin (paddedEquationCount p)) : Poly (Fin (variableCount p)) :=
  scale (-256) (square (paddedRow p i))
def errorRow (p : Data) (j : Fin (thresholdCount p + 1)) : Poly (Fin (variableCount p)) :=
  relabel (errorVariable p) (SparseStrictPolynomial.edge (thresholdCount p) j)
def errorContribution (p : Data) (j : Fin (thresholdCount p + 1)) : Poly (Fin (variableCount p)) :=
  scale (-400) (square (errorRow p j))
def boxedLead (p : Data) : Poly (Fin (variableCount p)) := scale 256 (square (atom (errorVariable p (Fin.last (thresholdCount p)))))
def unboxedLead (p : Data) : Poly (Fin (variableCount p)) := scale 256
  (product (square (atom (errorVariable p (Fin.last (thresholdCount p)))))
    (sub (constant 1) (square (atom (errorVariable p (Fin.last (thresholdCount p)))))))

theorem boxed_lead_literal (p : Data) : boxedLead p = relabel (variableEnumeration p)
    (scale 256 (square (atom (.inr (Fin.last (thresholdCount p)))))) := rfl

theorem unboxed_lead_literal (p : Data) : unboxedLead p = relabel (variableEnumeration p)
    (scale 256 (product (square (atom (.inr (Fin.last (thresholdCount p)))))
      (sub (constant 1) (square (atom (.inr (Fin.last (thresholdCount p)))))))) := rfl

theorem padded_literal (p : Data) (i : Fin (paddedEquationCount p)) :
    paddedContribution p i = relabel (variableEnumeration p)
      (neg (scale 256 (relabel Sum.inl (square (energyFamily p i))))) := by
  unfold paddedContribution paddedRow
  rw [← relabel_square, ← relabel_scale]
  simp [neg, scale, relabel, List.map_map, Function.comp_def]

theorem error_literal (p : Data) (j : Fin (thresholdCount p + 1)) :
    errorContribution p j = relabel (variableEnumeration p)
      (neg (scale 400 (relabel Sum.inr (square (SparseStrictPolynomial.edge (thresholdCount p) j))))) := by
  unfold errorContribution errorRow
  rw [← relabel_square, ← relabel_scale]
  simp [neg, scale, relabel, List.map_map, Function.comp_def, errorVariable]

theorem padded_initial_row (p : Data) : paddedRow p (scaleInitialIndex p) =
    sub (scale 4 (atom (scaleVariable p 0))) (constant 1) := by
  rw [paddedRow, scale_initial_energy]
  rfl

theorem padded_edge_row (p : Data) (j : Fin (scaleCount p)) : paddedRow p (scaleEdgeIndex p j) =
    sub (atom (scaleVariable p j.succ)) (square (atom (scaleVariable p j.castSucc))) := by
  rw [paddedRow, scale_edge_energy]
  rfl

theorem padded_circle_row (p : Data) (c : ScaleCoordinates p) : paddedRow p (circleIndex p c) =
    sub (scale 16 (add (square (atom (coordinateVariable p c false)))
      (square (atom (coordinateVariable p c true))))) (constant 1) := by
  rw [paddedRow, circle_energy]
  rfl

private theorem relabel_edge_zero {V : Type} (k : ℕ) (f : Fin (k + 1) → V) :
    relabel f (SparseStrictPolynomial.edge k 0) = sub (scale 16 (atom (f 0))) (constant 1) := rfl

private theorem relabel_edge_succ {V : Type} (k : ℕ) (f : Fin (k + 1) → V) (j : Fin k) :
    relabel f (SparseStrictPolynomial.edge k j.succ) =
      scale 16 (sub (atom (f j.succ)) (square (atom (f j.castSucc)))) := by
  rw [SparseStrictPolynomial.edge, Fin.cases_succ]
  simp only [relabel_scale, relabel_sub, relabel_atom, relabel_square]

theorem error_initial_row (p : Data) : errorRow p 0 = sub (scale 16 (atom (errorVariable p 0))) (constant 1) :=
  relabel_edge_zero (thresholdCount p) (errorVariable p)

theorem error_edge_row (p : Data) (j : Fin (thresholdCount p)) : errorRow p j.succ =
    scale 16 (sub (atom (errorVariable p j.succ)) (square (atom (errorVariable p j.castSucc)))) := by
  exact relabel_edge_succ (thresholdCount p) (errorVariable p) j

def scaleInitialValues (p : Data) : Fin 2 → ℕ := ![p.arity, 0]
def scaleEdgeValues (p : Data) (j : Fin (scaleCount p)) : Fin 2 → ℕ := ![p.arity + j.val, p.arity + (j.val + 1)]
def circleValues (p : Data) (c : ScaleCoordinates p) : Fin 2 → ℕ := ![(scaleCoordinateEnumeration p c).val, 0]
def errorInitialValues (p : Data) : Fin 2 → ℕ := ![scaleCoordinateCount p * 2, 0]
def errorEdgeValues (p : Data) (j : Fin (thresholdCount p)) : Fin 2 → ℕ :=
  ![scaleCoordinateCount p * 2 + j.val, scaleCoordinateCount p * 2 + (j.val + 1)]
def leadValues (p : Data) : Fin 2 → ℕ := ![scaleCoordinateCount p * 2 + thresholdCount p, 0]

theorem scale_initial_data (p : Data) : data (scaleInitialValues p) .scaleInitial =
    relabel Fin.val (paddedContribution p (scaleInitialIndex p)) := by
  rw [StrictGeneratedTemplates.scale_initial_data]
  simp only [paddedContribution, relabel_scale, relabel_square, padded_initial_row, relabel_sub,
    relabel_atom, relabel_constant, scale_val, scaleInitialValues, Matrix.cons_val_zero, Fin.val_zero, Nat.add_zero]

theorem scale_edge_data (p : Data) (j : Fin (scaleCount p)) : data (scaleEdgeValues p j) .scaleEdge =
    relabel Fin.val (paddedContribution p (scaleEdgeIndex p j)) := by
  rw [StrictGeneratedTemplates.scale_edge_data]
  simp only [paddedContribution, relabel_scale, relabel_square, padded_edge_row, relabel_sub,
    relabel_atom, scale_val, scaleEdgeValues, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_succ, Fin.val_castSucc]

theorem circle_data (p : Data) (c : ScaleCoordinates p) : data (circleValues p c) .circle =
    relabel Fin.val (paddedContribution p (circleIndex p c)) := by
  rw [StrictGeneratedTemplates.circle_data]
  simp only [paddedContribution, relabel_scale, relabel_square, padded_circle_row, relabel_sub,
    relabel_add, relabel_atom, relabel_constant, variable_val, circleValues, Matrix.cons_val_zero,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem error_initial_data (p : Data) : data (errorInitialValues p) .errorInitial =
    relabel Fin.val (errorContribution p 0) := by
  rw [StrictGeneratedTemplates.error_initial_data]
  simp only [errorContribution, relabel_scale, relabel_square, error_initial_row, relabel_sub,
    relabel_atom, relabel_constant, error_val, errorInitialValues, Matrix.cons_val_zero, Fin.val_zero, Nat.add_zero]

private theorem error_edge_natural {n : ℕ} (k base : ℕ) (f : Fin (k + 1) → Fin n)
    (hf : ∀ j, (f j).val = base + j.val) (j : Fin k) :
    data ![base + j.val, base + (j.val + 1)] .errorEdge =
      relabel Fin.val (scale (-400) (square (relabel f (SparseStrictPolynomial.edge k j.succ)))) := by
  rw [StrictGeneratedTemplates.error_edge_data]
  rw [relabel_edge_succ]
  simp only [relabel_scale, relabel_square, relabel_sub, relabel_atom,
    hf, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_succ, Fin.val_castSucc]

theorem error_edge_data (p : Data) (j : Fin (thresholdCount p)) : data (errorEdgeValues p j) .errorEdge =
    relabel Fin.val (errorContribution p j.succ) :=
  error_edge_natural (thresholdCount p) (scaleCoordinateCount p * 2) (errorVariable p) (error_val p) j

theorem boxed_lead_data (p : Data) : data (leadValues p) .boxedLead = relabel Fin.val (boxedLead p) := by
  rw [StrictGeneratedTemplates.boxed_lead_data]
  simp only [boxedLead, relabel_scale, relabel_square, relabel_atom, error_val, leadValues, Matrix.cons_val_zero, Fin.val_last]

theorem unboxed_lead_data (p : Data) : data (leadValues p) .unboxedLead = relabel Fin.val (unboxedLead p) := by
  rw [StrictGeneratedTemplates.unboxed_lead_data]
  simp only [unboxedLead, relabel_scale, relabel_product, relabel_square, relabel_sub,
    relabel_atom, relabel_constant, error_val, leadValues, Matrix.cons_val_zero, Fin.val_last]

theorem hoareTime (ports : Fin 2 → Fin w) (values : Fin 2 → ℕ) (W : ℕ)
    (hW : ∀ i, (values i).bits.length ≤ W) (kind : Kind) {n : ℕ} (q : Poly (Fin n))
    (hdata : data values kind = relabel Fin.val q) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (StrictGeneratedBytes.machine ports kind).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        WordCodeProgram.Ready ports (fun i => (values i).bits) R work)
      (fun inp work out => Cursor before input (emitted ++ FiniteRowSquare.finiteEntries q) inp work out ∧
        (∀ j, Parked (work j)) ∧ WordCodeProgram.Ready ports (fun i => (values i).bits) R work)
      (StrictGeneratedBytes.timeBound W kind) := by
  simpa only [hdata, FiniteRowSquare.finiteEntries] using
    StrictGeneratedBytes.hoareTime ports values W hW kind before input emitted R

end JointThermoComplexity.Complexity.FiniteGeneratedEnergy

#print axioms JointThermoComplexity.Complexity.FiniteGeneratedEnergy.padded_literal
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedEnergy.error_literal
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedEnergy.circle_data
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedEnergy.error_edge_data
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedEnergy.hoareTime
