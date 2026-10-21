module
public import proofs.JointThermoComplexity.Complexity.SparseQuadraticRelabel
public import proofs.JointThermoComplexity.Complexity.FiniteStrictNumbering
public import proofs.JointThermoComplexity.Complexity.RowSquareCanonical

set_option autoImplicit false
@[expose] public section

/-! Exact finite original-row energy data and bytes. The actual row-square
machine now emits the contribution selected by the finite strict enumeration,
with zero terms, higher-degree filtering and literal pair order preserved.
-/

namespace JointThermoComplexity.Complexity.FiniteRowSquare
open SparseInteger EquationSystemCodec FiniteStrictData FiniteStrictNumbering
open NumberedTermEquations (relabel_comp relabel_scale relabel_square)

def port (p : Data) : Fin p.arity ⊕ Unit → Fin (variableCount p) :=
  Sum.elim (originalVariable p) (fun _ => sharedScale p)

def row (p : Data) (i : OriginalIndices p) : Poly (Fin (variableCount p)) :=
  relabel (port p) (SparseQuadraticLift.lift (original p i))

def contribution (p : Data) (i : OriginalIndices p) : Poly (Fin (variableCount p)) := scale (-256) (square (row p i))
def inputRow (p : Data) (i : OriginalIndices p) : Poly ℕ := relabel Fin.val (original p i)
def finiteEntries {n : ℕ} (q : Poly (Fin n)) : List Bool := RowSquareCanonical.entries (relabel Fin.val q)

theorem port_val (p : Data) (a : Fin p.arity ⊕ Unit) :
    (port p a).val = RowSquareCanonical.coordinate (p.arity + scaleCount p) (Sum.map Fin.val id a) := by
  cases a with
  | inl v => exact original_val p v
  | inr u => exact shared_val p

theorem natural_homogeneous (p : Data) (i : OriginalIndices p) :
    RowSquareCanonical.homogeneous (p.arity + scaleCount p) (inputRow p i) = relabel Fin.val (row p i) := by
  unfold RowSquareCanonical.homogeneous inputRow
  rw [SparseQuadraticRelabel.lift, relabel_comp]
  unfold row
  rw [relabel_comp]
  congr 1
  funext a
  exact (port_val p a).symm

theorem numbered_original (p : Data) (i : OriginalIndices p) :
    relabel (variableEnumeration p) (relabel Sum.inl (energyFamily p (originalIndex p i))) = row p i := by
  rw [original_energy]
  simp only [paddedFamily, SparseCirclePadding.family, Sum.elim_inl, scaledFamily, SparseScaledSystem.family,
    relabel_comp]
  unfold row
  congr 1
  funext a
  cases a <;> rfl

theorem contribution_literal (p : Data) (i : OriginalIndices p) :
    contribution p i = relabel (variableEnumeration p)
      (neg (scale 256 (relabel Sum.inl (square (energyFamily p (originalIndex p i)))))) := by
  have hs : relabel (variableEnumeration p) (relabel Sum.inl (square (energyFamily p (originalIndex p i)))) = square (row p i) := by
    rw [relabel_square, relabel_square, numbered_original]
  unfold contribution neg
  rw [relabel_scale, relabel_scale, hs]
  simp [scale, List.map_map, Function.comp_def]

theorem finiteEntries_codec {n : ℕ} (q : Poly (Fin n)) :
    finiteEntries q ++ [false] = (SparsePolynomialCodec.polynomial n).code q := by
  rw [finiteEntries, RowSquareCanonical.entries_polynomial, relabel_comp]
  exact RowWordCodec.polynomial_finite n q

theorem input_length (p : Data) (i : OriginalIndices p) : (inputRow p i).length = (original p i).length := length_relabel _ _

theorem input_bound (p : Data) (i : OriginalIndices p) (hc : ∀ a ∈ original p i, a.1.natAbs ≤ 5) :
    ∀ a ∈ inputRow p i, a.1.natAbs ≤ 5 := by
  intro a ha
  unfold inputRow relabel at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hc b hb

theorem output_code (p : Data) (i : OriginalIndices p) (s : EquationRowControl.State) (suffix : List Bool)
    (hr : (original p i).length ≤ 3) (hc : ∀ a ∈ original p i, a.1.natAbs ≤ 5) :
    RowSquareControl.output (EquationRowControl.expected s (inputRow p i) suffix) (p.arity + scaleCount p).bits =
      finiteEntries (contribution p i) := by
  have hlen : (inputRow p i).length ≤ 3 := by rw [input_length]; exact hr
  have h := RowSquareCanonical.output_code s (inputRow p i) suffix hlen (input_bound p i hc) (p.arity + scaleCount p)
  rw [natural_homogeneous] at h
  simpa only [finiteEntries, contribution, relabel_scale, relabel_square] using h

theorem encoded_hoareTime {w : ℕ} (ports : RowSquareFrame.Ports w) (p : Data) (i : OriginalIndices p)
    (s : EquationRowControl.State) (suffix : List Bool) (hr : (original p i).length ≤ 3)
    (hc : ∀ a ∈ original p i, a.1.natAbs ≤ 5) (B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → _root_.Complexity.Tape) → Prop) (hR : RowSquareFrame.Stable ports R) :
    (RowSquareMachine.machine ports).HoareTime
      (RowSquareFrame.Logical ports (EquationRowControl.expected s (inputRow p i) suffix) (p.arity + scaleCount p).bits B W emitted R)
      (RowSquareFrame.Logical ports (EquationRowControl.expected s (inputRow p i) suffix) (p.arity + scaleCount p).bits B W
        (emitted ++ finiteEntries (contribution p i)) R) (RowSquareMachine.timeBound B W) := by
  simpa only [output_code p i s suffix hr hc] using
    RowSquareMachine.hoareTime ports (EquationRowControl.expected s (inputRow p i) suffix)
      (p.arity + scaleCount p).bits B W hB emitted R hR

theorem encoded_energy_hoareTime {w : ℕ} (ports : RowSquareFrame.Ports w) (p : Data) (i : OriginalIndices p)
    (s : EquationRowControl.State) (suffix : List Bool) (hr : (original p i).length ≤ 3)
    (hc : ∀ a ∈ original p i, a.1.natAbs ≤ 5) (B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → _root_.Complexity.Tape) → Prop) (hR : RowSquareFrame.Stable ports R) :
    (RowSquareMachine.machine ports).HoareTime
      (RowSquareFrame.Logical ports (EquationRowControl.expected s (inputRow p i) suffix) (p.arity + scaleCount p).bits B W emitted R)
      (RowSquareFrame.Logical ports (EquationRowControl.expected s (inputRow p i) suffix) (p.arity + scaleCount p).bits B W
        (emitted ++ finiteEntries (relabel (variableEnumeration p)
          (neg (scale 256 (relabel Sum.inl (square (energyFamily p (originalIndex p i)))))))) R)
      (RowSquareMachine.timeBound B W) := by
  simpa only [contribution_literal] using encoded_hoareTime ports p i s suffix hr hc B W hB emitted R hR

end JointThermoComplexity.Complexity.FiniteRowSquare

#print axioms JointThermoComplexity.Complexity.FiniteRowSquare.natural_homogeneous
#print axioms JointThermoComplexity.Complexity.FiniteRowSquare.numbered_original
#print axioms JointThermoComplexity.Complexity.FiniteRowSquare.output_code
#print axioms JointThermoComplexity.Complexity.FiniteRowSquare.encoded_energy_hoareTime
