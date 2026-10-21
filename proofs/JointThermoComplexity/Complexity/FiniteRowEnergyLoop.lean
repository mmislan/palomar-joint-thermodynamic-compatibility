module
public import proofs.JointThermoComplexity.Complexity.RowEnergyLoop
public import proofs.JointThermoComplexity.Complexity.FiniteRowReadSquare

set_option autoImplicit false
@[expose] public section

/-! The actual bounded outer-row machine consumes the finite source's whole
row-list codec and emits the literal concatenation of its original padded
strict-energy contributions. No row reordering or support merging is used.
-/

namespace JointThermoComplexity.Complexity.FiniteRowEnergyLoop
open _root_.Complexity _root_.Complexity.TM SparseInteger EquationSystemCodec FiniteStrictData FiniteRowSquare
open NumberedTermEquations (relabel_scale relabel_square)
open HeaderAt (Cursor)
variable {w : ℕ}

def rows (p : Data) : List (Poly ℕ) := List.ofFn (inputRow p)

def energy (p : Data) : Poly (Fin (variableCount p)) := (List.ofFn (contribution p)).flatten

theorem original_list (p : Data) : List.ofFn (original p) = p.rows := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [original]

theorem rows_map (p : Data) : rows p = p.rows.map (relabel Fin.val) := by
  rw [← original_list p, List.map_ofFn]
  rfl

theorem rows_code (p : Data) : RowEnergyControl.code (rows p) = (rowsCodec p.arity).code p.rows := by
  rw [rows_map]
  unfold RowEnergyControl.code
  rw [RowWordCodec.marked_map]
  have hf : (fun row : Poly (Fin p.arity) => EquationRowControl.code (relabel Fin.val row)) =
      (SparsePolynomialCodec.polynomial p.arity).code := by
    funext row
    exact EquationRowMachine.code_finite p.arity row
  rw [hf]
  exact RowWordCodec.marked_codec (SparsePolynomialCodec.polynomial p.arity) p.rows

theorem row_length (p : Data) (hp : FiniteEquationHardness.Domain p) :
    ∀ row ∈ rows p, row.length ≤ 3 := by
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  simpa only [input_length] using FiniteStrictBounds.original_length p hp i

theorem row_coefficients (p : Data) (hp : FiniteEquationHardness.Domain p) :
    ∀ row ∈ rows p, ∀ a ∈ row, a.1.natAbs ≤ 5 := by
  intro row hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  exact input_bound p i (FiniteRowReadSquare.coefficient_bound p hp i)

theorem finiteEntries_append {n : ℕ} (p q : Poly (Fin n)) :
    finiteEntries (p ++ q) = finiteEntries p ++ finiteEntries q := by
  simp only [finiteEntries, relabel, List.map_append, RowSquareCanonical.entries_append]

theorem finiteEntries_flatten {n : ℕ} (ps : List (Poly (Fin n))) :
    finiteEntries ps.flatten = (ps.map finiteEntries).flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatten_cons, finiteEntries_append, List.map_cons, ih]

theorem row_entries (p : Data) (i : OriginalIndices p) :
    RowSquareCanonical.entries (scale (-256) (square
      (RowSquareCanonical.homogeneous (p.arity + scaleCount p) (inputRow p i)))) =
      finiteEntries (contribution p i) := by
  simp only [natural_homogeneous, finiteEntries, contribution, relabel_scale, relabel_square]

theorem energy_entries (p : Data) :
    RowEnergyLoop.entries (p.arity + scaleCount p) (rows p) = finiteEntries (energy p) := by
  unfold energy
  rw [finiteEntries_flatten, List.map_ofFn]
  change ((List.ofFn (inputRow p)).map (fun row => RowSquareCanonical.entries
    (scale (-256) (square (RowSquareCanonical.homogeneous (p.arity + scaleCount p) row))))).flatten = _
  rw [List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact row_entries p i

theorem expected_before (scale : ℕ) (items : List (Poly ℕ)) (s : EquationRowControl.State)
    (suffix emitted : List Bool) :
    (RowEnergyLoop.expected scale items s suffix emitted).row.before = s.before ++ RowEnergyControl.code items := by
  induction items generalizing s emitted with
  | nil => rfl
  | cons row rest ih =>
    simpa [RowEnergyLoop.expected, EquationRowControl.expected, RowEnergyControl.code,
      RowWordCodec.marked, List.append_assoc] using
      ih (EquationRowControl.expected { s with before := s.before ++ [true] } row
        (RowEnergyControl.code rest ++ suffix))
        (emitted ++ RowSquareCanonical.entries (SparseInteger.scale (-256)
          (square (RowSquareCanonical.homogeneous scale row))))

theorem encoded_hoareTime (ports : RowEnergyStep.Ports w) (r : Fin (w + 1))
    (ha : r ≠ ports.active) (hp : ∀ a, r ≠ ports.square.index a)
    (p : Data) (hDomain : FiniteEquationHardness.Domain p) (s : EquationRowControl.State)
    (suffix emitted : List Bool) (B W : ℕ) (hB : 2 ≤ B)
    (hlen : ((rowsCodec p.arity).code p.rows ++ suffix).length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : RowEnergyStep.Stable ports R) (hRF : RowEnergyLoop.FuelStable r R) :
    (RowEnergyLoop.machine ports r).HoareTime
      (fun inp work out => RowEnergyStep.Logical ports
        ⟨{ s with input := (rowsCodec p.arity).code p.rows ++ suffix }, true, emitted⟩
        (p.arity + scaleCount p).bits B W R inp work out ∧ IsReg B (work r))
      (fun inp work out => Cursor (s.before ++ (rowsCodec p.arity).code p.rows) suffix
          (emitted ++ finiteEntries (energy p)) inp work out ∧
        RowEnergyStep.Ready ports (RowEnergyLoop.expected (p.arity + scaleCount p) (rows p) s suffix emitted)
          (p.arity + scaleCount p).bits B W R work ∧ IsReg B (work r))
      (RowEnergyLoop.timeBound B W B) := by
  have hlen' : (RowEnergyControl.code (rows p) ++ suffix).length ≤ B := by
    simpa only [rows_code] using hlen
  have h := RowEnergyLoop.encoded_hoareTime ports r ha hp B W (p.arity + scaleCount p) hB
    (rows p) (row_length p hDomain) (row_coefficients p hDomain) s suffix emitted hlen' R hR hRF
  apply h.consequence
  · intro inp work out hh
    simpa only [rows_code] using hh
  · rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    refine ⟨?_, hr, hf⟩
    simpa only [expected_before, rows_code, RowEnergyLoop.expected_input,
      RowEnergyLoop.expected_output, energy_entries] using hc
  · exact le_rfl

end JointThermoComplexity.Complexity.FiniteRowEnergyLoop

#print axioms JointThermoComplexity.Complexity.FiniteRowEnergyLoop.rows_code
#print axioms JointThermoComplexity.Complexity.FiniteRowEnergyLoop.energy_entries
#print axioms JointThermoComplexity.Complexity.FiniteRowEnergyLoop.encoded_hoareTime
