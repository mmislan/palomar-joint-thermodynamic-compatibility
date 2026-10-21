module
public import proofs.JointThermoComplexity.Complexity.RowSquareStored
public import proofs.JointThermoComplexity.Complexity.RowSquareMachine
public import proofs.JointThermoComplexity.Complexity.SparseQuadraticLift

set_option autoImplicit false
@[expose] public section

/-! Exact sparse-polynomial meaning of actual row-square output. Raw terms of
degree above two are discarded by the same executable quadratic lift, and every
retained zero coefficient and literal Cartesian occurrence remains in the stream.
-/

namespace JointThermoComplexity.Complexity.RowSquareCanonical
open SparseInteger EquationRowControl RowSquareWords RowSquareStored

def coordinate (scale : ℕ) : ℕ ⊕ Unit → ℕ := Sum.elim (fun v => 2 * v) (fun _ => 2 * scale)
def homogeneous (scale : ℕ) (row : Poly ℕ) : Poly ℕ := relabel (coordinate scale) (SparseQuadraticLift.lift row)
def encode (a : ℤ × List ℕ) : WordTerm := (BitCodec.integerCode a.1, a.2.map BitCodec.naturalCode)

def entries : Poly ℕ → List Bool
  | [] => []
  | a :: rest => true :: (RowWordCodec.term (a.1, a.2.map BitCodec.naturalCode) ++ entries rest)

theorem entries_append (p q : Poly ℕ) : entries (p ++ q) = entries p ++ entries q := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, entries, ih, List.append_assoc]

theorem entries_polynomial (p : Poly ℕ) : entries p ++ [false] = RowWordCodec.polynomial (relabel BitCodec.naturalCode p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change (true :: (RowWordCodec.term (a.1, a.2.map BitCodec.naturalCode) ++ entries p)) ++ [false] =
      true :: (RowWordCodec.term (a.1, a.2.map BitCodec.naturalCode) ++ RowWordCodec.polynomial (relabel BitCodec.naturalCode p))
    rw [← ih]
    simp only [List.cons_append, List.append_assoc]

theorem sourcePiece_toList (scale : ℕ) (a : ℤ × List ℕ) :
    (sourcePiece scale a).toList = (relabel (coordinate scale) (SparseQuadraticLift.term a)).map encode := by
  unfold sourcePiece SparseQuadraticLift.term
  split_ifs <;> simp [encode, relabel, coordinate, Function.comp_def]

theorem homogeneous_cons (scale : ℕ) (a : ℤ × List ℕ) (row : Poly ℕ) :
    homogeneous scale (a :: row) = relabel (coordinate scale) (SparseQuadraticLift.term a) ++ homogeneous scale row := by
  simp only [homogeneous, SparseQuadraticLift.lift, List.flatMap_cons, relabel, List.map_append]

theorem sourcePieces_eq (scale : ℕ) (row : Poly ℕ) : sourcePieces scale row = (homogeneous scale row).map encode := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    change (sourcePiece scale a).toList ++ sourcePieces scale row = _
    rw [homogeneous_cons, List.map_append, sourcePiece_toList, ih]

theorem homogeneous_bound (scale : ℕ) (row : Poly ℕ) (hp : ∀ a ∈ row, a.1.natAbs ≤ 5) :
    ∀ a ∈ homogeneous scale row, a.1.natAbs ≤ 5 := by
  intro a ha
  unfold homogeneous relabel at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  unfold SparseQuadraticLift.lift at hb
  obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
  unfold SparseQuadraticLift.term at hb
  split at hb
  · have he := List.mem_singleton.mp hb
    subst b
    exact hp c hc
  · simp at hb

theorem entry_code (a b : ℤ × List ℕ) (ha : a.1.natAbs ≤ 5) (hb : b.1.natAbs ≤ 5) :
    entryWords (encode a) (encode b) =
      true :: RowWordCodec.term (-256 * (a.1 * b.1), (a.2 ++ b.2).map BitCodec.naturalCode) := by
  simp only [entryWords, encode, EquationProductReplay.output_code a.1 b.1 ha hb, RowWordCodec.term,
    List.map_append, mul_assoc]

theorem inner_entries (a : ℤ × List ℕ) (ha : a.1.natAbs ≤ 5) (q : Poly ℕ)
    (hq : ∀ b ∈ q, b.1.natAbs ≤ 5) :
    (q.map encode).flatMap (fun b => entryWords (encode a) b) =
      entries (scale (-256) (q.map (fun b => (a.1 * b.1, a.2 ++ b.2)))) := by
  induction q with
  | nil => rfl
  | cons b q ih =>
    have hb := hq b (by simp)
    have hr := ih (fun c hc => hq c (by simp [hc]))
    change entryWords (encode a) (encode b) ++ (q.map encode).flatMap (fun c => entryWords (encode a) c) =
      true :: (RowWordCodec.term (-256 * (a.1 * b.1), (a.2 ++ b.2).map BitCodec.naturalCode) ++
        entries (scale (-256) (q.map (fun c => (a.1 * c.1, a.2 ++ c.2)))))
    rw [entry_code a b ha hb, hr]
    rfl

theorem scale_append (c : ℤ) (p q : Poly ℕ) : scale c (p ++ q) = scale c p ++ scale c q := List.map_append

theorem cartesian_encoded (p q : Poly ℕ) (hp : ∀ a ∈ p, a.1.natAbs ≤ 5) (hq : ∀ a ∈ q, a.1.natAbs ≤ 5) :
    cartesian (p.map encode) (q.map encode) = entries (scale (-256) (product p q)) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha := hp a (by simp)
    have hr := ih (fun b hb => hp b (by simp [hb]))
    change (q.map encode).flatMap (fun b => entryWords (encode a) b) ++ cartesian (p.map encode) (q.map encode) =
      entries (scale (-256) (q.map (fun b => (a.1 * b.1, a.2 ++ b.2)) ++ product p q))
    rw [scale_append, entries_append, inner_entries a ha q hq, hr]

theorem output_code (s : State) (row : Poly ℕ) (suffix : List Bool) (hr : row.length ≤ 3)
    (hc : ∀ a ∈ row, a.1.natAbs ≤ 5) (scale : ℕ) :
    RowSquareControl.output (expected s row suffix) scale.bits = entries (SparseInteger.scale (-256) (square (homogeneous scale row))) := by
  rw [RowSquareWords.output_eq, pieces_expected s row suffix hr scale, sourcePieces_eq]
  exact cartesian_encoded (homogeneous scale row) (homogeneous scale row)
    (homogeneous_bound scale row hc) (homogeneous_bound scale row hc)

theorem encoded_hoareTime {w : ℕ} (p : RowSquareFrame.Ports w) (s : State) (row : Poly ℕ) (suffix : List Bool)
    (hr : row.length ≤ 3) (hc : ∀ a ∈ row, a.1.natAbs ≤ 5) (scale B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → _root_.Complexity.Tape) → Prop) (hR : RowSquareFrame.Stable p R) :
    (RowSquareMachine.machine p).HoareTime (RowSquareFrame.Logical p (expected s row suffix) scale.bits B W emitted R)
      (RowSquareFrame.Logical p (expected s row suffix) scale.bits B W
        (emitted ++ entries (SparseInteger.scale (-256) (square (homogeneous scale row)))) R)
      (RowSquareMachine.timeBound B W) := by
  simpa only [output_code s row suffix hr hc scale] using
    RowSquareMachine.hoareTime p (expected s row suffix) scale.bits B W hB emitted R hR

end JointThermoComplexity.Complexity.RowSquareCanonical

#print axioms JointThermoComplexity.Complexity.RowSquareCanonical.output_code
#print axioms JointThermoComplexity.Complexity.RowSquareCanonical.encoded_hoareTime
