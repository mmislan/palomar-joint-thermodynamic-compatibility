module
public import proofs.JointThermoComplexity.Complexity.WordCodeProgram
public import proofs.JointThermoComplexity.Complexity.RowWordCodec

set_option autoImplicit false
@[expose] public section

/-! Compile fixed sparse polynomial templates to actual word-buffer output.
Term entries concatenate without row markers; one final false closes the
single polynomial. Repeated monomials and zero coefficients are preserved.
-/

namespace JointThermoComplexity.Complexity.WordPolynomialProgram
open _root_.Complexity _root_.Complexity.TM HeaderAt SparseInteger WordCodeProgram
variable {w k : ℕ} {α : Type}

inductive Ref (k : ℕ) where
  | plain : Fin k → Ref k
  | paired : Bool → Fin k → Ref k
  deriving DecidableEq

def instruction : Ref k → Instr k
  | .plain i => .word i
  | .paired odd i => .paired odd i

def refCode (values : Fin k → List Bool) (r : Ref k) : List Bool := code values (instruction r)

def refValue (values : Fin k → ℕ) : Ref k → ℕ
  | .plain i => values i
  | .paired odd i => 2 * values i + if odd then 1 else 0

theorem refCode_natural (values : Fin k → ℕ) (r : Ref k) :
    refCode (fun i => (values i).bits) r = BitCodec.naturalCode (refValue values r) := by
  cases r with
  | plain i => rfl
  | paired odd i => exact BinaryCoordinateReplay.natural_code odd (values i)

def marked (f : α → List (Instr k)) : List α → List (Instr k)
  | [] => [.bits [false]]
  | a :: rest => .bits [true] :: (f a ++ marked f rest)

theorem marked_output (values : Fin k → List Bool) (f : α → List (Instr k)) (xs : List α) :
    output values (marked f xs) = RowWordCodec.marked (fun a => output values (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    change true :: output values (f a ++ marked f rest) =
      true :: (output values (f a) ++ RowWordCodec.marked (fun a => output values (f a)) rest)
    rw [output_append, ih]

def monomial (indices : List (Ref k)) : List (Instr k) := marked (fun r => [instruction r]) indices
def term (a : ℤ × List (Ref k)) : List (Instr k) := .bits (BitCodec.integerCode a.1) :: monomial a.2
def polynomial (p : SparseInteger.Poly (Ref k)) : List (Instr k) := marked term p

def entries : SparseInteger.Poly (Ref k) → List (Instr k)
  | [] => []
  | a :: rest => .bits [true] :: (term a ++ entries rest)

theorem monomial_output (values : Fin k → List Bool) (indices : List (Ref k)) :
    output values (monomial indices) = RowWordCodec.monomial (indices.map (refCode values)) := by
  rw [monomial, marked_output, RowWordCodec.monomial, RowWordCodec.marked_map]
  simp only [output, List.flatMap_cons, List.flatMap_nil, refCode, List.append_nil, id_eq]

theorem term_output (values : Fin k → List Bool) (a : ℤ × List (Ref k)) :
    output values (term a) = RowWordCodec.term (a.1, a.2.map (refCode values)) := by
  change BitCodec.integerCode a.1 ++ output values (monomial a.2) = _
  rw [monomial_output]
  rfl

theorem polynomial_output (values : Fin k → List Bool) (p : SparseInteger.Poly (Ref k)) :
    output values (polynomial p) = RowWordCodec.polynomial (relabel (refCode values) p) := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    change true :: output values (term a ++ polynomial rest) =
      true :: (RowWordCodec.term (a.1, a.2.map (refCode values)) ++
        RowWordCodec.polynomial (relabel (refCode values) rest))
    rw [output_append, term_output, ih]

theorem polynomial_entries (p : SparseInteger.Poly (Ref k)) : polynomial p = entries p ++ [.bits [false]] := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    change .bits [true] :: (term a ++ polynomial rest) =
      (.bits [true] :: (term a ++ entries rest)) ++ [.bits [false]]
    rw [ih]
    simp only [List.cons_append, List.append_assoc]

theorem entries_append (p q : SparseInteger.Poly (Ref k)) : entries (p ++ q) = entries p ++ entries q := by
  induction p with
  | nil => rfl
  | cons a rest ih => simp only [List.cons_append, entries, ih, List.append_assoc]

theorem entries_complete (values : Fin k → List Bool) (p : SparseInteger.Poly (Ref k)) :
    output values (entries p) ++ [false] = RowWordCodec.polynomial (relabel (refCode values) p) := by
  have h := polynomial_output values p
  rw [polynomial_entries, output_append] at h
  simpa only [output, List.flatMap_cons, List.flatMap_nil, code, List.append_nil] using h

theorem polynomial_finite {n : ℕ} (values : Fin k → ℕ) (indices : Ref k → Fin n)
    (hi : ∀ r, refValue values r = (indices r).val) (p : SparseInteger.Poly (Ref k)) :
    output (fun i => (values i).bits) (polynomial p) =
      (SparsePolynomialCodec.polynomial n).code (relabel indices p) := by
  rw [polynomial_output]
  have hf : refCode (fun i => (values i).bits) = fun r => BitCodec.naturalCode (indices r).val := by
    funext r
    rw [refCode_natural, hi]
  rw [hf]
  have he : relabel (fun r => BitCodec.naturalCode (indices r).val) p =
      relabel (fun i : Fin n => BitCodec.naturalCode i.val) (relabel indices p) := by
    simp [relabel, List.map_map, Function.comp_def]
  rw [he, RowWordCodec.polynomial_finite]

theorem entries_hoareTime (ports : Fin k → Fin w) (values : Fin k → List Bool) (B : ℕ)
    (hB : ∀ i, (values i).length ≤ B) (p : SparseInteger.Poly (Ref k))
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (WordCodeProgram.machine ports (entries p)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports values R work)
      (fun inp work out => Cursor before input (emitted ++ output values (entries p)) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports values R work) (timeBound B (entries p)) :=
  WordCodeProgram.hoareTime ports values B hB (entries p) before input emitted R

theorem polynomial_hoareTime (ports : Fin k → Fin w) (values : Fin k → List Bool) (B : ℕ)
    (hB : ∀ i, (values i).length ≤ B) (p : SparseInteger.Poly (Ref k))
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (WordCodeProgram.machine ports (polynomial p)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports values R work)
      (fun inp work out => Cursor before input (emitted ++ RowWordCodec.polynomial (relabel (refCode values) p)) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports values R work) (timeBound B (polynomial p)) := by
  simpa only [polynomial_output] using WordCodeProgram.hoareTime ports values B hB (polynomial p) before input emitted R

noncomputable def timePolynomial (program : List (Instr k)) : Polynomial ℕ :=
  Polynomial.C (3 * slotCount program) * Polynomial.X +
    Polynomial.C (12 * slotCount program + literalBytes program + program.length)

theorem timePolynomial_eval (program : List (Instr k)) (B : ℕ) :
    (timePolynomial program).eval B = timeBound B program := by
  rw [program_time_polynomial]
  simp [timePolynomial, Nat.add_assoc]

end JointThermoComplexity.Complexity.WordPolynomialProgram

#print axioms JointThermoComplexity.Complexity.WordPolynomialProgram.entries_complete
#print axioms JointThermoComplexity.Complexity.WordPolynomialProgram.polynomial_finite
#print axioms JointThermoComplexity.Complexity.WordPolynomialProgram.polynomial_hoareTime
#print axioms JointThermoComplexity.Complexity.WordPolynomialProgram.timePolynomial_eval
