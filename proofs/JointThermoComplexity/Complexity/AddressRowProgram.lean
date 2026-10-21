module
public import proofs.JointThermoComplexity.Complexity.AddressCodeProgram
public import proofs.JointThermoComplexity.Complexity.RowWordCodec

set_option autoImplicit false
@[expose] public section

/-! Compile fixed raw row templates to actual binary output with runtime address slots. -/

namespace JointThermoComplexity.Complexity.AddressRowProgram
open _root_.Complexity _root_.Complexity.TM HeaderAt SparseInteger AddressCodeProgram
variable {w k : ℕ} {α : Type}

def marked (f : α → List (Instr k)) : List α → List (Instr k)
  | [] => [.bits [false]]
  | a :: rest => .bits [true] :: (f a ++ marked f rest)

theorem marked_output (values : Fin k → ℕ) (f : α → List (Instr k)) (xs : List α) :
    output values (marked f xs) = RowWordCodec.marked (fun a => output values (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    change true :: output values (f a ++ marked f rest) =
      true :: (output values (f a) ++ RowWordCodec.marked (fun a => output values (f a)) rest)
    rw [output_append, ih]

def monomial (indices : List (Fin k)) : List (Instr k) := marked (fun i => [.index i]) indices

def term (a : ℤ × List (Fin k)) : List (Instr k) := .bits (BitCodec.integerCode a.1) :: monomial a.2

def polynomial (p : Poly (Fin k)) : List (Instr k) := marked term p

def rows (ps : List (Poly (Fin k))) : List (Instr k) := marked polynomial ps

def entries : List (Poly (Fin k)) → List (Instr k)
  | [] => []
  | p :: ps => .bits [true] :: (polynomial p ++ entries ps)

theorem monomial_output (values : Fin k → ℕ) (indices : List (Fin k)) :
    output values (monomial indices) = RowWordCodec.monomial (indices.map (fun i => BitCodec.naturalCode (values i))) := by
  rw [monomial, marked_output, RowWordCodec.monomial, RowWordCodec.marked_map]
  simp only [output, List.flatMap_cons, List.flatMap_nil, code, List.append_nil, id_eq]

theorem term_output (values : Fin k → ℕ) (a : ℤ × List (Fin k)) :
    output values (term a) = RowWordCodec.term (a.1, a.2.map (fun i => BitCodec.naturalCode (values i))) := by
  change BitCodec.integerCode a.1 ++ output values (monomial a.2) = _
  rw [monomial_output]
  rfl

theorem polynomial_output (values : Fin k → ℕ) (p : Poly (Fin k)) :
    output values (polynomial p) = RowWordCodec.polynomial (relabel (fun i => BitCodec.naturalCode (values i)) p) := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    change true :: output values (term a ++ polynomial rest) =
      true :: (RowWordCodec.term (a.1, a.2.map (fun i => BitCodec.naturalCode (values i))) ++
        RowWordCodec.polynomial (relabel (fun i => BitCodec.naturalCode (values i)) rest))
    rw [output_append, term_output, ih]

theorem rows_output (values : Fin k → ℕ) (ps : List (Poly (Fin k))) :
    output values (rows ps) = RowWordCodec.rows (ps.map (relabel (fun i => BitCodec.naturalCode (values i)))) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    change true :: output values (polynomial p ++ rows rest) =
      true :: (RowWordCodec.polynomial (relabel (fun i => BitCodec.naturalCode (values i)) p) ++
        RowWordCodec.rows (rest.map (relabel (fun i => BitCodec.naturalCode (values i)))))
    rw [output_append, polynomial_output, ih]

theorem rows_entries (ps : List (Poly (Fin k))) : rows ps = entries ps ++ [.bits [false]] := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    change .bits [true] :: (polynomial p ++ rows rest) =
      (.bits [true] :: (polynomial p ++ entries rest)) ++ [.bits [false]]
    rw [ih]
    simp only [List.cons_append, List.append_assoc]

theorem entries_append (ps qs : List (Poly (Fin k))) : entries (ps ++ qs) = entries ps ++ entries qs := by
  induction ps with
  | nil => rfl
  | cons p rest ih => simp only [List.cons_append, entries, ih, List.append_assoc]

def literalBytes : List (Instr k) → ℕ
  | [] => 0
  | .bits bits :: rest => bits.length + literalBytes rest
  | .index _ :: rest => literalBytes rest

def indexCount : List (Instr k) → ℕ
  | [] => 0
  | .bits _ :: rest => indexCount rest
  | .index _ :: rest => indexCount rest + 1

theorem program_time (B : ℕ) (program : List (Instr k)) :
    timeBound B program = literalBytes program + indexCount program * ReusableIndexEmitter.timeBound B + program.length := by
  induction program with
  | nil => simp only [timeBound, literalBytes, indexCount, Nat.zero_mul, Nat.zero_add, List.length_nil]
  | cons i rest ih =>
    cases i <;> simp only [timeBound, atomTime, literalBytes, indexCount, List.length_cons, ih]
    · omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega

theorem program_time_polynomial (B : ℕ) (program : List (Instr k)) :
    timeBound B program = 2 * indexCount program * B ^ 2 + 12 * indexCount program * B +
      14 * indexCount program + literalBytes program + program.length := by
  rw [program_time, ReusableIndexEmitter.timeBound_eq]
  ring1

theorem rows_hoareTime (ports : Fin k → Fin w) (scratch : Fin w) (hne : ∀ i, ports i ≠ scratch)
    (values : Fin k → ℕ) (B : ℕ) (hB : ∀ i, values i ≤ B) (ps : List (Poly (Fin k)))
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (AddressCodeProgram.machine ports scratch (rows ps)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports scratch values R work)
      (fun inp work out => Cursor before input
        (emitted ++ RowWordCodec.rows (ps.map (relabel (fun i => BitCodec.naturalCode (values i))))) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports scratch values R work) (timeBound B (rows ps)) := by
  simpa only [rows_output] using AddressCodeProgram.hoareTime ports scratch hne values B hB (rows ps) before input emitted R

theorem entries_hoareTime (ports : Fin k → Fin w) (scratch : Fin w) (hne : ∀ i, ports i ≠ scratch)
    (values : Fin k → ℕ) (B : ℕ) (hB : ∀ i, values i ≤ B) (ps : List (Poly (Fin k)))
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (AddressCodeProgram.machine ports scratch (entries ps)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports scratch values R work)
      (fun inp work out => Cursor before input (emitted ++ output values (entries ps)) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports scratch values R work) (timeBound B (entries ps)) :=
  AddressCodeProgram.hoareTime ports scratch hne values B hB (entries ps) before input emitted R

end JointThermoComplexity.Complexity.AddressRowProgram

#print axioms JointThermoComplexity.Complexity.AddressRowProgram.rows_hoareTime
#print axioms JointThermoComplexity.Complexity.AddressRowProgram.rows_entries
