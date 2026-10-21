module
public import proofs.JointThermoComplexity.Complexity.RowReadSquareMachine
public import proofs.JointThermoComplexity.Complexity.RowSquareCanonical

set_option autoImplicit false
@[expose] public section

/-! Total bounded control for the marked outer list of source rows. Output is
part of the control state; a false outer marker disables all later iterations.
-/

namespace JointThermoComplexity.Complexity.RowEnergyControl

structure State where
  row : EquationRowControl.State
  active : Bool
  emitted : List Bool

def afterMarker (s : State) : State :=
  ⟨{ s.row with
      before := s.row.before ++ BooleanMachine.copied s.row.input
      input := BooleanMachine.suffix s.row.input
      available := BooleanMachine.accepted s.row.input },
    SourceBitRead.value s.row.input, s.emitted⟩

def afterRow (B : ℕ) (scaleBits : List Bool) (s : State) : State :=
  let t := EquationRowControl.parse B s.row
  ⟨t, s.active, s.emitted ++ RowSquareControl.output t scaleBits⟩

def step (B : ℕ) (scaleBits : List Bool) (s : State) : State :=
  if s.active then
    let t := afterMarker s
    if t.active then afterRow B scaleBits t else t
  else s

def run (B : ℕ) (scaleBits : List Bool) : ℕ → State → State
  | 0, s => s
  | n + 1, s => step B scaleBits (run B scaleBits n s)

theorem inactive (B : ℕ) (scaleBits : List Bool) (s : State) (hs : s.active = false) :
    step B scaleBits s = s := by simp [step, hs]

theorem run_inactive (B : ℕ) (scaleBits : List Bool) (n : ℕ) (s : State) (hs : s.active = false) :
    run B scaleBits n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, inactive B scaleBits s hs]

theorem marker_length (s : State) : (afterMarker s).row.input.length ≤ s.row.input.length := by
  change (BooleanMachine.suffix s.row.input).length ≤ s.row.input.length
  cases s.row.input <;> simp [BooleanMachine.suffix]

theorem step_length (B : ℕ) (scaleBits : List Bool) (s : State) :
    (step B scaleBits s).row.input.length ≤ s.row.input.length := by
  unfold step
  dsimp only
  split
  · split
    · exact (EquationRowControl.parse_length B _).trans (marker_length s)
    · exact marker_length s
  · exact le_rfl

theorem run_length (B : ℕ) (scaleBits : List Bool) (n : ℕ) (s : State) :
    (run B scaleBits n s).row.input.length ≤ s.row.input.length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (step_length B scaleBits (run B scaleBits n s)).trans ih

theorem run_add (B : ℕ) (scaleBits : List Bool) (a b : ℕ) (s : State) :
    run B scaleBits (a + b) s = run B scaleBits b (run B scaleBits a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change step B scaleBits (run B scaleBits (a + b) s) = step B scaleBits (run B scaleBits b (run B scaleBits a s))
    exact congrArg (step B scaleBits) ih

theorem run_succ_start (B : ℕ) (scaleBits : List Bool) (n : ℕ) (s : State) :
    run B scaleBits (n + 1) s = run B scaleBits n (step B scaleBits s) := by
  simpa only [Nat.one_add, Nat.add_one, run] using run_add B scaleBits 1 n s

def code (rows : List (List (ℤ × List ℕ))) : List Bool := RowWordCodec.marked EquationRowControl.code rows

theorem code_length (rows : List (List (ℤ × List ℕ))) : rows.length + 1 ≤ (code rows).length := by
  have h := RowWordCodec.marked_length EquationRowControl.code rows
  change (code rows).length = _ at h
  omega

theorem step_nil (B : ℕ) (scaleBits : List Bool) (s : EquationRowControl.State) (suffix emitted : List Bool) :
    step B scaleBits ⟨{ s with input := code [] ++ suffix }, true, emitted⟩ =
      ⟨{ s with before := s.before ++ code [], input := suffix, available := true }, false, emitted⟩ := by
  simp [step, afterMarker, code, RowWordCodec.marked, BooleanMachine.copied,
    BooleanMachine.suffix, BooleanMachine.accepted, SourceBitRead.value]

theorem step_cons (B : ℕ) (scale : ℕ) (s : EquationRowControl.State)
    (row : List (ℤ × List ℕ)) (rows : List (List (ℤ × List ℕ))) (suffix emitted : List Bool)
    (hr : row.length ≤ 3) (hc : ∀ a ∈ row, a.1.natAbs ≤ 5) (hf : ∀ a ∈ row, a.2.length + 1 ≤ B) :
    step B scale.bits ⟨{ s with input := code (row :: rows) ++ suffix }, true, emitted⟩ =
      ⟨EquationRowControl.expected { s with before := s.before ++ [true] } row (code rows ++ suffix), true,
        emitted ++ RowSquareCanonical.entries (SparseInteger.scale (-256)
          (SparseInteger.square (RowSquareCanonical.homogeneous scale row)))⟩ := by
  have hp := EquationRowControl.parse_code B { s with before := s.before ++ [true], available := true }
    row (code rows ++ suffix) hr hc hf
  have ho := RowSquareCanonical.output_code { s with before := s.before ++ [true], available := true }
    row (code rows ++ suffix) hr hc scale
  simp only [step, afterMarker, code, RowWordCodec.marked, List.cons_append,
    List.append_assoc, BooleanMachine.copied, BooleanMachine.suffix, BooleanMachine.accepted,
    SourceBitRead.value, ↓reduceIte]
  change afterRow B scale.bits
    ⟨{ s with before := s.before ++ [true], input := EquationRowControl.code row ++ (code rows ++ suffix), available := true }, true, emitted⟩ = _
  unfold afterRow
  rw [hp]
  dsimp only
  rw [ho]
  rfl

end JointThermoComplexity.Complexity.RowEnergyControl

#print axioms JointThermoComplexity.Complexity.RowEnergyControl.run_length
#print axioms JointThermoComplexity.Complexity.RowEnergyControl.step_cons
