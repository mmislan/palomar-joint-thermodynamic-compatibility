module
public import proofs.JointThermoComplexity.Complexity.NaturalRawControl
public import proofs.JointThermoComplexity.Complexity.SourceBitRead
public import proofs.JointThermoComplexity.Complexity.RowWordCodec

set_option autoImplicit false
@[expose] public section

/-! Total bounded control for a marked list of binary natural fields.
A false marker or EOF disables later iterations without consuming the suffix.
-/

namespace JointThermoComplexity.Complexity.MarkedNaturalControl

structure State where
  before : List Bool
  input : List Bool
  active : Bool

def afterMarker (s : State) : State :=
  ⟨s.before ++ BooleanMachine.copied s.input, BooleanMachine.suffix s.input, SourceBitRead.value s.input⟩

def afterNatural (s : State) : State :=
  ⟨s.before ++ (NaturalRawControl.scan s.input).taken, (NaturalRawControl.scan s.input).rest, s.active⟩

def step (s : State) : State :=
  if s.active then
    let t := afterMarker s
    if t.active then afterNatural t else t
  else s

def run : ℕ → State → State
  | 0, s => s
  | n + 1, s => step (run n s)

theorem inactive (s : State) (hs : s.active = false) : step s = s := by simp [step, hs]

theorem run_inactive (n : ℕ) (s : State) (hs : s.active = false) : run n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, inactive s hs]

theorem afterMarker_split (s : State) : (afterMarker s).before ++ (afterMarker s).input = s.before ++ s.input := by
  simp only [afterMarker, List.append_assoc, BooleanMachine.consumed_and_suffix]

theorem afterNatural_split (s : State) : (afterNatural s).before ++ (afterNatural s).input = s.before ++ s.input := by
  simp only [afterNatural, List.append_assoc, NaturalRawControl.split]

theorem step_split (s : State) : (step s).before ++ (step s).input = s.before ++ s.input := by
  unfold step
  dsimp only
  split
  · split
    · exact (afterNatural_split _).trans (afterMarker_split s)
    · exact afterMarker_split s
  · rfl

theorem afterMarker_length (s : State) : (afterMarker s).input.length ≤ s.input.length := by
  change (BooleanMachine.suffix s.input).length ≤ s.input.length
  cases s.input <;> simp [BooleanMachine.suffix]

theorem afterNatural_length (s : State) : (afterNatural s).input.length ≤ s.input.length := by
  have h := congrArg List.length (NaturalRawControl.split s.input)
  simp only [List.length_append] at h
  change (NaturalRawControl.scan s.input).rest.length ≤ s.input.length
  omega

theorem step_length (s : State) : (step s).input.length ≤ s.input.length := by
  unfold step
  dsimp only
  split
  · split
    · exact (afterNatural_length _).trans (afterMarker_length s)
    · exact afterMarker_length s
  · exact le_rfl

theorem run_length (n : ℕ) (s : State) : (run n s).input.length ≤ s.input.length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (step_length (run n s)).trans ih

theorem run_add (a b : ℕ) (s : State) : run (a + b) s = run b (run a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change step (run (a + b) s) = step (run b (run a s))
    exact congrArg step ih

theorem run_succ_start (n : ℕ) (s : State) : run (n + 1) s = run n (step s) := by
  have h := run_add 1 n s
  simpa only [Nat.one_add, Nat.add_one, run] using h

def code (items : List ℕ) : List Bool := RowWordCodec.marked BitCodec.naturalCode items

theorem step_nil (before suffix : List Bool) :
    step ⟨before, code [] ++ suffix, true⟩ = ⟨before ++ code [], suffix, false⟩ := by
  simp [step, afterMarker, code, RowWordCodec.marked, BooleanMachine.copied, BooleanMachine.suffix, SourceBitRead.value]

theorem step_cons (value : ℕ) (items : List ℕ) (before suffix : List Bool) :
    step ⟨before, code (value :: items) ++ suffix, true⟩ =
      ⟨(before ++ [true]) ++ BitCodec.naturalCode value, code items ++ suffix, true⟩ := by
  simp [step, afterMarker, afterNatural, code, RowWordCodec.marked, BooleanMachine.copied,
    BooleanMachine.suffix, SourceBitRead.value, NaturalRawControl.natural, List.append_assoc]

theorem run_minimal (items : List ℕ) (before suffix : List Bool) :
    run (items.length + 1) ⟨before, code items ++ suffix, true⟩ = ⟨before ++ code items, suffix, false⟩ := by
  induction items generalizing before with
  | nil => simpa only [List.length_nil, Nat.zero_add, run] using step_nil before suffix
  | cons value items ih =>
    rw [List.length_cons, run_succ_start, step_cons]
    simpa [code, RowWordCodec.marked, List.append_assoc] using ih ((before ++ [true]) ++ BitCodec.naturalCode value)

theorem run_code (fuel : ℕ) (items : List ℕ) (hf : items.length + 1 ≤ fuel) (before suffix : List Bool) :
    run fuel ⟨before, code items ++ suffix, true⟩ = ⟨before ++ code items, suffix, false⟩ := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hf
  rw [run_add, run_minimal]
  exact run_inactive extra _ rfl

theorem code_length (items : List ℕ) : items.length + 1 ≤ (code items).length := by
  have h := RowWordCodec.marked_length BitCodec.naturalCode items
  change (code items).length = _ at h
  omega

end JointThermoComplexity.Complexity.MarkedNaturalControl

#print axioms JointThermoComplexity.Complexity.MarkedNaturalControl.step_split
#print axioms JointThermoComplexity.Complexity.MarkedNaturalControl.run_length
#print axioms JointThermoComplexity.Complexity.MarkedNaturalControl.run_code
