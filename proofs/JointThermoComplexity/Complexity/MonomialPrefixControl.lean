module
public import proofs.JointThermoComplexity.Complexity.MarkedNaturalControl

set_option autoImplicit false
@[expose] public section

/-! Total control for retaining two binary indices and discarding longer monomials.
Unused flags and buffers retain their previous values. Degree decoding therefore
tests the first and second marker before consulting the overflow marker.
-/

namespace JointThermoComplexity.Complexity.MonomialPrefixControl

structure State where
  before : List Bool
  input : List Bool
  flags : Fin 3 → Bool
  words : Fin 2 → List Bool
  available : Bool

def read (s : State) (i : Fin 3) : State :=
  { s with
    before := s.before ++ BooleanMachine.copied s.input
    input := BooleanMachine.suffix s.input
    flags := Function.update s.flags i (SourceBitRead.value s.input)
    available := BooleanMachine.accepted s.input }

def load (s : State) (j : Fin 2) : State :=
  { s with
    before := s.before ++ (NaturalRawControl.scan s.input).taken
    input := (NaturalRawControl.scan s.input).rest
    words := Function.update s.words j (NaturalRawControl.scan s.input).bits }

def field (s : State) (i : Fin 3) (j : Fin 2) : State :=
  let t := read s i
  if t.flags i then load t j else t

def moveNatural (s : State) : State :=
  { s with
    before := s.before ++ (NaturalRawControl.scan s.input).taken
    input := (NaturalRawControl.scan s.input).rest }

def tailState (s : State) : MarkedNaturalControl.State := ⟨s.before, s.input, s.available⟩

def tailRun (fuel : ℕ) (s : State) : State :=
  let t := MarkedNaturalControl.run fuel (tailState s)
  { s with before := t.before, input := t.input, available := t.active }

def overflow (fuel : ℕ) (s : State) : State :=
  if s.flags 2 then tailRun fuel (moveNatural s) else s

def third (fuel : ℕ) (s : State) : State := overflow fuel (read s 2)

def second (s : State) : State := if s.flags 0 then field s 1 1 else s

def last (fuel : ℕ) (s : State) : State :=
  if s.flags 0 then if s.flags 1 then third fuel s else s else s

def parse (fuel : ℕ) (s : State) : State := last fuel (second (field s 0 0))

/-- 0, 1, 2 are retained degrees; 3 denotes a discarded raw monomial. -/
def degree (s : State) : ℕ := if s.flags 0 then if s.flags 1 then if s.flags 2 then 3 else 2 else 1 else 0

theorem read_split (s : State) (i : Fin 3) : (read s i).before ++ (read s i).input = s.before ++ s.input := by
  simp only [read, List.append_assoc, BooleanMachine.consumed_and_suffix]

theorem load_split (s : State) (j : Fin 2) : (load s j).before ++ (load s j).input = s.before ++ s.input := by
  simp only [load, List.append_assoc, NaturalRawControl.split]

theorem prefix_split (s : State) (i : Fin 3) (j : Fin 2) :
    (field s i j).before ++ (field s i j).input = s.before ++ s.input := by
  unfold field
  dsimp only
  split
  · exact (load_split _ _).trans (read_split s i)
  · exact read_split s i

theorem moveNatural_split (s : State) : (moveNatural s).before ++ (moveNatural s).input = s.before ++ s.input := by
  simp only [moveNatural, List.append_assoc, NaturalRawControl.split]

theorem tailRun_split (fuel : ℕ) (s : State) : (tailRun fuel s).before ++ (tailRun fuel s).input = s.before ++ s.input := by
  have h : ∀ n, (MarkedNaturalControl.run n (tailState s)).before ++ (MarkedNaturalControl.run n (tailState s)).input =
      s.before ++ s.input := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (MarkedNaturalControl.step_split _).trans ih
  exact h fuel

theorem overflow_split (fuel : ℕ) (s : State) : (overflow fuel s).before ++ (overflow fuel s).input = s.before ++ s.input := by
  unfold overflow
  split
  · exact (tailRun_split _ _).trans (moveNatural_split s)
  · rfl

theorem third_split (fuel : ℕ) (s : State) : (third fuel s).before ++ (third fuel s).input = s.before ++ s.input :=
  (overflow_split _ _).trans (read_split s 2)

theorem second_split (s : State) : (second s).before ++ (second s).input = s.before ++ s.input := by
  unfold second
  split
  · exact prefix_split _ _ _
  · rfl

theorem last_split (fuel : ℕ) (s : State) : (last fuel s).before ++ (last fuel s).input = s.before ++ s.input := by
  unfold last
  split
  · split
    · exact third_split _ _
    · rfl
  · rfl

theorem parse_split (fuel : ℕ) (s : State) : (parse fuel s).before ++ (parse fuel s).input = s.before ++ s.input :=
  (last_split _ _).trans ((second_split _).trans (prefix_split _ _ _))

theorem read_length (s : State) (i : Fin 3) : (read s i).input.length ≤ s.input.length := by
  change (BooleanMachine.suffix s.input).length ≤ s.input.length
  cases s.input <;> simp [BooleanMachine.suffix]

theorem load_length (s : State) (j : Fin 2) : (load s j).input.length ≤ s.input.length := by
  have h := congrArg List.length (NaturalRawControl.split s.input)
  simp only [List.length_append] at h
  change (NaturalRawControl.scan s.input).rest.length ≤ s.input.length
  omega

theorem prefix_length (s : State) (i : Fin 3) (j : Fin 2) : (field s i j).input.length ≤ s.input.length := by
  unfold field
  dsimp only
  split
  · exact (load_length _ _).trans (read_length s i)
  · exact read_length s i

theorem moveNatural_length (s : State) : (moveNatural s).input.length ≤ s.input.length := load_length s 0

theorem tailRun_length (fuel : ℕ) (s : State) : (tailRun fuel s).input.length ≤ s.input.length :=
  MarkedNaturalControl.run_length fuel (tailState s)

theorem overflow_length (fuel : ℕ) (s : State) : (overflow fuel s).input.length ≤ s.input.length := by
  unfold overflow
  split
  · exact (tailRun_length _ _).trans (moveNatural_length s)
  · exact le_rfl

theorem third_length (fuel : ℕ) (s : State) : (third fuel s).input.length ≤ s.input.length :=
  (overflow_length _ _).trans (read_length s 2)

theorem second_length (s : State) : (second s).input.length ≤ s.input.length := by
  unfold second
  split
  · exact prefix_length _ _ _
  · exact le_rfl

theorem last_length (fuel : ℕ) (s : State) : (last fuel s).input.length ≤ s.input.length := by
  unfold last
  split
  · split
    · exact third_length _ _
    · exact le_rfl
  · exact le_rfl

theorem parse_length (fuel : ℕ) (s : State) : (parse fuel s).input.length ≤ s.input.length :=
  (last_length _ _).trans ((second_length _).trans (prefix_length _ _ _))

def expected (s : State) (items : List ℕ) (suffix : List Bool) : State :=
  let base := { s with before := s.before ++ MarkedNaturalControl.code items, input := suffix, available := true }
  match items with
  | [] => { base with
      flags := Function.update s.flags 0 false }
  | [a] => { base with
      flags := Function.update (Function.update s.flags 0 true) 1 false
      words := Function.update s.words 0 a.bits }
  | [a, b] => { base with
      flags := Function.update (Function.update (Function.update s.flags 0 true) 1 true) 2 false
      words := Function.update (Function.update s.words 0 a.bits) 1 b.bits }
  | a :: b :: _ :: _ => { base with
      flags := fun _ => true
      words := Function.update (Function.update s.words 0 a.bits) 1 b.bits, available := false }

theorem value_true_accepted (input : List Bool) (h : SourceBitRead.value input = true) :
    BooleanMachine.accepted input = true := by
  cases input with
  | nil => simp [SourceBitRead.value] at h
  | cons b rest => rfl

theorem parse_code (fuel : ℕ) (s : State) (items : List ℕ) (suffix : List Bool)
    (hf : items.length + 1 ≤ fuel) :
    parse fuel { s with input := MarkedNaturalControl.code items ++ suffix } = expected s items suffix := by
  rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [parse, last, second, field, read, expected, MarkedNaturalControl.code,
      RowWordCodec.marked, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix, BooleanMachine.accepted]
  · simp [parse, last, second, field, read, load, expected, MarkedNaturalControl.code,
      RowWordCodec.marked, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix, BooleanMachine.accepted,
      NaturalRawControl.natural, List.append_assoc]
  · simp [parse, last, second, third, overflow, field, read, load, expected, MarkedNaturalControl.code,
      RowWordCodec.marked, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix, BooleanMachine.accepted,
      NaturalRawControl.natural, List.append_assoc]
  · have hr : rest.length + 1 ≤ fuel := by simp only [List.length_cons] at hf; omega
    have he : Function.update (Function.update (Function.update s.flags 0 true) 1 true) 2 true = fun _ => true := by
      funext i
      fin_cases i <;> rfl
    have hrun (before : List Bool) := MarkedNaturalControl.run_code fuel rest hr before suffix
    simp only [MarkedNaturalControl.code] at hrun
    simp [parse, last, second, third, overflow, field, read, load, moveNatural, tailRun, tailState,
      expected, MarkedNaturalControl.code, RowWordCodec.marked, SourceBitRead.value, BooleanMachine.copied,
      BooleanMachine.suffix, BooleanMachine.accepted, NaturalRawControl.natural, List.append_assoc,
      hrun, he]

theorem expected_degree (s : State) (items : List ℕ) (suffix : List Bool) :
    degree (expected s items suffix) = min items.length 3 := by
  rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [expected, degree]

end JointThermoComplexity.Complexity.MonomialPrefixControl

#print axioms JointThermoComplexity.Complexity.MonomialPrefixControl.parse_split
#print axioms JointThermoComplexity.Complexity.MonomialPrefixControl.parse_length
#print axioms JointThermoComplexity.Complexity.MonomialPrefixControl.parse_code
#print axioms JointThermoComplexity.Complexity.MonomialPrefixControl.expected_degree
