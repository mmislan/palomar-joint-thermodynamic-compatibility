module
public import proofs.JointThermoComplexity.Complexity.SmallIntegerStreamRun
public import proofs.JointThermoComplexity.Complexity.SourceSmallLiteralSentence

set_option autoImplicit false
@[expose] public section

/-! Total one-token streaming control; pending terms distinguish formula tags from term tags. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxToken

structure Token where
  taken : List Bool
  rest : List Bool
  output : List Bool
  pending : ℕ
  deriving DecidableEq

def termBody (v : ℕ) (bits input : List Bool) : Token := match SourceTermToken.classify bits with
  | .integer => ⟨SmallIntegerStream.taken input, SmallIntegerStream.rest input, SmallIntegerStream.output input, v⟩
  | .variable => ⟨PayloadControl.copied .empty input, NumericCursor.naturalRest input,
      bits ++ PayloadControl.copied .empty input, v⟩
  | .add | .mul => ⟨[], input, bits, v + 2⟩
  | .neg => ⟨[], input, bits, v + 1⟩
  | .invalid => ⟨[], input, [], v + 1⟩

def formulaBody (bits input : List Bool) : Token := match SourceFormulaScan.classify bits with
  | .eq | .lt => ⟨[], input, bits, 2⟩
  | .invalid => ⟨[], input, [], 0⟩
  | _ => ⟨[], input, bits, 0⟩

def body : ℕ → List Bool → List Bool → Token
  | 0, bits, input => formulaBody bits input
  | v + 1, bits, input => termBody v bits input

def step (pending : ℕ) (input : List Bool) : Token :=
  if SourceTags.accepted input then
    let next := body pending (SourceTermToken.tagBits input) (input.drop 3)
    ⟨input.take 3 ++ next.taken, next.rest, next.output, next.pending⟩
  else ⟨input.take 3, input.drop 3, [], pending⟩

theorem body_split (pending : ℕ) (bits input : List Bool) :
    (body pending bits input).taken ++ (body pending bits input).rest = input := by
  cases pending with
  | zero => cases hk : SourceFormulaScan.classify bits <;> simp only [body, formulaBody, hk, List.nil_append]
  | succ v =>
    cases hk : SourceTermToken.classify bits <;> simp only [body, termBody, hk, List.nil_append]
    · exact SmallIntegerStream.split input
    · exact NumericCursor.natural_split input

theorem split (pending : ℕ) (input : List Bool) : (step pending input).taken ++ (step pending input).rest = input := by
  unfold step
  split
  · rw [List.append_assoc, body_split]
    exact List.take_append_drop 3 input
  · exact List.take_append_drop 3 input

theorem pending_bound (pending : ℕ) (input : List Bool) : (step pending input).pending ≤ pending + 2 := by
  unfold step
  split
  · cases pending with
    | zero => cases hk : SourceFormulaScan.classify (SourceTermToken.tagBits input) <;> simp only [body, formulaBody, hk] <;> omega
    | succ v => cases hk : SourceTermToken.classify (SourceTermToken.tagBits input) <;> simp only [body, termBody, hk] <;> omega
  · exact Nat.le_add_right _ _

theorem input_bound (pending : ℕ) (input : List Bool) : (step pending input).rest.length ≤ input.length := by
  have h := congrArg List.length (split pending input)
  rw [List.length_append] at h
  omega

@[simp] theorem step_empty (pending : ℕ) : step pending [] = ⟨[], [], [], pending⟩ := rfl

theorem tag_step (pending : ℕ) (a b c : Bool) (input : List Bool) :
    step pending (a :: b :: c :: input) =
      ⟨[a, b, c] ++ (body pending [a, b, c] input).taken, (body pending [a, b, c] input).rest,
        (body pending [a, b, c] input).output, (body pending [a, b, c] input).pending⟩ := by
  simp [step, SourceTags.accepted, SourceTermToken.tagBits, SourceBitRead.value]

def headOutput {n : ℕ} : SourceTermScan.Head n → List Bool
  | .int z => (SourceSmallLiterals.integerTerm z : RealSyntax.Term n).code
  | h => h.code

theorem term_head (n v : ℕ) (head : SourceTermScan.Head n) (suffix : List Bool) :
    step (v + 1) (head.code ++ suffix) = ⟨head.code, suffix, headOutput head, v + head.children⟩ := by
  cases head with
  | int z =>
    obtain ⟨ht, hr, ho⟩ := SmallIntegerStream.code_result n z suffix
    simp [SourceTermScan.Head.code, tag_step, body, termBody, SourceTermToken.classify,
      headOutput, SourceTermScan.Head.children, ht, hr, ho]
  | var i =>
    simp [SourceTermScan.Head.code, tag_step, body, termBody, SourceTermToken.classify,
      headOutput, SourceTermScan.Head.children, NumericCursor.natural_copied_code, NumericCursor.natural_rest_code]
  | add | mul | neg =>
    simp [SourceTermScan.Head.code, tag_step, body, termBody, SourceTermToken.classify,
      headOutput, SourceTermScan.Head.children]

end JointThermoComplexity.Complexity.SmallSyntaxToken

#print axioms JointThermoComplexity.Complexity.SmallSyntaxToken.split
#print axioms JointThermoComplexity.Complexity.SmallSyntaxToken.term_head
