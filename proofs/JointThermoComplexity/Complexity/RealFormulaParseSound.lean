module
public import proofs.JointThermoComplexity.Complexity.RealTermParseSound
public import proofs.JointThermoComplexity.Complexity.SparseListCodec

set_option autoImplicit false
@[expose] public section

/-! # Exact source formula/binder/sentence decoding and input length

Every successful sentence decode is the original canonical word. Thus bounds
in canonical sentence length apply to the actual successfully parsed input.
-/

namespace JointThermoComplexity.Complexity.RealSyntax

theorem parseFormula_sound (n fuel : ℕ) {input suffix : List Bool} {p : Formula n}
    (h : parseFormula n fuel input = some (p, suffix)) : input = p.code ++ suffix := by
  induction fuel generalizing input p suffix with
  | zero => simp [parseFormula] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [parseFormula] at h
    | cons a input =>
      cases input with
      | nil => cases a <;> simp [parseFormula] at h
      | cons b input =>
        cases input with
        | nil => cases a <;> cases b <;> simp [parseFormula] at h
        | cons c rest =>
          cases a <;> cases b <;> cases c
          · simp only [parseFormula, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
          · simp only [parseFormula, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
          · cases h1 : parseTerm n fuel rest with
            | none => simp [parseFormula, h1] at h
            | some pair =>
              obtain ⟨t1, middle⟩ := pair
              cases h2 : parseTerm n fuel middle with
              | none => simp [parseFormula, h1, h2] at h
              | some pair =>
                obtain ⟨t2, tail⟩ := pair
                simp [parseFormula, h1, h2] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [parseTerm_sound n fuel h1, parseTerm_sound n fuel h2]
                simp [Formula.code, List.append_assoc]
          · cases h1 : parseTerm n fuel rest with
            | none => simp [parseFormula, h1] at h
            | some pair =>
              obtain ⟨t1, middle⟩ := pair
              cases h2 : parseTerm n fuel middle with
              | none => simp [parseFormula, h1, h2] at h
              | some pair =>
                obtain ⟨t2, tail⟩ := pair
                simp [parseFormula, h1, h2] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [parseTerm_sound n fuel h1, parseTerm_sound n fuel h2]
                simp [Formula.code, List.append_assoc]
          · cases h1 : parseFormula n fuel rest with
            | none => simp [parseFormula, h1] at h
            | some pair =>
              obtain ⟨p1, middle⟩ := pair
              cases h2 : parseFormula n fuel middle with
              | none => simp [parseFormula, h1, h2] at h
              | some pair =>
                obtain ⟨p2, tail⟩ := pair
                simp [parseFormula, h1, h2] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [ih h1, ih h2]
                simp [Formula.code, List.append_assoc]
          · cases h1 : parseFormula n fuel rest with
            | none => simp [parseFormula, h1] at h
            | some pair =>
              obtain ⟨p1, middle⟩ := pair
              cases h2 : parseFormula n fuel middle with
              | none => simp [parseFormula, h1, h2] at h
              | some pair =>
                obtain ⟨p2, tail⟩ := pair
                simp [parseFormula, h1, h2] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [ih h1, ih h2]
                simp [Formula.code, List.append_assoc]
          · simp [parseFormula] at h
          · simp [parseFormula] at h

theorem parseFormula_consumed_length (n fuel : ℕ) {input suffix : List Bool} {p : Formula n}
    (h : parseFormula n fuel input = some (p, suffix)) : p.code.length + suffix.length = input.length := by
  rw [parseFormula_sound n fuel h, List.length_append]

theorem binderCode_eq_unaryCode (n : ℕ) : binderCode n = SparseListCodec.unaryCode n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binderCode, List.replicate_succ, List.cons_append, SparseListCodec.unaryCode]
    exact congrArg (List.cons true) ih

theorem parseBinders_eq_parseUnary (input : List Bool) : parseBinders input = SparseListCodec.parseUnary input := by
  induction input with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => rfl
    | true => simp only [parseBinders, SparseListCodec.parseUnary, ih]

theorem parseBinders_sound {input suffix : List Bool} {n : ℕ}
    (h : parseBinders input = some (n, suffix)) : input = binderCode n ++ suffix := by
  rw [parseBinders_eq_parseUnary] at h
  simpa only [← binderCode_eq_unaryCode] using SparseListCodec.parseUnary_sound h

theorem decodeSentence_sound {input : List Bool} {s : Sentence}
    (h : decodeSentence input = some s) : input = s.code := by
  cases hb : parseBinders input with
  | none => simp [decodeSentence, hb] at h
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    cases hp : parseFormula n rest.length rest with
    | none => simp [decodeSentence, hb, hp] at h
    | some pair =>
      obtain ⟨p, tail⟩ := pair
      by_cases ht : tail = []
      · subst tail
        simp [decodeSentence, hb, hp] at h
        subst s
        rw [parseBinders_sound hb, parseFormula_sound n rest.length hp]
        simp only [Sentence.code, List.append_nil]
      · simp [decodeSentence, hb, hp, ht] at h

theorem decodeSentence_some_iff (input : List Bool) (s : Sentence) : decodeSentence input = some s ↔ input = s.code := by
  constructor
  · exact decodeSentence_sound
  · intro h
    rw [h]
    exact decodeSentence_code s

theorem decoded_code_length {input : List Bool} {s : Sentence} (h : decodeSentence input = some s) :
    s.code.length = input.length := by rw [decodeSentence_sound h]

end JointThermoComplexity.Complexity.RealSyntax

#print axioms JointThermoComplexity.Complexity.RealSyntax.parseFormula_sound
#print axioms JointThermoComplexity.Complexity.RealSyntax.parseBinders_sound
#print axioms JointThermoComplexity.Complexity.RealSyntax.decodeSentence_sound
#print axioms JointThermoComplexity.Complexity.RealSyntax.decodeSentence_some_iff
#print axioms JointThermoComplexity.Complexity.RealSyntax.decoded_code_length
