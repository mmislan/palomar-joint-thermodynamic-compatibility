module
public import proofs.JointThermoComplexity.Complexity.RealFormulaParseSound

set_option autoImplicit false
@[expose] public section

/-! Total source normalization preserves the independent language, including malformed inputs. -/

namespace JointThermoComplexity.Complexity.SourceNormalization
open RealSyntax

def falseSentence : Sentence := ⟨0, .falsity⟩

theorem falseSentence_unsatisfiable : ¬falseSentence.Satisfiable := by
  rintro ⟨ρ, hρ⟩
  exact hρ

theorem falseSentence_code_length : falseSentence.code.length = 4 := rfl

def normalize (input : List Bool) : Sentence := (decodeSentence input).getD falseSentence

theorem normalize_of_some {input : List Bool} {s : Sentence}
    (h : decodeSentence input = some s) : normalize input = s := by simp only [normalize, h, Option.getD_some]

theorem normalize_of_none {input : List Bool} (h : decodeSentence input = none) :
    normalize input = falseSentence := by simp only [normalize, h, Option.getD_none]

theorem normalize_code (s : Sentence) : normalize s.code = s := normalize_of_some (decodeSentence_code s)

theorem normalize_satisfiable_iff (input : List Bool) : (normalize input).Satisfiable ↔ input ∈ ETR := by
  change (normalize input).Satisfiable ↔ ∃ s, decodeSentence input = some s ∧ s.Satisfiable
  cases hd : decodeSentence input with
  | none =>
    rw [normalize_of_none hd]
    constructor
    · intro h; exact False.elim (falseSentence_unsatisfiable h)
    · rintro ⟨s, hs, _⟩; cases hs
  | some s =>
    rw [normalize_of_some hd]
    constructor
    · intro h; exact ⟨s, rfl, h⟩
    · rintro ⟨t, ht, hs⟩
      cases ht
      exact hs

theorem normalize_code_length (input : List Bool) : (normalize input).code.length ≤ input.length + 4 := by
  cases hd : decodeSentence input with
  | none => rw [normalize_of_none hd, falseSentence_code_length]; omega
  | some s => rw [normalize_of_some hd, decoded_code_length hd]; omega

end JointThermoComplexity.Complexity.SourceNormalization

#print axioms JointThermoComplexity.Complexity.SourceNormalization.normalize_satisfiable_iff
#print axioms JointThermoComplexity.Complexity.SourceNormalization.normalize_code_length
