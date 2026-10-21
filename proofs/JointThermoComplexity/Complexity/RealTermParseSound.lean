module
public import proofs.JointThermoComplexity.Complexity.RealSyntax

set_option autoImplicit false
@[expose] public section

/-! # Exact consumed prefix of every successful independent term parse -/

namespace JointThermoComplexity.Complexity.RealSyntax
open BitCodec

theorem parseTerm_sound (n fuel : ℕ) {input suffix : List Bool} {t : Term n}
    (h : parseTerm n fuel input = some (t, suffix)) : input = t.code ++ suffix := by
  induction fuel generalizing input t suffix with
  | zero => simp [parseTerm] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [parseTerm] at h
    | cons a input =>
      cases input with
      | nil => cases a <;> simp [parseTerm] at h
      | cons b input =>
        cases input with
        | nil => cases a <;> cases b <;> simp [parseTerm] at h
        | cons c rest =>
          cases a <;> cases b <;> cases c
          · cases hz : parseInteger rest with
            | none => simp [parseTerm, hz] at h
            | some pair =>
              obtain ⟨z, tail⟩ := pair
              simp [parseTerm, hz] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [parseInteger_sound hz]
              rfl
          · cases hp : parseNatural rest with
            | none => simp [parseTerm, hp] at h
            | some pair =>
              obtain ⟨i, tail⟩ := pair
              by_cases hi : i < n
              · simp [parseTerm, hp, hi] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [parseNatural_sound hp]
                rfl
              · simp [parseTerm, hp, hi] at h
          · cases h1 : parseTerm n fuel rest with
            | none => simp [parseTerm, h1] at h
            | some pair =>
              obtain ⟨s1, middle⟩ := pair
              cases h2 : parseTerm n fuel middle with
              | none => simp [parseTerm, h1, h2] at h
              | some pair =>
                obtain ⟨s2, tail⟩ := pair
                simp [parseTerm, h1, h2] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [ih h1, ih h2]
                simp [Term.code, List.append_assoc]
          · cases h1 : parseTerm n fuel rest with
            | none => simp [parseTerm, h1] at h
            | some pair =>
              obtain ⟨s1, middle⟩ := pair
              cases h2 : parseTerm n fuel middle with
              | none => simp [parseTerm, h1, h2] at h
              | some pair =>
                obtain ⟨s2, tail⟩ := pair
                simp [parseTerm, h1, h2] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [ih h1, ih h2]
                simp [Term.code, List.append_assoc]
          · cases h1 : parseTerm n fuel rest with
            | none => simp [parseTerm, h1] at h
            | some pair =>
              obtain ⟨s1, tail⟩ := pair
              simp [parseTerm, h1] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [ih h1]
              rfl
          · simp [parseTerm] at h
          · simp [parseTerm] at h
          · simp [parseTerm] at h

theorem parseTerm_consumed_length (n fuel : ℕ) {input suffix : List Bool} {t : Term n}
    (h : parseTerm n fuel input = some (t, suffix)) : t.code.length + suffix.length = input.length := by
  rw [parseTerm_sound n fuel h, List.length_append]

end JointThermoComplexity.Complexity.RealSyntax

#print axioms JointThermoComplexity.Complexity.RealSyntax.parseTerm_sound
#print axioms JointThermoComplexity.Complexity.RealSyntax.parseTerm_consumed_length
