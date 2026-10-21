module
public import proofs.JointThermoComplexity.Complexity.HeaderControl

set_option autoImplicit false
@[expose] public section

/-! The three consecutive dimension headers, including truncated binary inputs. -/

namespace JointThermoComplexity.Complexity.DimensionHeaders
open HeaderControl

def tail₁ (input : List Bool) : List Bool := suffix input
def tail₂ (input : List Bool) : List Bool := suffix (tail₁ input)
def tail₃ (input : List Bool) : List Bool := suffix (tail₂ input)

def species (input : List Bool) : ℕ := count input
def reactions (input : List Bool) : ℕ := count (tail₁ input)
def cores (input : List Bool) : ℕ := count (tail₂ input)

def accepted (input : List Bool) : Bool := valid input && valid (tail₁ input) && valid (tail₂ input)

def parse (input : List Bool) : Option (ℕ × ℕ × ℕ × List Bool) := do
  let (n, t₁) ← NetworkCodec.dimension.parse input
  let (r, t₂) ← NetworkCodec.dimension.parse t₁
  let (c, t₃) ← NetworkCodec.dimension.parse t₂
  pure (n, r, c, t₃)

theorem parse_eq (input : List Bool) :
    parse input = if accepted input then some (species input, reactions input, cores input, tail₃ input) else none := by
  cases h₀ : valid input <;> cases h₁ : valid (tail₁ input) <;> cases h₂ : valid (tail₂ input) <;>
    simp_all [parse, NetworkCodec.dimension, parseBinders_eq, accepted,
      species, reactions, cores, tail₁, tail₂, tail₃]

theorem invalid_suffix {input : List Bool} (h : valid input = false) : suffix input = [] := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false => simp [valid] at h
    | true => exact ih h

theorem valid_suffix_implies (input : List Bool) (h : valid (suffix input) = true) : valid input = true := by
  cases hv : valid input with
  | false => rw [invalid_suffix hv] at h; simp [valid] at h
  | true => rfl

theorem accepted_eq_last (input : List Bool) : accepted input = valid (tail₂ input) := by
  cases h : valid (tail₂ input) with
  | false => simp [accepted, h]
  | true =>
    have h₁ := valid_suffix_implies (tail₁ input) h
    have h₀ := valid_suffix_implies input h₁
    simp [accepted, h, h₁, h₀]

theorem status_iff_parse (input : List Bool) :
    valid (tail₂ input) = true ↔ ∃ n r c tail, parse input = some (n, r, c, tail) := by
  rw [parse_eq, accepted_eq_last]
  cases valid (tail₂ input) <;> simp

theorem consumed_length (input : List Bool) :
    (copied input).length + (suffix input).length = input.length := by
  have h := congrArg List.length (consumed_and_suffix input)
  simpa only [List.length_append] using h

theorem count_sum_bound (input : List Bool) :
    species input + reactions input + cores input ≤ input.length := by
  have h₀ := consumed_length input
  have h₁ := consumed_length (tail₁ input)
  have h₂ := consumed_length (tail₂ input)
  have hc₀ := count_le_copied input
  have hc₁ := count_le_copied (tail₁ input)
  have hc₂ := count_le_copied (tail₂ input)
  simp only [species, reactions, cores]
  change (copied input).length + (tail₁ input).length = input.length at h₀
  change (copied (tail₁ input)).length + (tail₂ input).length = (tail₁ input).length at h₁
  omega

theorem prefix_and_suffix (input : List Bool) :
    (copied input ++ copied (tail₁ input) ++ copied (tail₂ input)) ++ tail₃ input = input := by
  simp only [List.append_assoc, tail₃, consumed_and_suffix, tail₂, tail₁]

end JointThermoComplexity.Complexity.DimensionHeaders

#print axioms JointThermoComplexity.Complexity.DimensionHeaders.status_iff_parse
#print axioms JointThermoComplexity.Complexity.DimensionHeaders.count_sum_bound
