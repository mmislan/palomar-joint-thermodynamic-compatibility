module
public import proofs.JointThermoComplexity.Complexity.NetworkCodec

set_option autoImplicit false
@[expose] public section

/-!
# Unary dimension headers and bounded counters

Only dimension headers and bounded positions use unary counters. This control
does not convert binary exponent or rational-factor values into unary form.
Its status, count and unused suffix are the canonical dimension parser's data.
-/

namespace JointThermoComplexity.Complexity.HeaderControl
open RealSyntax

def count : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: rest => count rest + 1

def valid : List Bool → Bool
  | [] => false
  | false :: _ => true
  | true :: rest => valid rest

def copied : List Bool → List Bool
  | [] => []
  | false :: _ => [false]
  | true :: rest => true :: copied rest

def suffix : List Bool → List Bool
  | [] => []
  | false :: rest => rest
  | true :: rest => suffix rest

theorem parseBinders_eq (input : List Bool) :
    parseBinders input = if valid input then some (count input, suffix input) else none := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false => rfl
    | true =>
      rw [parseBinders, ih]
      cases h : valid rest <;> simp [valid, count, suffix, h]

theorem code_succ (n : ℕ) : binderCode (n + 1) = true :: binderCode n := by
  simp [binderCode, List.replicate_succ]

theorem count_code (n : ℕ) (tail : List Bool) : count (binderCode n ++ tail) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [code_succ, List.cons_append, count, ih]

theorem valid_code (n : ℕ) (tail : List Bool) : valid (binderCode n ++ tail) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [code_succ, List.cons_append, valid] using ih

theorem copied_code (n : ℕ) (tail : List Bool) : copied (binderCode n ++ tail) = binderCode n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [code_succ, List.cons_append, copied, ih]

theorem suffix_code (n : ℕ) (tail : List Bool) : suffix (binderCode n ++ tail) = tail := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [code_succ, List.cons_append, suffix] using ih

theorem count_le_copied (input : List Bool) : count input ≤ (copied input).length := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false => simp [count, copied]
    | true => simpa only [count, copied, List.length_cons] using Nat.add_le_add_right ih 1

theorem copied_length_le (input : List Bool) : (copied input).length ≤ input.length := by
  induction input with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false => simp [copied]
    | true => simpa only [copied, List.length_cons] using Nat.add_le_add_right ih 1

theorem count_le_length (input : List Bool) : count input ≤ input.length :=
  (count_le_copied input).trans (copied_length_le input)

theorem consumed_and_suffix (input : List Bool) : copied input ++ suffix input = input := by
  induction input with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp [copied, suffix, ih]

theorem valid_iff_parse (input : List Bool) :
    valid input = true ↔ ∃ n tail, NetworkCodec.dimension.parse input = some (n, tail) := by
  change valid input = true ↔ ∃ n tail, parseBinders input = some (n, tail)
  rw [parseBinders_eq]
  cases h : valid input <;> simp

theorem valid_copied_code (input : List Bool) (h : valid input = true) :
    copied input = binderCode (count input) := by
  induction input with
  | nil => simp [valid] at h
  | cons bit rest ih =>
    cases bit with
    | false => rfl
    | true =>
      have ht := ih h
      simp only [copied, count, code_succ, ht]

end JointThermoComplexity.Complexity.HeaderControl

#print axioms JointThermoComplexity.Complexity.HeaderControl.valid_iff_parse
#print axioms JointThermoComplexity.Complexity.HeaderControl.count_le_length
