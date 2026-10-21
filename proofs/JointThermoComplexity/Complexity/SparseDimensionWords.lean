module
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryEmit

set_option autoImplicit false
@[expose] public section

/-! Exact unary header words in the concrete literal-network order. -/

namespace JointThermoComplexity.Complexity.SparseDimensionWords
open RealSyntax

def arityWord (boxed : Bool) : List Bool := if boxed then [true] else [true, true]
def speciesPad (boxed : Bool) : List Bool := List.replicate (if boxed then 2 else 3) true ++ [false]
def reactionPad : List Bool := [true, true, true, true, false]
def species (boxed : Bool) (n t : ℕ) : ℕ := if boxed then n + 2 * t + 2 else 2 * n + 2 * t + 3
def reactions (t : ℕ) : ℕ := 2 * t + 4
def header (boxed : Bool) (n t : ℕ) : List Bool :=
  binderCode (species boxed n t) ++ binderCode (reactions t) ++ binderCode 2

theorem copies_replicate (k n : ℕ) :
    RepeatedOutput.copies (List.replicate k true) n = List.replicate (n * k) true := by
  induction n with
  | zero => simp only [RepeatedOutput.copies, Nat.zero_mul, List.replicate_zero]
  | succ n ih => rw [RepeatedOutput.copies, ih, ← List.replicate_add, Nat.succ_mul]

theorem species_word (boxed : Bool) (n t : ℕ) :
    (RepeatedOutput.copies (arityWord boxed) n ++ RepeatedOutput.copies [true, true] t) ++ speciesPad boxed =
      binderCode (species boxed n t) := by
  cases boxed
  · change (RepeatedOutput.copies (List.replicate 2 true) n ++ RepeatedOutput.copies (List.replicate 2 true) t) ++
      (List.replicate 3 true ++ [false]) = List.replicate (2 * n + 2 * t + 3) true ++ [false]
    rw [copies_replicate, copies_replicate, ← List.replicate_add, ← List.append_assoc, ← List.replicate_add]
    congr 2
    omega
  · change (RepeatedOutput.copies (List.replicate 1 true) n ++ RepeatedOutput.copies (List.replicate 2 true) t) ++
      (List.replicate 2 true ++ [false]) = List.replicate (n + 2 * t + 2) true ++ [false]
    rw [copies_replicate, copies_replicate, ← List.replicate_add, ← List.append_assoc, ← List.replicate_add]
    congr 2
    omega

theorem reaction_word (t : ℕ) : RepeatedOutput.copies [true, true] t ++ reactionPad = binderCode (reactions t) := by
  change RepeatedOutput.copies (List.replicate 2 true) t ++ (List.replicate 4 true ++ [false]) =
    List.replicate (2 * t + 4) true ++ [false]
  rw [copies_replicate, ← List.append_assoc, ← List.replicate_add]
  congr 2
  omega

theorem arity_length (boxed : Bool) : (arityWord boxed).length ≤ 2 := by cases boxed <;> decide
theorem speciesPad_length (boxed : Bool) : (speciesPad boxed).length ≤ 4 := by cases boxed <;> decide

end JointThermoComplexity.Complexity.SparseDimensionWords

#print axioms JointThermoComplexity.Complexity.SparseDimensionWords.species_word
#print axioms JointThermoComplexity.Complexity.SparseDimensionWords.reaction_word
