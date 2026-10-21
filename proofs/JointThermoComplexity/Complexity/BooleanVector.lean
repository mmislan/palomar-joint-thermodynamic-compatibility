module
public import proofs.JointThermoComplexity.Complexity.BooleanMachine

set_option autoImplicit false
@[expose] public section

/-! Canonical finite Boolean masks and their exact consumed prefixes. -/

namespace JointThermoComplexity.Complexity.BooleanVector
open FiniteCodec

def accepted (v : ℕ) (input : List Bool) : Bool := decide (v ≤ input.length)

theorem code_length {v : ℕ} (f : Fin v → Bool) :
    ((finiteFunction boolean v).code f).length = v := by
  simp [finiteFunction, functionCode_eq_flatMap, boolean]

theorem parse_iff (v : ℕ) (input : List Bool) :
    (∃ f tail, (finiteFunction boolean v).parse input = some (f, tail)) ↔ v ≤ input.length := by
  change (∃ f tail, parseFunction boolean v input = some (f, tail)) ↔ v ≤ input.length
  induction v generalizing input with
  | zero => simp [parseFunction]
  | succ v ih =>
    cases input with
    | nil => simp [parseFunction, boolean]
    | cons bit rest =>
      have h := ih rest
      simp only [List.length_cons, Nat.add_le_add_iff_right]
      change (∃ f tail, (parseFunction boolean v rest).bind
        (fun pair => some (Fin.cons (n := v) (α := fun _ => Bool) bit pair.1, pair.2)) = some (f, tail)) ↔ v ≤ rest.length
      cases hp : parseFunction boolean v rest with
      | none =>
        simp [hp] at h
        simp [show ¬ v ≤ rest.length by omega]
      | some pair =>
        obtain ⟨f, tail⟩ := pair
        have hv := h.mp ⟨f, tail, hp⟩
        simp [hv]

theorem status_iff (v : ℕ) (input : List Bool) :
    accepted v input = true ↔ ∃ f tail, (finiteFunction boolean v).parse input = some (f, tail) := by
  simp only [accepted, decide_eq_true_eq, parse_iff]

theorem parsed_prefix {v : ℕ} {input tail : List Bool} {f : Fin v → Bool}
    (h : (finiteFunction boolean v).parse input = some (f, tail)) :
    (finiteFunction boolean v).code f = input.take v ∧ tail = input.drop v := by
  have hs := (finiteFunction boolean v).sound h
  rw [hs]
  exact ⟨(List.take_left' (code_length f)).symm, (List.drop_left' (code_length f)).symm⟩

theorem copied_eq_take (input : List Bool) : BooleanMachine.copied input = input.take 1 := by
  cases input <;> rfl

theorem suffix_eq_drop (input : List Bool) : BooleanMachine.suffix input = input.drop 1 := by
  cases input <;> rfl

theorem copied_step (input : List Bool) (i : ℕ) :
    input.take i ++ BooleanMachine.copied (input.drop i) = input.take (i + 1) := by
  rw [copied_eq_take]
  exact List.take_add.symm

theorem suffix_step (input : List Bool) (i : ℕ) :
    BooleanMachine.suffix (input.drop i) = input.drop (i + 1) := by
  rw [suffix_eq_drop, List.drop_drop]

theorem accepted_length (input : List Bool) : BooleanMachine.accepted input = decide (0 < input.length) := by
  cases input <;> simp [BooleanMachine.accepted]

theorem accepted_step (input : List Bool) (i : ℕ) :
    BooleanMachine.accepted (input.drop i) = accepted (i + 1) input := by
  rw [accepted_length, List.length_drop]
  have h : 0 < input.length - i ↔ i + 1 ≤ input.length := by omega
  simp only [h, accepted]

end JointThermoComplexity.Complexity.BooleanVector

#print axioms JointThermoComplexity.Complexity.BooleanVector.status_iff
#print axioms JointThermoComplexity.Complexity.BooleanVector.parsed_prefix
