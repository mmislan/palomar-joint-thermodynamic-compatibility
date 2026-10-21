module
public import proofs.JointThermoComplexity.Complexity.NumericCursor
public import proofs.JointThermoComplexity.Complexity.BooleanVector

set_option autoImplicit false
@[expose] public section

/-!
# Iterated canonical field control

This semantic interface records the already-proved field codecs. It does not
assume a machine runtime. The numeric-array machine proof separately uses the
concrete checked field scanners and their actual transition bounds.
-/

namespace JointThermoComplexity.Complexity.FieldControl
open FiniteCodec

variable {α : Type}

structure Control (A : Codec α) where
  taken : List Bool → List Bool
  rest : List Bool → List Bool
  valid : List Bool → Bool
  split : ∀ input, taken input ++ rest input = input
  parsed : ∀ {input tail a}, A.parse input = some (a, tail) → taken input = A.code a ∧ rest input = tail
  accepts : ∀ input, valid input = true ↔ ∃ a tail, A.parse input = some (a, tail)

namespace Control
variable {A : Codec α} (S : Control A)

def tail : ℕ → List Bool → List Bool
  | 0, input => input
  | v + 1, input => tail v (S.rest input)

def copied : ℕ → List Bool → List Bool
  | 0, _ => []
  | v + 1, input => S.taken input ++ copied v (S.rest input)

def accepted : ℕ → List Bool → Bool
  | 0, _ => true
  | v + 1, input => S.valid input && accepted v (S.rest input)

theorem split_batch (v : ℕ) (input : List Bool) : S.copied v input ++ S.tail v input = input := by
  induction v generalizing input with
  | zero => rfl
  | succ v ih => simpa only [copied, tail, List.append_assoc, ih] using S.split input

theorem tail_length_le (v : ℕ) (input : List Bool) : (S.tail v input).length ≤ input.length := by
  have h := congrArg List.length (S.split_batch v input)
  simp only [List.length_append] at h
  omega

theorem tail_succ (v : ℕ) (input : List Bool) : S.tail (v + 1) input = S.rest (S.tail v input) := by
  induction v generalizing input with
  | zero => rfl
  | succ v ih =>
    change S.tail (v + 1) (S.rest input) = S.rest (S.tail v (S.rest input))
    exact ih (S.rest input)

theorem copied_succ (v : ℕ) (input : List Bool) :
    S.copied (v + 1) input = S.copied v input ++ S.taken (S.tail v input) := by
  induction v generalizing input with
  | zero => simp [copied, tail]
  | succ v ih =>
    change S.taken input ++ S.copied (v + 1) (S.rest input) =
      (S.taken input ++ S.copied v (S.rest input)) ++ S.taken (S.tail v (S.rest input))
    rw [ih (S.rest input), List.append_assoc]

theorem accepted_succ (v : ℕ) (input : List Bool) :
    S.accepted (v + 1) input = (S.accepted v input && S.valid (S.tail v input)) := by
  induction v generalizing input with
  | zero => simp [accepted, tail]
  | succ v ih =>
    change (S.valid input && S.accepted (v + 1) (S.rest input)) =
      ((S.valid input && S.accepted v (S.rest input)) && S.valid (S.tail v (S.rest input)))
    rw [ih (S.rest input), Bool.and_assoc]

theorem accepted_iff (v : ℕ) (input : List Bool) :
    S.accepted v input = true ↔ ∃ f rest, (finiteFunction A v).parse input = some (f, rest) := by
  change S.accepted v input = true ↔ ∃ f rest, parseFunction A v input = some (f, rest)
  induction v generalizing input with
  | zero => simp [accepted, parseFunction]
  | succ v ih =>
    cases hp : A.parse input with
    | none =>
      have hv : S.valid input ≠ true := by
        intro h
        obtain ⟨a, rest, ha⟩ := (S.accepts input).mp h
        simp [hp] at ha
      simp [accepted, hv, parseFunction, hp]
    | some pair =>
      obtain ⟨a, rest⟩ := pair
      have hv : S.valid input = true := (S.accepts input).mpr ⟨a, rest, hp⟩
      have hr := (S.parsed hp).2
      cases hf : parseFunction A v rest with
      | none =>
        have hbad : S.accepted v rest ≠ true := by
          intro h
          obtain ⟨f, suffix, hparse⟩ := (ih rest).mp h
          simp [hf] at hparse
        simp [accepted, hv, hr, hbad, parseFunction, hp, hf]
      | some pair =>
        obtain ⟨f, suffix⟩ := pair
        have hgood : S.accepted v rest = true := (ih rest).mpr ⟨f, suffix, hf⟩
        simp [accepted, hv, hr, hgood, parseFunction, hp, hf]

theorem parsed_batch {v : ℕ} {input rest : List Bool} {f : Fin v → α}
    (h : (finiteFunction A v).parse input = some (f, rest)) :
    S.copied v input = (finiteFunction A v).code f ∧ S.tail v input = rest := by
  change parseFunction A v input = some (f, rest) at h
  induction v generalizing input rest with
  | zero =>
    simp only [parseFunction, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨rfl, h.2⟩
  | succ v ih =>
    cases hp : A.parse input with
    | none => simp [parseFunction, hp] at h
    | some pair =>
      obtain ⟨a, next⟩ := pair
      cases ht : parseFunction A v next with
      | none => simp [parseFunction, hp, ht] at h
      | some pair =>
        obtain ⟨g, suffix⟩ := pair
        simp [parseFunction, hp, ht] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hc, hr⟩ := S.parsed hp
        obtain ⟨hpc, hpt⟩ := ih ht
        simp only [copied, tail, hc, hr, hpc, hpt, finiteFunction, functionCode, Fin.cons_zero, Fin.cons_succ]
        trivial

end Control

def natural : Control FiniteCodec.natural where
  taken := PayloadControl.copied .empty
  rest := NumericCursor.naturalRest
  valid := NaturalMachineParser.accepted false
  split := NumericCursor.natural_split
  parsed := NumericCursor.natural_parsed
  accepts input := by
    simp [NaturalMachineParser.accepted, FiniteCodec.natural, Option.isSome_iff_exists, Prod.exists]

def positive : Control FiniteCodec.positive where
  taken := PayloadControl.copied .empty
  rest := NumericCursor.naturalRest
  valid := NaturalMachineParser.accepted true
  split := NumericCursor.natural_split
  parsed := NumericCursor.positive_parsed
  accepts input := by
    simp [NaturalMachineParser.accepted, Option.isSome_iff_exists, Prod.exists]

def integer : Control FiniteCodec.integer where
  taken := IntegerMachineRun.copied
  rest := NumericCursor.integerRest
  valid := NaturalMachineParser.integerAccepted
  split := NumericCursor.integer_split
  parsed := NumericCursor.integer_parsed
  accepts := NaturalMachineParser.integerAccepted_iff

end JointThermoComplexity.Complexity.FieldControl

#print axioms JointThermoComplexity.Complexity.FieldControl.Control.accepted_iff
#print axioms JointThermoComplexity.Complexity.FieldControl.Control.parsed_batch
#print axioms JointThermoComplexity.Complexity.FieldControl.positive
