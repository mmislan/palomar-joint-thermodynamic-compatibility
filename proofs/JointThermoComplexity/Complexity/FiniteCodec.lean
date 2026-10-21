module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
@[expose] public section

/-!
# Canonical finite-data codec components

Every successful parse consumes exactly the code of its returned value and
preserves the unused suffix. Fixed-length finite tables store entries in index
order. Natural payloads and positive denominators remain binary; their numeric
values are not expanded into unary data. No machine runtime is asserted here.
-/

namespace JointThermoComplexity.Complexity.FiniteCodec
open BitCodec

structure Codec (α : Type) where
  code : α → List Bool
  parse : List Bool → Option (α × List Bool)
  roundtrip : ∀ a suffix, parse (code a ++ suffix) = some (a, suffix)
  sound : ∀ {input a suffix}, parse input = some (a, suffix) → input = code a ++ suffix

variable {α β : Type}

def natural : Codec ℕ := ⟨naturalCode, parseNatural, parseNatural_code, parseNatural_sound⟩
def integer : Codec ℤ := ⟨integerCode, parseInteger, parseInteger_code, parseInteger_sound⟩

def boolean : Codec Bool where
  code b := [b]
  parse | [] => none | b :: rest => some (b, rest)
  roundtrip _ _ := rfl
  sound := by
    intro input a suffix h
    cases input with
    | nil => simp at h
    | cons b rest =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

def positive : Codec {a : ℕ // 0 < a} where
  code a := naturalCode a.val
  parse input := do
    let (a, rest) ← parseNatural input
    if h : 0 < a then pure (⟨a, h⟩, rest) else none
  roundtrip := by
    intro a suffix
    simp [parseNatural_code, a.property]
  sound := by
    intro input a suffix h
    cases hp : parseNatural input with
    | none => simp [hp] at h
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      simp only [hp] at h
      change (if hp : 0 < value then some ((⟨value, hp⟩ : {a : ℕ // 0 < a}), rest)
        else none) = some (a, suffix) at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ha, rfl⟩ := h
        have hv : value = a.val := congrArg Subtype.val ha
        simpa only [hv] using parseNatural_sound hp
      · simp at h

def product (A : Codec α) (B : Codec β) : Codec (α × β) where
  code a := A.code a.1 ++ B.code a.2
  parse input := do
    let (a, rest) ← A.parse input
    let (b, suffix) ← B.parse rest
    pure ((a, b), suffix)
  roundtrip := by
    rintro ⟨a, b⟩ suffix
    simp [List.append_assoc, A.roundtrip, B.roundtrip]
  sound := by
    intro input value suffix h
    cases ha : A.parse input with
    | none => simp [ha] at h
    | some pair =>
      obtain ⟨a, rest⟩ := pair
      cases hb : B.parse rest with
      | none => simp [ha, hb] at h
      | some pair =>
        obtain ⟨b, tail⟩ := pair
        simp [ha, hb] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [A.sound ha, B.sound hb, List.append_assoc]

def optional (A : Codec α) : Codec (Option α) where
  code | none => [false] | some a => true :: A.code a
  parse
    | [] => none
    | false :: rest => some (none, rest)
    | true :: rest => do
        let (a, suffix) ← A.parse rest
        pure (some a, suffix)
  roundtrip := by
    intro a suffix
    cases a <;> simp [A.roundtrip]
  sound := by
    intro input value suffix h
    cases input with
    | nil => simp at h
    | cons bit rest =>
      cases bit with
      | false =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      | true =>
        cases ha : A.parse rest with
        | none => simp [ha] at h
        | some pair =>
          obtain ⟨a, tail⟩ := pair
          simp [ha] at h
          obtain ⟨rfl, rfl⟩ := h
          simpa only [List.cons_append] using congrArg (List.cons true) (A.sound ha)

def functionCode (A : Codec α) : {n : ℕ} → (Fin n → α) → List Bool
  | 0, _ => []
  | _ + 1, f => A.code (f 0) ++ functionCode A (fun i => f i.succ)

def parseFunction (A : Codec α) : (n : ℕ) → List Bool → Option ((Fin n → α) × List Bool)
  | 0, input => some (Fin.elim0, input)
  | n + 1, input => do
      let (a, rest) ← A.parse input
      let (f, suffix) ← parseFunction A n rest
      pure (Fin.cons a f, suffix)

theorem parseFunction_code (A : Codec α) {n : ℕ} (f : Fin n → α) (suffix : List Bool) :
    parseFunction A n (functionCode A f ++ suffix) = some (f, suffix) := by
  induction n with
  | zero =>
    have hf : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst f
    rfl
  | succ n ih =>
    simp [functionCode, List.append_assoc, parseFunction, A.roundtrip, ih,
      show Fin.cons (f 0) (fun i => f i.succ) = f from Fin.cons_self_tail f]

theorem parseFunction_sound (A : Codec α) {n : ℕ} {input suffix : List Bool}
    {f : Fin n → α} (h : parseFunction A n input = some (f, suffix)) :
    input = functionCode A f ++ suffix := by
  induction n generalizing input suffix with
  | zero =>
    simp only [parseFunction, Option.some.injEq, Prod.mk.injEq] at h
    simpa only [functionCode, List.nil_append] using h.2
  | succ n ih =>
    cases ha : A.parse input with
    | none => simp [parseFunction, ha] at h
    | some pair =>
      obtain ⟨a, rest⟩ := pair
      cases hf : parseFunction A n rest with
      | none => simp [parseFunction, ha, hf] at h
      | some pair =>
        obtain ⟨g, tail⟩ := pair
        simp [parseFunction, ha, hf] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [A.sound ha, ih hf]
        simp only [functionCode, Fin.cons_zero, Fin.cons_succ, List.append_assoc]

def finiteFunction (A : Codec α) (n : ℕ) : Codec (Fin n → α) :=
  ⟨functionCode A, parseFunction A n, parseFunction_code A, parseFunction_sound A⟩

theorem functionCode_eq_flatMap (A : Codec α) {n : ℕ} (f : Fin n → α) :
    functionCode A f = (List.ofFn f).flatMap A.code := by
  induction n with
  | zero => simp [functionCode]
  | succ n ih => simp [functionCode, List.ofFn_succ, ih]

theorem Codec.code_injective (A : Codec α) : Function.Injective A.code := by
  intro a b h
  have hp := congrArg (fun input => A.parse (input ++ [])) h
  simpa only [A.roundtrip, Option.some.injEq, Prod.mk.injEq, and_true] using hp

theorem Codec.parse_consumed_length (A : Codec α) {input suffix : List Bool} {a : α}
    (h : A.parse input = some (a, suffix)) :
    (A.code a).length + suffix.length = input.length := by
  rw [A.sound h, List.length_append]

end JointThermoComplexity.Complexity.FiniteCodec

#print axioms JointThermoComplexity.Complexity.FiniteCodec.parseFunction_code
#print axioms JointThermoComplexity.Complexity.FiniteCodec.parseFunction_sound
#print axioms JointThermoComplexity.Complexity.FiniteCodec.Codec.code_injective
