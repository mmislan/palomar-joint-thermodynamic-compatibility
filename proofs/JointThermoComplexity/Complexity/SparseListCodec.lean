module
public import proofs.JointThermoComplexity.Complexity.FiniteCodec
public import Mathlib.Data.Nat.Size

set_option autoImplicit false
@[expose] public section

/-! # Faithful finite-index and marked-list binary codecs

Lists use one true marker per entry and one false terminator. The parser has
fuel bounded by input length, even for malformed words or empty entry codes.
The unary natural codec is used only for the polynomial's declared arity.
-/

namespace JointThermoComplexity.Complexity.SparseListCodec
open FiniteCodec BitCodec
variable {α : Type}

def unaryCode : ℕ → List Bool
  | 0 => [false]
  | n + 1 => true :: unaryCode n

def parseUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, suffix) ← parseUnary rest
      pure (n + 1, suffix)

theorem parseUnary_code (n : ℕ) (suffix : List Bool) : parseUnary (unaryCode n ++ suffix) = some (n, suffix) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryCode, parseUnary, ih]

theorem parseUnary_sound {input suffix : List Bool} {n : ℕ}
    (h : parseUnary input = some (n, suffix)) : input = unaryCode n ++ suffix := by
  induction input generalizing n suffix with
  | nil => simp [parseUnary] at h
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [parseUnary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | true =>
      cases hr : parseUnary rest with
      | none => simp [parseUnary, hr] at h
      | some pair =>
        obtain ⟨k, tail⟩ := pair
        simp [parseUnary, hr] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa only [unaryCode, List.cons_append] using congrArg (List.cons true) (ih hr)

@[simp] theorem unaryCode_length (n : ℕ) : (unaryCode n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unaryCode, ih]

def unary : Codec ℕ := ⟨unaryCode, parseUnary, parseUnary_code, parseUnary_sound⟩

def finite (n : ℕ) : Codec (Fin n) where
  code i := naturalCode i.val
  parse input := do
    let (i, rest) ← parseNatural input
    if h : i < n then pure (⟨i, h⟩, rest) else none
  roundtrip := by
    intro i suffix
    simp [parseNatural_code, i.isLt]
  sound := by
    intro input i suffix h
    cases hp : parseNatural input with
    | none => simp [hp] at h
    | some pair =>
      obtain ⟨j, rest⟩ := pair
      simp only [hp] at h
      change (if hj : j < n then some ((⟨j, hj⟩ : Fin n), rest) else none) = some (i, suffix) at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hi, rfl⟩ := h
        have hv : j = i.val := congrArg Fin.val hi
        simpa only [hv] using parseNatural_sound hp
      · simp at h

theorem finite_code_length (n : ℕ) (i : Fin n) : ((finite n).code i).length ≤ 2 * n + 1 := by
  change (naturalCode i.val).length ≤ _
  rw [naturalCode_length]
  have hbits : i.val.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (i.isLt.trans (Nat.lt_two_pow_self : n < 2 ^ n))
  omega

def listCode (A : Codec α) : List α → List Bool
  | [] => [false]
  | a :: xs => true :: (A.code a ++ listCode A xs)

def parseList (A : Codec α) : ℕ → List Bool → Option (List α × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
      let (a, tail) ← A.parse rest
      let (xs, suffix) ← parseList A fuel tail
      pure (a :: xs, suffix)

theorem parseList_code (A : Codec α) (xs : List α) (suffix : List Bool) (fuel : ℕ)
    (hf : xs.length + 1 ≤ fuel) : parseList A fuel (listCode A xs ++ suffix) = some (xs, suffix) := by
  induction xs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ fuel => rfl
  | cons a xs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hf' : xs.length + 1 ≤ fuel := by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hf
      have ht := ih fuel hf'
      simp [listCode, List.append_assoc, parseList, A.roundtrip, ht]

theorem parseList_sound (A : Codec α) {fuel : ℕ} {input suffix : List Bool} {xs : List α}
    (h : parseList A fuel input = some (xs, suffix)) : input = listCode A xs ++ suffix := by
  induction fuel generalizing input xs suffix with
  | zero => simp [parseList] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [parseList] at h
    | cons b rest =>
      cases b with
      | false =>
        simp only [parseList, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      | true =>
        cases ha : A.parse rest with
        | none => simp [parseList, ha] at h
        | some pair =>
          obtain ⟨a, tail⟩ := pair
          cases hx : parseList A fuel tail with
          | none => simp [parseList, ha, hx] at h
          | some pair =>
            obtain ⟨ys, ending⟩ := pair
            simp [parseList, ha, hx] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [A.sound ha, ih hx]
            simp only [listCode, List.cons_append, List.append_assoc]

theorem listCode_length (A : Codec α) (xs : List α) :
    (listCode A xs).length = xs.length + 1 + (xs.map (fun a => (A.code a).length)).sum := by
  induction xs with
  | nil => simp [listCode]
  | cons a xs ih =>
    simp only [listCode, List.length_cons, List.length_append, List.map_cons, List.sum_cons]
    rw [ih]
    omega

theorem listCode_length_le (A : Codec α) (xs : List α) (B : ℕ)
    (hB : ∀ a ∈ xs, (A.code a).length ≤ B) : (listCode A xs).length ≤ xs.length * (B + 1) + 1 := by
  induction xs with
  | nil => simp [listCode]
  | cons a xs ih =>
    have ha := hB a List.mem_cons_self
    have ht := ih (fun b hb => hB b (List.mem_cons_of_mem a hb))
    simp only [listCode, List.length_cons, List.length_append, Nat.add_mul, Nat.one_mul]
    omega

def list (A : Codec α) : Codec (List α) where
  code := listCode A
  parse input := parseList A (input.length + 1) input
  roundtrip := by
    intro xs suffix
    apply parseList_code
    have h := listCode_length A xs
    simp only [List.length_append]
    omega
  sound := by
    intro input xs suffix h
    exact parseList_sound A h

end JointThermoComplexity.Complexity.SparseListCodec

#print axioms JointThermoComplexity.Complexity.SparseListCodec.parseUnary_sound
#print axioms JointThermoComplexity.Complexity.SparseListCodec.finite
#print axioms JointThermoComplexity.Complexity.SparseListCodec.parseList_code
#print axioms JointThermoComplexity.Complexity.SparseListCodec.parseList_sound
#print axioms JointThermoComplexity.Complexity.SparseListCodec.listCode_length_le
