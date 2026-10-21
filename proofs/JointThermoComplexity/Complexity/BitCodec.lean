module
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.Int.Basic

set_option autoImplicit false

@[expose] public section

/-!
# Self-delimiting binary integer data

Each payload bit is preceded by `true`; a single `false` ends the payload.
Natural-number payloads are the canonical, little-endian `Nat.bits` list.
The parser preserves the unused suffix and rejects noncanonical payloads.
Signs distinguish nonnegative integers from strictly negative integers, so
negative zero is rejected. These are executable codecs, not runtime theorems.
-/

namespace JointThermoComplexity.Complexity.BitCodec

def encodeBits : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encodeBits bs

def parseBits : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | [true] => none
  | true :: b :: rest => do
      let (payload, suffix) ← parseBits rest
      pure (b :: payload, suffix)

@[simp] theorem parseBits_encodeBits (payload suffix : List Bool) :
    parseBits (encodeBits payload ++ suffix) = some (payload, suffix) := by
  induction payload with
  | nil => rfl
  | cons b bs ih => simp [encodeBits, parseBits, ih]

theorem parseBits_sound {input payload suffix : List Bool}
    (h : parseBits input = some (payload, suffix)) :
    input = encodeBits payload ++ suffix := by
  induction input using parseBits.induct generalizing payload suffix with
  | case1 => simp [parseBits] at h
  | case2 rest =>
    simp only [parseBits, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case3 => simp [parseBits] at h
  | case4 b rest ih =>
    cases hp : parseBits rest with
    | none => simp [parseBits, hp] at h
    | some pair =>
      rcases pair with ⟨bs, tail⟩
      simp [parseBits, hp] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [encodeBits] using congrArg (fun xs => true :: b :: xs) (ih hp)

@[simp] theorem encodeBits_length (payload : List Bool) :
    (encodeBits payload).length = 2 * payload.length + 1 := by
  induction payload with
  | nil => rfl
  | cons b bs ih => simp [encodeBits, ih]; omega

def readBits (payload : List Bool) : ℕ := payload.foldr Nat.bit 0

@[simp] theorem readBits_bits (n : ℕ) : readBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [readBits]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    change Nat.bit b (readBits n.bits) = Nat.bit b n
    rw [ih]

def naturalCode (n : ℕ) : List Bool := encodeBits n.bits

def parseNatural (input : List Bool) : Option (ℕ × List Bool) := do
  let (payload, suffix) ← parseBits input
  let n := readBits payload
  if payload = n.bits then pure (n, suffix) else none

@[simp] theorem parseNatural_code (n : ℕ) (suffix : List Bool) :
    parseNatural (naturalCode n ++ suffix) = some (n, suffix) := by
  simp [parseNatural, naturalCode]

theorem parseNatural_sound {input suffix : List Bool} {n : ℕ}
    (h : parseNatural input = some (n, suffix)) :
    input = naturalCode n ++ suffix := by
  unfold parseNatural at h
  cases hp : parseBits input with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨payload, rest⟩
    simp only [hp] at h
    change (if payload = (readBits payload).bits then
      some (readBits payload, rest) else none) = some (n, suffix) at h
    split at h
    next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [naturalCode, ← hc] using parseBits_sound hp
    next => simp at h

@[simp] theorem naturalCode_length (n : ℕ) :
    (naturalCode n).length = 2 * n.bits.length + 1 := by
  exact encodeBits_length _

theorem naturalCode_append_inj {m n : ℕ} {xs ys : List Bool} :
    naturalCode m ++ xs = naturalCode n ++ ys ↔ m = n ∧ xs = ys := by
  constructor
  · intro h
    have hp := congrArg parseNatural h
    simpa only [parseNatural_code, Option.some.injEq, Prod.mk.injEq] using hp
  · rintro ⟨rfl, rfl⟩
    rfl

theorem naturalCode_injective : Function.Injective naturalCode := by
  intro m n h
  exact (naturalCode_append_inj (xs := []) (ys := []) |>.mp (by simpa using h)).1

def integerCode : ℤ → List Bool
  | .ofNat n => false :: naturalCode n
  | .negSucc n => true :: naturalCode (n + 1)

def parseInteger : List Bool → Option (ℤ × List Bool)
  | [] => none
  | false :: rest => do
      let (n, suffix) ← parseNatural rest
      pure (Int.ofNat n, suffix)
  | true :: rest => do
      let (n, suffix) ← parseNatural rest
      match n with
      | 0 => none
      | k + 1 => pure (Int.negSucc k, suffix)

@[simp] theorem parseInteger_code (z : ℤ) (suffix : List Bool) :
    parseInteger (integerCode z ++ suffix) = some (z, suffix) := by
  cases z <;> simp [integerCode, parseInteger]

theorem parseInteger_sound {input suffix : List Bool} {z : ℤ}
    (h : parseInteger input = some (z, suffix)) :
    input = integerCode z ++ suffix := by
  cases input with
  | nil => simp [parseInteger] at h
  | cons b rest =>
    cases b
    · cases hp : parseNatural rest with
      | none => simp [parseInteger, hp] at h
      | some pair =>
        rcases pair with ⟨n, tail⟩
        simp [parseInteger, hp] at h
        rcases h with ⟨rfl, rfl⟩
        simpa [integerCode] using congrArg (List.cons false) (parseNatural_sound hp)
    · cases hp : parseNatural rest with
      | none => simp [parseInteger, hp] at h
      | some pair =>
        rcases pair with ⟨n, tail⟩
        cases n with
        | zero => simp [parseInteger, hp] at h
        | succ n =>
          simp [parseInteger, hp] at h
          rcases h with ⟨rfl, rfl⟩
          simpa [integerCode] using congrArg (List.cons true) (parseNatural_sound hp)

theorem integerCode_append_inj {z w : ℤ} {xs ys : List Bool} :
    integerCode z ++ xs = integerCode w ++ ys ↔ z = w ∧ xs = ys := by
  constructor
  · intro h
    have hp := congrArg parseInteger h
    simpa only [parseInteger_code, Option.some.injEq, Prod.mk.injEq] using hp
  · rintro ⟨rfl, rfl⟩
    rfl

theorem integerCode_injective : Function.Injective integerCode := by
  intro z w h
  exact (integerCode_append_inj (xs := []) (ys := []) |>.mp (by simpa using h)).1

@[simp] theorem integerCode_length (z : ℤ) :
    (integerCode z).length = 2 * z.natAbs.bits.length + 2 := by
  cases z <;> simp [integerCode, naturalCode_length]

@[simp] theorem parseInteger_negative_zero (suffix : List Bool) :
    parseInteger (true :: (naturalCode 0 ++ suffix)) = none := by
  simp [parseInteger]

end JointThermoComplexity.Complexity.BitCodec

#print axioms JointThermoComplexity.Complexity.BitCodec.parseNatural_code
#print axioms JointThermoComplexity.Complexity.BitCodec.parseNatural_sound
#print axioms JointThermoComplexity.Complexity.BitCodec.parseInteger_code
#print axioms JointThermoComplexity.Complexity.BitCodec.parseInteger_sound
#print axioms JointThermoComplexity.Complexity.BitCodec.integerCode_append_inj
