module
public import proofs.JointThermoComplexity.Complexity.RealSyntaxSize

set_option autoImplicit false
@[expose] public section

/-! Canonical source term tokens. Literal values and range-checked variable
references use the independent binary codec; no term subtree is parsed here. -/

namespace JointThermoComplexity.Complexity.SourceTermScan
open RealSyntax BitCodec

inductive Head (n : ℕ) where
  | int : ℤ → Head n
  | var : Fin n → Head n
  | add | mul | neg : Head n
  deriving DecidableEq

variable {n : ℕ}

def Head.children : Head n → ℕ
  | .int _ | .var _ => 0
  | .add | .mul => 2
  | .neg => 1

def Head.code : Head n → List Bool
  | .int z => [false, false, false] ++ integerCode z
  | .var i => [false, false, true] ++ naturalCode i.val
  | .add => [false, true, false]
  | .mul => [false, true, true]
  | .neg => [true, false, false]

def parseHead (n : ℕ) : List Bool → Option (Head n × List Bool)
  | false :: false :: false :: rest => do
    let (z, tail) ← parseInteger rest
    pure (.int z, tail)
  | false :: false :: true :: rest => do
    let (i, tail) ← parseNatural rest
    if h : i < n then pure (.var ⟨i, h⟩, tail) else none
  | false :: true :: false :: rest => some (.add, rest)
  | false :: true :: true :: rest => some (.mul, rest)
  | true :: false :: false :: rest => some (.neg, rest)
  | _ => none

theorem parseHead_code (h : Head n) (suffix : List Bool) : parseHead n (h.code ++ suffix) = some (h, suffix) := by
  cases h <;> simp [Head.code, parseHead]

theorem parseHead_sound {input suffix : List Bool} {h : Head n}
    (hp : parseHead n input = some (h, suffix)) : input = h.code ++ suffix := by
  cases input with
  | nil => simp [parseHead] at hp
  | cons a input =>
    cases input with
    | nil => cases a <;> simp [parseHead] at hp
    | cons b input =>
      cases input with
      | nil => cases a <;> cases b <;> simp [parseHead] at hp
      | cons c rest =>
        cases a <;> cases b <;> cases c
        · cases hi : parseInteger rest with
          | none => simp [parseHead, hi] at hp
          | some pair =>
            obtain ⟨z, tail⟩ := pair
            simp [parseHead, hi] at hp
            obtain ⟨rfl, rfl⟩ := hp
            rw [parseInteger_sound hi]
            simp [Head.code]
        · cases hi : parseNatural rest with
          | none => simp [parseHead, hi] at hp
          | some pair =>
            obtain ⟨i, tail⟩ := pair
            by_cases hr : i < n
            · simp [parseHead, hi, hr] at hp
              obtain ⟨rfl, rfl⟩ := hp
              rw [parseNatural_sound hi]
              simp [Head.code]
            · simp [parseHead, hi, hr] at hp
        · simp [parseHead] at hp
          obtain ⟨rfl, rfl⟩ := hp
          rfl
        · simp [parseHead] at hp
          obtain ⟨rfl, rfl⟩ := hp
          rfl
        · simp [parseHead] at hp
          obtain ⟨rfl, rfl⟩ := hp
          rfl
        · simp [parseHead] at hp
        · simp [parseHead] at hp
        · simp [parseHead] at hp

theorem head_min_length (h : Head n) : 3 ≤ h.code.length := by
  cases h <;> simp only [Head.code, List.length_append, List.length_cons, List.length_nil] <;> omega

theorem head_child_bound (h : Head n) : h.children ≤ 2 := by cases h <;> simp only [Head.children] <;> omega

theorem parseHead_consumes {input suffix : List Bool} {h : Head n}
    (hp : parseHead n input = some (h, suffix)) : suffix.length + 3 ≤ input.length := by
  rw [parseHead_sound hp, List.length_append]
  have hlen := head_min_length h
  omega

end JointThermoComplexity.Complexity.SourceTermScan

#print axioms JointThermoComplexity.Complexity.SourceTermScan.parseHead_code
#print axioms JointThermoComplexity.Complexity.SourceTermScan.parseHead_sound
#print axioms JointThermoComplexity.Complexity.SourceTermScan.parseHead_consumes
