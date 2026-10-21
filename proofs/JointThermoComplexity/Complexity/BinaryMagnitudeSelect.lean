module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceEmit
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun
public import proofs.JointThermoComplexity.Complexity.SignedBinaryDifference

set_option autoImplicit false
@[expose] public section

/-! An actual retained sign bit selects the operand order for the nonnegative magnitude scan. -/

namespace JointThermoComplexity.Complexity.BinaryMagnitudeSelect
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceCursor BinaryDifferenceRuntime SignedBinaryDifference

variable {w : ℕ}

def rawMagnitude (xs ys : List Bool) : List Bool :=
  if negative xs ys then (BinaryDifference.subtract ys xs false).1 else (BinaryDifference.subtract xs ys false).1

def machine (left right flag : Fin w) : TM w := FlagBranch.machine flag
  (BinaryDifferenceMachine.machine right left flag true) (BinaryDifferenceMachine.machine left right flag true)

theorem start_swap (left right flag : Fin w) (xs ys : List Bool) (work : Fin w → Tape)
    (h : Start left right flag xs ys work) : Start right left flag ys xs work :=
  ⟨h.safe, h.rhs, h.lhs, h.rhsZero, h.lhsZero, h.flagHead⟩

theorem finish_swap (left right flag : Fin w) (xs ys : List Bool) (work : Fin w → Tape)
    (h : Finish right left flag true ys xs work) : Finish left right flag true xs ys work :=
  ⟨h.safe, h.rhs, h.lhs, h.rhsZero, h.lhsZero, h.flagHead, by simp⟩

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧
        (work flag).read = Γ.ofBool (negative xs ys) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ rawMagnitude xs ys) inp work out ∧
        Finish left right flag true xs ys work ∧ (work flag).read = Γ.ofBool (negative xs ys) ∧ R work)
      (max xs.length ys.length + 3) := by
  let R' : (Fin w → Tape) → Prop := fun work => (work flag).read = Γ.ofBool (negative xs ys) ∧ R work
  have hR' : ∀ work work', (∀ j, j ≠ left → j ≠ right → work' j = work j) → R' work → R' work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw flag sep.flagLeft sep.flagRight] using hf, hR work work' hw hr⟩
  let P : (Fin w → Tape) → Prop := fun work => Start left right flag xs ys work ∧ R' work
  let Q : (Fin w → Tape) → Prop := fun work => Finish left right flag true xs ys work ∧ R' work
  cases hn : negative xs ys with
  | false =>
    have hraw := BinaryDifferenceEmit.hoareTime left right flag sep xs ys before input emitted R' hR'
    have hbranch := FlagBranchRun.no_hoareTime flag
      (BinaryDifferenceMachine.machine right left flag true) (BinaryDifferenceMachine.machine left right flag true)
      before input emitted before input (emitted ++ (BinaryDifference.subtract xs ys false).1)
      P Q (max xs.length ys.length + 1) hraw
    exact hbranch.consequence (by
      rintro inp work out ⟨hc, hp, hf, hr⟩
      exact ⟨⟨hc, hp, by simpa only [hn] using hf, hr⟩, by simpa only [Γ.ofBool] using hf⟩) (by
        intro inp work out h
        simpa only [Q, R', rawMagnitude, hn, Bool.false_eq_true, ↓reduceIte] using h) (by omega)
  | true =>
    have hswap : Separate right left flag := ⟨sep.operands.symm, sep.flagRight, sep.flagLeft⟩
    have hRswap : ∀ work work', (∀ j, j ≠ right → j ≠ left → work' j = work j) → R' work → R' work' :=
      fun work work' hw => hR' work work' (fun j hl hr => hw j hr hl)
    have hraw := BinaryDifferenceEmit.hoareTime right left flag hswap ys xs before input emitted R' hRswap
    have hbody : (BinaryDifferenceMachine.machine right left flag true).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before input (emitted ++ (BinaryDifference.subtract ys xs false).1) inp work out ∧ Q work)
        (max xs.length ys.length + 1) := hraw.consequence (by
          rintro inp work out ⟨hc, hp, hr⟩
          exact ⟨hc, start_swap left right flag xs ys work hp, hr⟩) (by
            rintro inp work out ⟨hc, hp, hr⟩
            exact ⟨hc, finish_swap left right flag xs ys work hp, hr⟩) (by rw [Nat.max_comm])
    have hbranch := FlagBranchRun.yes_hoareTime flag
      (BinaryDifferenceMachine.machine right left flag true) (BinaryDifferenceMachine.machine left right flag true)
      before input emitted before input (emitted ++ (BinaryDifference.subtract ys xs false).1)
      P Q (max xs.length ys.length + 1) hbody
    exact hbranch.consequence (by
      rintro inp work out ⟨hc, hp, hf, hr⟩
      exact ⟨⟨hc, hp, by simpa only [hn] using hf, hr⟩, by simpa only [Γ.ofBool] using hf⟩) (by
        intro inp work out h
        simpa only [Q, R', rawMagnitude, hn, ↓reduceIte] using h) (by omega)

theorem trim_raw (xs ys : List Bool) : BinaryTrim.trim (rawMagnitude xs ys) = magnitude xs ys := by
  cases h : negative xs ys <;> simp only [rawMagnitude, magnitude, h, Bool.false_eq_true, ↓reduceIte]

theorem raw_length (xs ys : List Bool) : (rawMagnitude xs ys).length = max xs.length ys.length := by
  cases h : negative xs ys <;> simp only [rawMagnitude, h, Bool.false_eq_true, ↓reduceIte, BinaryDifference.output_length, Nat.max_comm]

end JointThermoComplexity.Complexity.BinaryMagnitudeSelect

#print axioms JointThermoComplexity.Complexity.BinaryMagnitudeSelect.hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryMagnitudeSelect.trim_raw
