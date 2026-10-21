module
public import proofs.JointThermoComplexity.Complexity.UnaryBinaryBuild
public import proofs.JointThermoComplexity.Complexity.BinaryEmit
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-!
# Canonical binary index emission from a bounded count register

The actual machine preserves the unary source, appends its canonical natural
code, and leaves the binary scratch register parked with the same value. The
scratch starts empty. This is for bounded indices, never input numeric values.
-/

namespace JointThermoComplexity.Complexity.IndexEmitter
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

def machine (fuel scratch : Fin w) : TM w := seqTM (UnaryBinaryBuild.machine fuel scratch) (BinaryEmit.machine scratch)

def timeBound (v : ℕ) : ℕ := v * (2 * v + 6) + 4 * v + 8

theorem timeBound_eq (v : ℕ) : timeBound v = 2 * v ^ 2 + 10 * v + 8 := by
  unfold timeBound
  ring1

theorem hoareTime (fuel scratch : Fin w) (hne : fuel ≠ scratch) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel → j ≠ scratch → work' j = work j) → R work → R work') :
    (machine fuel scratch).HoareTime
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input emitted inp work out ∧ Register 0 (work scratch) ∧ R work)
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input (emitted ++ BitCodec.naturalCode v) inp work out ∧
        Register v (work scratch) ∧ R work) (timeBound v) := by
  let RP : (Fin w → Tape) → Prop := fun work => IsReg v (work fuel) ∧ R work
  have hb := UnaryBinaryBuild.hoareTime fuel scratch hne v before input emitted R hR
  have he := BinaryEmit.natural_hoareTime scratch v before input emitted RP
  have hseq := seqTM_hoareTime (UnaryBinaryBuild.machine fuel scratch) (BinaryEmit.machine scratch) hb (by
    rintro inp work out ⟨hreg, hc, hd, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hd, hreg, hr⟩) he
  apply HoareTime.mono_bound (b := (v * (2 * v + 6) + (v + 2)) + 1 + (3 * v.bits.length + 5))
  · apply HoareTime.strengthen_post hseq
    rintro inp work out ⟨hc, hd, hreg, hr⟩
    exact ⟨hreg, hc, hd, hr⟩
  · have hn := BinaryIncrementControl.bits_length_le v
    unfold timeBound
    omega

end JointThermoComplexity.Complexity.IndexEmitter

#print axioms JointThermoComplexity.Complexity.IndexEmitter.hoareTime
