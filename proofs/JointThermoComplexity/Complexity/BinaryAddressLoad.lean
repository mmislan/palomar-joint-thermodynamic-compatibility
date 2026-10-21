module
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset
public import proofs.JointThermoComplexity.Complexity.UnaryBinaryBuildFramed

set_option autoImplicit false
@[expose] public section

/-! Replace a raw binary address from a bounded unary source, preserving every
other work tape, including the restored source register and its saved frame. -/

namespace JointThermoComplexity.Complexity.BinaryAddressLoad
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
variable {w : ℕ}

def Stable (dst : Fin w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ dst → next j = work j) → R work → R next

theorem build_hoareTime (fuel dst : Fin w) (hne : fuel ≠ dst) (value : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable dst R) :
    (UnaryBinaryBuild.machine fuel dst).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work dst) ∧ IsReg value (work fuel) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register value (work dst) ∧ IsReg value (work fuel) ∧ R work)
      (value * (2 * value + 6) + (value + 2)) := by
  rintro inp work out ⟨hc, hs, hd, hf, hx⟩
  let C : (Fin w → Tape) → Prop := fun next => ∀ j, j ≠ fuel → j ≠ dst → next j = work j
  have hC : ∀ a b, (∀ j, j ≠ fuel → j ≠ dst → b j = a j) → C a → C b := by
    intro a b he ha j hj hk
    exact (he j hj hk).trans (ha j hj hk)
  have h := UnaryBinaryBuildFramed.hoareTime fuel dst hne value before input emitted C hC
  obtain ⟨d, t, ht, hr, hh, hc', hs', hf', hd', he⟩ :=
    h inp work out ⟨hc, hs, hf, hd, fun _ _ _ => rfl⟩
  have hother : ∀ j, j ≠ dst → d.work j = work j := by
    intro j hj
    by_cases hjf : j = fuel
    · subst j
      exact hf'.eq_regT.trans hf.eq_regT.symm
    · exact he j hjf hj
  exact ⟨d, t, ht, hr, hh, hc', hs', hd', hf', hR work d.work hother hx⟩

def machine (fuel dst : Fin w) : TM w :=
  seqTM (BinaryBufferReset.machine dst) (UnaryBinaryBuild.machine fuel dst)

def timeBound (old value : ℕ) : ℕ := (3 * old.bits.length + 9) + 1 + (value * (2 * value + 6) + (value + 2))
def boundedTime (W : ℕ) : ℕ := (3 * W + 9) + 1 + (W * (2 * W + 6) + (W + 2))

theorem timeBound_le (old value W : ℕ) (ho : old.bits.length ≤ W) (hv : value ≤ W) :
    timeBound old value ≤ boundedTime W := by
  dsimp only [timeBound, boundedTime]
  gcongr

theorem hoareTime (fuel dst : Fin w) (hne : fuel ≠ dst) (old value : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable dst R) :
    (machine fuel dst).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register old (work dst) ∧ IsReg value (work fuel) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register value (work dst) ∧ IsReg value (work fuel) ∧ R work)
      (timeBound old value) := by
  let C : (Fin w → Tape) → Prop := fun work => IsReg value (work fuel) ∧ R work
  have hC : Stable dst C := by
    rintro work next he ⟨hf, hx⟩
    exact ⟨by simpa only [he fuel hne] using hf, hR work next he hx⟩
  have hreset := BinaryBufferReset.hoareTime dst old.bits before input emitted C hC
  have hbuild := build_hoareTime fuel dst hne value before input emitted R hR
  have hseq := seqTM_hoareTime _ _ hreset (by
    rintro inp work out ⟨hc, hs, hz, hf, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs,
      ⟨by simpa only [List.replicate_zero, Nat.zero_bits] using CountTape.string_of_register hz, hz.cell0⟩, hf, hx⟩) hbuild
  apply hseq.weaken_pre
  rintro inp work out ⟨hc, hs, hd, hf, hx⟩
  exact ⟨hc, hs, hd.1.2, hd.2, by rw [hd.1.1]; omega, hf, hx⟩

end JointThermoComplexity.Complexity.BinaryAddressLoad

#print axioms JointThermoComplexity.Complexity.BinaryAddressLoad.build_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryAddressLoad.hoareTime
