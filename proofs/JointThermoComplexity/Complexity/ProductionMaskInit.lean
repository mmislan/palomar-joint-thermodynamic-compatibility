module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionStep

set_option autoImplicit false
@[expose] public section

/-! Rewind the actual stored reaction mask and original input before the production sum, retaining reusable State. -/

namespace JointThermoComplexity.Complexity.ProductionMaskInit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts ProductionReactionState

theorem rewind_hoareTime (m L n ri si idx : ℕ) (mask : List Bool) (before remaining emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (rewindWorkTM (MotifBufferPorts.buffer (m + 5) 1)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n ri si work ∧
        IsReg idx (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧
        BoxBufferState.Stored mask (work (MotifBufferPorts.buffer (m + 5) 1)) ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n ri si idx mask 0 R work) (mask.length + 3) := by
  rintro inp work out ⟨hc, hp, hi, hz, hm, hr⟩
  let P : (Fin (m + 20) → Tape) → Prop := fun work' => ∀ j, j ≠ MotifBufferPorts.buffer (m + 5) 1 → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ MotifBufferPorts.buffer (m + 5) 1 → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs, hbits, hzero, hw⟩ :=
    BinaryPrefixRewind.hoareTime (MotifBufferPorts.buffer (m + 5) 1) mask before remaining emitted P hP
      inp work out ⟨hc, hp.safe, hm.1, hm.2, fun _ _ => rfl⟩
  have hx (j : Fin (m + 20)) (hj : j.val ≠ 3) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hstate : ProductionOperandLoad.State m L n ri si d.work :=
    ⟨hs, by simpa only [hx (left m) (by change (9 : ℕ) ≠ 3; omega)] using hp.productReusable,
      by simpa only [hx (right m) (by change (10 : ℕ) ≠ 3; omega)] using hp.reactantReusable,
      by simpa only [hx (magnitude m) (by change (8 : ℕ) ≠ 3; omega)] using hp.magnitudeReusable,
      by simpa only [hx (sign m) (by change (11 : ℕ) ≠ 3; omega)] using hp.signHead,
      by simpa only [hx (species m) (by change (12 : ℕ) ≠ 3; omega)] using hp.speciesPosition,
      by simpa only [hx (count m) (by change m + 15 ≠ 3; omega)] using hp.speciesCount,
      by simpa only [hx (reaction m) (by change (6 : ℕ) ≠ 3; omega)] using hp.reactionPosition⟩
  exact ⟨d, t, ht, hd, hh, hc', hstate,
    by simpa only [hx (current m) (by change (7 : ℕ) ≠ 3; omega)] using hi,
    by simpa only [hx (PowerPorts.scratch (m + 7)) (by change (5 : ℕ) ≠ 3; omega)] using hz,
    ⟨hbits.2, hzero, hbits.1⟩, hR work d.work (of_mask m work d.work hw) hr⟩

def machine (m : ℕ) : TM (m + 20) := seqTM (rewindWorkTM (MotifBufferPorts.buffer (m + 5) 1)) rewindInputTM

theorem hoareTime (m n ri si idx : ℕ) (input before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (mask : List Bool) (hm : mask.length ≤ input.length) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m input.length n ri si work ∧
        IsReg idx (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧
        BoxBufferState.Stored mask (work (MotifBufferPorts.buffer (m + 5) 1)) ∧ R work)
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input.length n ri si idx mask 0 R work)
      (2 * input.length + 7) := by
  have hm := rewind_hoareTime m input.length n ri si idx mask before remaining emitted R hR
  have hr := InputRewind.hoareTime before remaining emitted (State m input.length n ri si idx mask 0 R)
  have hs := seqTM_hoareTime (rewindWorkTM (MotifBufferPorts.buffer (m + 5) 1)) rewindInputTM hm (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp⟩) hr
  have hlength := congrArg List.length hsplit
  simp only [List.length_append] at hlength
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ ⟨hc, hp⟩ => ⟨by simpa only [hsplit] using hc, hp⟩) (by omega)

end JointThermoComplexity.Complexity.ProductionMaskInit

#print axioms JointThermoComplexity.Complexity.ProductionMaskInit.rewind_hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionMaskInit.hoareTime
