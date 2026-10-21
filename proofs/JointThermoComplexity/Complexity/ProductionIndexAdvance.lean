module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionState

set_option autoImplicit false
@[expose] public section

/-! Advance actual reaction and shared-current addresses while preserving reusable operands and the reaction-mask head. -/

namespace JointThermoComplexity.Complexity.ProductionIndexAdvance
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts ProductionReactionState

theorem reaction_hoareTime (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (before remaining emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (UnarySuccessor.machine (reaction m)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n ri si idx mask k R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n (ri + 1) si idx mask k R work) (2 * ri + 6) := by
  rintro inp work out ⟨hc, hp⟩
  let P : (Fin (m + 20) → Tape) → Prop := fun work' => ∀ j, j ≠ reaction m → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ reaction m → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs, hi, hw⟩ := UnarySuccessor.hoareTime (reaction m) ri before remaining emitted P hP
    inp work out ⟨hc, hp.1.safe, hp.1.reactionPosition, fun _ _ => rfl⟩
  have hx (j : Fin (m + 20)) (hj : j.val ≠ 6) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hstate : ProductionOperandLoad.State m L n (ri + 1) si d.work :=
    ⟨hs, by simpa only [hx (left m) (by change (9 : ℕ) ≠ 6; omega)] using hp.1.productReusable,
      by simpa only [hx (right m) (by change (10 : ℕ) ≠ 6; omega)] using hp.1.reactantReusable,
      by simpa only [hx (magnitude m) (by change (8 : ℕ) ≠ 6; omega)] using hp.1.magnitudeReusable,
      by simpa only [hx (sign m) (by change (11 : ℕ) ≠ 6; omega)] using hp.1.signHead,
      by simpa only [hx (species m) (by change (12 : ℕ) ≠ 6; omega)] using hp.1.speciesPosition,
      by simpa only [hx (count m) (by change m + 15 ≠ 6; omega)] using hp.1.speciesCount, hi⟩
  exact ⟨d, t, ht, hd, hh, hc', hstate,
    by simpa only [hx (current m) (by change (7 : ℕ) ≠ 6; omega)] using hp.2.1,
    by simpa only [hx (PowerPorts.scratch (m + 7)) (by change (5 : ℕ) ≠ 6; omega)] using hp.2.2.1,
    by simpa only [hx (MotifBufferPorts.buffer (m + 5) 1) (by change (3 : ℕ) ≠ 6; omega)] using hp.2.2.2.1,
    hR work d.work (of_reaction m work d.work hw) hp.2.2.2.2⟩

theorem current_hoareTime (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (before remaining emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (UnarySuccessor.machine (current m)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n ri si idx mask k R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n ri si (idx + 1) mask k R work) (2 * idx + 6) := by
  rintro inp work out ⟨hc, hp⟩
  let P : (Fin (m + 20) → Tape) → Prop := fun work' => ∀ j, j ≠ current m → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ current m → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs, hi, hw⟩ := UnarySuccessor.hoareTime (current m) idx before remaining emitted P hP
    inp work out ⟨hc, hp.1.safe, hp.2.1, fun _ _ => rfl⟩
  have hzero : PowerPorts.scratch (m + 7) ≠ current m := by
    intro he; have hv := congrArg Fin.val he; change (5 : ℕ) = 7 at hv; omega
  have hmask : MotifBufferPorts.buffer (m + 5) 1 ≠ current m := by
    intro he; have hv := congrArg Fin.val he; change (3 : ℕ) = 7 at hv; omega
  exact ⟨d, t, ht, hd, hh, hc', ProductionVariable.state_frame m L n ri si work d.work (fun j hj _ => hw j hj) hs hp.1, hi,
    by simpa only [hw _ hzero] using hp.2.2.1, by simpa only [hw _ hmask] using hp.2.2.2.1,
    hR work d.work (of_current m work d.work hw) hp.2.2.2.2⟩

def machine (m : ℕ) : TM (m + 20) := seqTM (UnarySuccessor.machine (reaction m)) (UnarySuccessor.machine (current m))

theorem hoareTime (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (before remaining emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n ri si idx mask k R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n (ri + 1) si (idx + 1) mask k R work)
      (2 * ri + 2 * idx + 13) := by
  have hr := reaction_hoareTime m L n ri si idx mask k before remaining emitted R hR
  have hc := current_hoareTime m L n (ri + 1) si idx mask k before remaining emitted R hR
  have hs := seqTM_hoareTime (UnarySuccessor.machine (reaction m)) (UnarySuccessor.machine (current m)) hr (by
    rintro inp work out ⟨hcur, hp⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hp⟩) hc
  exact hs.mono_bound (by omega)

end JointThermoComplexity.Complexity.ProductionIndexAdvance

#print axioms JointThermoComplexity.Complexity.ProductionIndexAdvance.reaction_hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionIndexAdvance.current_hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionIndexAdvance.hoareTime
