module
public import proofs.JointThermoComplexity.Complexity.ReactionTally
public import proofs.JointThermoComplexity.Complexity.ReactionArrayData

set_option autoImplicit false
@[expose] public section

/-! A uniform nested loop computing the exact gate count of consecutive reaction records. -/

namespace JointThermoComplexity.Complexity.ReactionArrayTally
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend ReactionArrayData

variable {w n : ℕ}

def StateInv (species : Fin w) (values : List (ReactionCircuit.Reaction n)) (count : ℕ)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) (i : ℕ) : _root_.Complexity.TM.TapePred (w + 1) :=
  TallySpec.State (count + ExactGateCount.networkCost (values.take i))
    (before ++ code (values.take i)) (code (values.drop i) ++ tail) emitted
    (fun old => IsReg n (old species) ∧ R old)

theorem time_mono (n : ℕ) : Monotone (ReactionTally.timeBound n) := by
  intro a b h
  have hm := Nat.mul_le_mul_left n (Nat.add_le_add_right h 6)
  dsimp [ReactionTally.timeBound]
  omega

theorem body_hoareTime (species fuel : Fin w) (hsf : species ≠ fuel)
    (values : List (ReactionCircuit.Reaction n)) (count i : ℕ) (hi : i < values.length)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (ReactionTally.machine species).HoareTime
      (InvariantLoop.Frame fuel.castSucc values.length (i + 2) (StateInv species values count before tail emitted R i))
      (InvariantLoop.Frame fuel.castSucc values.length (i + 2) (StateInv species values count before tail emitted R (i + 1)))
      (ReactionTally.timeBound n (code values).length) := by
  intro inp work out hf
  rcases hf.invariant with ⟨hc, hs, hp, hz, hspecies, hr⟩
  have hfuel : Parked (work fuel.castSucc) := by
    rw [hf.fuel]
    exact parked_regCells (by omega : 1 ≤ i + 2)
  have hphysical := LoopCursor.physical fuel.castSucc values.length hc ⟨hfuel.read_ne_start, hfuel.1⟩
  have hsafe := CountLoopFrame.physical_safe work fuel values.length (i + 2) (by omega) hf.fuel hs
  have hcur : Cursor (before ++ code (values.take i))
      ((DataCodec.reaction n).code values[i] ++ (code (values.drop (i + 1)) ++ tail)) emitted inp work out := by
    simpa only [drop_code values i hi, List.append_assoc] using hphysical
  have hprefix : (work destination).HasBinaryPrefix
      (List.replicate (count + ExactGateCount.networkCost (values.take i)) true) := by
    simpa only [CountLoopFrame.destination_restore] using hp
  have hzero : (work destination).cells 0 = Γ.start := by
    simpa only [CountLoopFrame.destination_restore] using hz
  have hsp : IsReg n (oldWork work species) := by
    simpa only [CountLoopFrame.oldWork_restore, Function.update_of_ne hsf] using hspecies
  let RN : (Fin w → Tape) → Prop := fun old =>
    old fuel = ⟨i + 2, regCells values.length⟩ ∧ R (Function.update old fuel (regTape values.length))
  have hRN : RN (oldWork work) := by
    refine ⟨hf.fuel, ?_⟩
    simpa only [CountLoopFrame.oldWork_restore] using hr
  obtain ⟨e, t, ht, hreach, hhalt, hecur, hesafe, hep, hez, heSpecies, heR⟩ :=
    ReactionTally.runs species values[i] (count + ExactGateCount.networkCost (values.take i))
      (before ++ code (values.take i)) (code (values.drop (i + 1)) ++ tail) emitted RN
      inp work out ⟨hcur, hsafe, hprefix, hzero, hsp, hRN⟩
  have hnewcur : Cursor (before ++ code (values.take (i + 1)))
      (code (values.drop (i + 1)) ++ tail) emitted e.input e.work e.output := by
    simpa only [take_code_succ values i hi, List.append_assoc] using hecur
  refine ⟨e, t, le_trans ht (time_mono n (field_length_le values i hi)), hreach, hhalt,
    heR.1, hecur.input_read, (fun j _ => (hecur.works j).1), hecur.output_read,
    LoopCursor.restore hnewcur fuel.castSucc values.length,
    RepeatedOutput.restored_safe e.work fuel.castSucc values.length hesafe, ?_, ?_, ?_, ?_⟩
  · simpa only [CountLoopFrame.destination_restore, take_cost_succ values i hi, Nat.add_assoc] using hep
  · simpa only [CountLoopFrame.destination_restore] using hez
  · simpa only [CountLoopFrame.oldWork_restore, Function.update_of_ne hsf] using heSpecies
  · simpa only [CountLoopFrame.oldWork_restore] using heR.2

def machine (species fuel : Fin w) : TM (w + 1) := forRegTM (ReactionTally.machine species) fuel.castSucc

theorem hoareTime (species fuel : Fin w) (hsf : species ≠ fuel) (values : List (ReactionCircuit.Reaction n))
    (count : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine species fuel).HoareTime
      (fun inp work out => IsReg values.length (work fuel.castSucc) ∧ IsReg n (work species.castSucc) ∧
        Cursor before (code values ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate count true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => IsReg values.length (work fuel.castSucc) ∧ IsReg n (work species.castSucc) ∧
        Cursor (before ++ code values) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate (count + ExactGateCount.networkCost values) true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (values.length * (ReactionTally.timeBound n (code values).length + 2) + (values.length + 2)) := by
  rintro inp work out ⟨hf, hspecies, hc, hs, hp, hz, hr⟩
  have hpre : InvariantLoop.Frame fuel.castSucc values.length 1
      (StateInv species values count before tail emitted R 0) inp work out := by
    refine ⟨hf.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [InvariantLoop.restore_self work fuel.castSucc values.length hf.eq_regT]
    simpa only [StateInv, TallySpec.State, List.take_zero, List.drop_zero, code,
      ExactGateCount.networkCost, List.append_nil, Nat.add_zero]
      using (show Cursor before (code values ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧
        IsReg n (oldWork work species) ∧ R (oldWork work) from ⟨hc, hs, hp, hz, hspecies, hr⟩)
  obtain ⟨d, t, ht, hreach, hhalt, hpost⟩ :=
    InvariantLoop.hoareTime (ReactionTally.machine species) fuel.castSucc
      (StateInv species values count before tail emitted R) (ReactionTally.timeBound n (code values).length) values.length
      (fun i hi => body_hoareTime species fuel hsf values count i hi before tail emitted R) inp work out hpre
  have hp' := hpost.on_work
  simp only [StateInv, TallySpec.State, List.take_length, List.drop_length, code, List.nil_append] at hp'
  rcases hp' with ⟨hc', hs', hprefix, hzero, hspecies', hr'⟩
  exact ⟨d, t, ht, hreach, hhalt, hpost.register, hspecies', hc', hs', hprefix, hzero, hr'⟩

end JointThermoComplexity.Complexity.ReactionArrayTally

#print axioms JointThermoComplexity.Complexity.ReactionArrayTally.hoareTime
