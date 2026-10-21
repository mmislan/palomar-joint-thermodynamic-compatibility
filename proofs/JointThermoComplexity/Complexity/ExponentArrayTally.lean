module
public import proofs.JointThermoComplexity.Complexity.ExponentArrayData
public import proofs.JointThermoComplexity.Complexity.CountLoopFrame

set_option autoImplicit false
@[expose] public section

/-! A register-controlled pass over an encoded exponent array, with exact gate tally. -/

namespace JointThermoComplexity.Complexity.ExponentArrayTally
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend ExponentArrayData

variable {w : ℕ}

def StateInv (values : List ℕ) (count : ℕ) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (i : ℕ) : _root_.Complexity.TM.TapePred (w + 1) :=
  fun inp work out =>
    Cursor (before ++ code (values.take i)) (code (values.drop i) ++ tail) emitted inp work out ∧
    (∀ j, Parked (work j)) ∧
    (work destination).HasBinaryPrefix (List.replicate (count + cost (values.take i)) true) ∧
    (work destination).cells 0 = Γ.start ∧ R (oldWork work)

theorem body_hoareTime (fuel : Fin w) (values : List ℕ) (count i : ℕ) (hi : i < values.length)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (ExponentTally.machine (w := w)).HoareTime
      (InvariantLoop.Frame fuel.castSucc values.length (i + 2) (StateInv values count before tail emitted R i))
      (InvariantLoop.Frame fuel.castSucc values.length (i + 2) (StateInv values count before tail emitted R (i + 1)))
      ((code values).length + 4) := by
  intro inp work out hf
  rcases hf.invariant with ⟨hc, hs, hp, hz, hr⟩
  have hfuel : Parked (work fuel.castSucc) := by
    rw [hf.fuel]
    exact parked_regCells (by omega : 1 ≤ i + 2)
  have hphysical := LoopCursor.physical fuel.castSucc values.length hc ⟨hfuel.read_ne_start, hfuel.1⟩
  have hsafe := CountLoopFrame.physical_safe work fuel values.length (i + 2) (by omega) hf.fuel hs
  have hcur : Cursor (before ++ code (values.take i))
      (BitCodec.naturalCode values[i] ++ (code (values.drop (i + 1)) ++ tail)) emitted inp work out := by
    simpa only [drop_code values i hi, List.append_assoc] using hphysical
  have hprefix : (work destination).HasBinaryPrefix (List.replicate (count + cost (values.take i)) true) := by
    simpa only [CountLoopFrame.destination_restore] using hp
  have hzero : (work destination).cells 0 = Γ.start := by
    simpa only [CountLoopFrame.destination_restore] using hz
  let RN : (Fin w → Tape) → Prop := fun old =>
    old fuel = ⟨i + 2, regCells values.length⟩ ∧ R (Function.update old fuel (regTape values.length))
  have hRN : RN (oldWork work) := by
    refine ⟨hf.fuel, ?_⟩
    simpa only [CountLoopFrame.oldWork_restore] using hr
  obtain ⟨e, t, ht, hreach, hhalt, hecur, hesafe, hep, hez, heR⟩ :=
    ExponentTally.hoareTime values[i] (count + cost (values.take i)) (before ++ code (values.take i))
      (code (values.drop (i + 1)) ++ tail) emitted RN inp work out ⟨hcur, hsafe, hprefix, hzero, hRN⟩
  have hdfuel : e.work fuel.castSucc = ⟨i + 2, regCells values.length⟩ := heR.1
  have hnewcur : Cursor (before ++ code (values.take (i + 1)))
      (code (values.drop (i + 1)) ++ tail) emitted e.input e.work e.output := by
    simpa only [take_code_succ values i hi, List.append_assoc] using hecur
  refine ⟨e, t, le_trans ht (Nat.add_le_add_right (field_length_le values i hi) 4), hreach, hhalt,
    hdfuel, hecur.input_read, (fun j _ => (hecur.works j).1), hecur.output_read,
    LoopCursor.restore hnewcur fuel.castSucc values.length,
    RepeatedOutput.restored_safe e.work fuel.castSucc values.length hesafe, ?_, ?_, ?_⟩
  · simpa only [CountLoopFrame.destination_restore, take_cost_succ values i hi, Nat.add_assoc] using hep
  · simpa only [CountLoopFrame.destination_restore] using hez
  · simpa only [CountLoopFrame.oldWork_restore] using heR.2

def machine (fuel : Fin w) : TM (w + 1) := forRegTM ExponentTally.machine fuel.castSucc

theorem hoareTime (fuel : Fin w) (values : List ℕ) (count : ℕ) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine fuel).HoareTime
      (fun inp work out => IsReg values.length (work fuel.castSucc) ∧
        Cursor before (code values ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate count true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => IsReg values.length (work fuel.castSucc) ∧
        Cursor (before ++ code values) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate (count + cost values) true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (values.length * ((code values).length + 6) + (values.length + 2)) := by
  rintro inp work out ⟨hf, hc, hs, hp, hz, hr⟩
  have hpre : InvariantLoop.Frame fuel.castSucc values.length 1
      (StateInv values count before tail emitted R 0) inp work out := by
    refine ⟨hf.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [InvariantLoop.restore_self work fuel.castSucc values.length hf.eq_regT]
    simpa only [StateInv, List.take_zero, List.drop_zero, code, cost, List.append_nil, Nat.add_zero]
      using (show Cursor before (code values ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work)
        from ⟨hc, hs, hp, hz, hr⟩)
  obtain ⟨d, t, ht, hreach, hhalt, hpost⟩ :=
    InvariantLoop.hoareTime ExponentTally.machine fuel.castSucc (StateInv values count before tail emitted R)
      ((code values).length + 4) values.length
      (fun i hi => body_hoareTime fuel values count i hi before tail emitted R) inp work out hpre
  refine ⟨d, t, by simpa only [Nat.add_assoc] using ht, hreach, hhalt, hpost.register, ?_⟩
  simpa only [StateInv, List.take_length, List.drop_length, code, List.nil_append] using hpost.on_work

end JointThermoComplexity.Complexity.ExponentArrayTally

#print axioms JointThermoComplexity.Complexity.ExponentArrayTally.hoareTime
