module
public import proofs.JointThermoComplexity.Complexity.RepeatedOutput
public import proofs.JointThermoComplexity.Complexity.OutputRoute

set_option autoImplicit false
@[expose] public section

/-! Append a bounded count to a unary work accumulator, leaving real output untouched. -/

namespace JointThermoComplexity.Complexity.CountAppend
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def oldWork (work : Fin (w + 1) → Tape) : Fin w → Tape := fun j => work j.castSucc
def destination : Fin (w + 1) := Fin.last w
def machine (fuel : Fin w) : TM (w + 1) := (RepeatedOutput.machine fuel [true]).retargetOutput

theorem hoareTime (fuel : Fin w) (v d : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine fuel).HoareTime
      (fun inp work out => IsReg v (work fuel.castSucc) ∧ Cursor before input emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work destination).HasBinaryPrefix (List.replicate d true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => IsReg v (work fuel.castSucc) ∧ Cursor before input emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work destination).HasBinaryPrefix (List.replicate (d + v) true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work)) (4 * v + 2) := by
  rintro inp work out ⟨hf, hc, hs, hp, hz, hr⟩
  let S : Tape → Prop := fun out => out.HasBinaryPrefix emitted ∧ out.cells 0 = Γ.start
  have hrepeat := RepeatedOutput.hoareTime fuel v before input (List.replicate d true) [true] R
  have hroute := OutputRoute.hoareTime (RepeatedOutput.machine fuel [true]) _ _ _ S hrepeat
  have hvcur : Cursor before input (List.replicate d true) inp (oldWork work) (work destination) :=
    ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, hp, hz⟩
  obtain ⟨e, t, ht, hreach, hhalt, _ho, hout, heFuel, heCur, heSafe, heR⟩ :=
    hroute inp work out ⟨hc.output_read, ⟨hc.tapePrefix, hc.zero⟩, hf, hvcur, (fun j => hs j.castSucc), hr⟩
  have hePrefix : (e.work destination).HasBinaryPrefix (List.replicate (d + v) true) := by
    simpa only [destination, RepeatedOutput.copies_singleton, ← List.replicate_add] using heCur.tapePrefix
  have heZero : (e.work destination).cells 0 = Γ.start := heCur.zero
  have heAll : ∀ j, Parked (e.work j) := by
    intro j
    by_cases hj : j.val < w
    · let k : Fin w := ⟨j.val, hj⟩
      have he : j = k.castSucc := rfl
      rw [he]
      exact heSafe k
    · have he : j = Fin.last w := by apply Fin.ext; simp only [Fin.val_last]; omega
      rw [he]
      exact ((FixedOutput.outAcc_iff _ _).mpr ⟨hePrefix, heZero⟩).parked
  have heCursor : Cursor before input emitted e.input e.work e.output :=
    ⟨heCur.cells, heCur.head, fun j => ⟨(heAll j).read_ne_start, (heAll j).1⟩, hout.1, hout.2⟩
  refine ⟨e, t, ?_, hreach, hhalt, heFuel, heCursor, heAll, hePrefix, heZero, heR⟩
  simp only [List.length_cons, List.length_nil] at ht
  omega

end JointThermoComplexity.Complexity.CountAppend

#print axioms JointThermoComplexity.Complexity.CountAppend.hoareTime
