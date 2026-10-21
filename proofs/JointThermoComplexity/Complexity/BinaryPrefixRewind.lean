module
public import proofs.JointThermoComplexity.Complexity.HeaderAt
public import proofs.JointThermoComplexity.Complexity.TapeSafety

set_option autoImplicit false
@[expose] public section

/-! Rewind an arbitrary completed binary prefix, preserving all other tapes. -/

namespace JointThermoComplexity.Complexity.BinaryPrefixRewind
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem hoareTime (idx : Fin w) (bits : List Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (rewindWorkTM idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work) (bits.length + 3) := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  let P : _root_.Complexity.TM.TapePred w := fun inp' work' out' =>
    inp' = inp ∧ out' = out ∧ (work' idx).cells = (work idx).cells ∧ ∀ j, j ≠ idx → work' j = work j
  have hP : ∀ (inp' : Tape) (work' : Fin w → Tape) (out' : Tape)
      (inp'' : Tape) (work'' : Fin w → Tape) (out'' : Tape),
      P inp' work' out' → (work'' idx).cells = (work' idx).cells → (work'' idx).head = 1 →
      (∀ j, j ≠ idx → work'' j = work' j) → inp'' = inp' → out''.cells = out'.cells →
      out''.head = out'.head → P inp'' work'' out'' := by
    rintro inp' work' out' inp'' work'' out'' ⟨hi, ho, hcells, hw⟩ hcells' _ hw' hi' hoc hoh
    exact ⟨hi'.trans hi, (Tape.ext hoh hoc).trans ho, hcells'.trans hcells, fun j hj => (hw' j hj).trans (hw j hj)⟩
  have hcontent : (work idx).HasBinaryContent bits := hp.2
  obtain ⟨e, t, ht, hreach, hhalt, heHead, heFrame⟩ :=
    rewindWorkTM_hoareTime_frame idx (bits.length + 1) hP inp work out
      ⟨hz, hcontent.cells_ne_start, hp.1.le, hc.input_read, hc.output_read,
        by rw [hc.tapePrefix.1]; omega, (fun j _ => ⟨(hs j).read_ne_start, (hs j).1⟩),
        ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  have heSafe : ∀ j, Parked (e.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j
      exact ⟨by rw [heHead], TapeSafety.work_reaches idx hreach (hs idx).2⟩
    · rw [heFrame.2.2.2 j hj]
      exact hs j
  have heCur : Cursor before input emitted e.input e.work e.output :=
    ⟨by simpa only [heFrame.1] using hc.cells, by simpa only [heFrame.1] using hc.head,
      (fun j => ⟨(heSafe j).read_ne_start, (heSafe j).1⟩),
      by simpa only [heFrame.2.1] using hc.tapePrefix, by simpa only [heFrame.2.1] using hc.zero⟩
  have heContent : (e.work idx).HasBinaryContent bits := by
    simpa only [Tape.HasBinaryContent, heFrame.2.2.1] using hcontent
  exact ⟨e, t, by omega, hreach, hhalt, heCur, heSafe, ⟨heHead, heContent⟩,
    by simpa only [heFrame.2.2.1] using hz, hR work e.work heFrame.2.2.2 hr⟩

end JointThermoComplexity.Complexity.BinaryPrefixRewind

#print axioms JointThermoComplexity.Complexity.BinaryPrefixRewind.hoareTime
