module
public import proofs.JointThermoComplexity.Complexity.CountTape
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Finish a bounded unary accumulator by rewinding it to a canonical register. -/

namespace JointThermoComplexity.Complexity.CountRewind
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (rewindWorkTM idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate v true) ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => IsReg v (work idx) ∧ Cursor before input emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (v + 3) := by
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
  have hcontent : (work idx).HasBinaryContent (List.replicate v true) := hp.2
  have hhead : (work idx).head ≤ v + 1 := by simpa only [List.length_replicate] using hp.1.le
  obtain ⟨e, t, ht, hreach, hhalt, heHead, heFrame⟩ :=
    rewindWorkTM_hoareTime_frame idx (v + 1) hP inp work out
      ⟨hz, hcontent.cells_ne_start, hhead, hc.input_read, hc.output_read,
        by rw [hc.tapePrefix.1]; omega, (fun j _ => ⟨(hs j).read_ne_start, (hs j).1⟩),
        ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  have heContent : (e.work idx).HasBinaryContent (List.replicate v true) := by
    simpa only [Tape.HasBinaryContent, heFrame.2.2.1] using hcontent
  have heReg : IsReg v (e.work idx) := CountTape.register_of_string ⟨heHead, heContent⟩
    (by simpa only [heFrame.2.2.1] using hz)
  have heSafe : ∀ j, Parked (e.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j
      exact heReg.parked
    · rw [heFrame.2.2.2 j hj]
      exact hs j
  have heCur : Cursor before input emitted e.input e.work e.output :=
    ⟨by simpa only [heFrame.1] using hc.cells, by simpa only [heFrame.1] using hc.head,
      (fun j => ⟨(heSafe j).read_ne_start, (heSafe j).1⟩),
      by simpa only [heFrame.2.1] using hc.tapePrefix, by simpa only [heFrame.2.1] using hc.zero⟩
  exact ⟨e, t, by omega, hreach, hhalt, heReg, heCur, heSafe, hR work e.work heFrame.2.2.2 hr⟩

end JointThermoComplexity.Complexity.CountRewind

#print axioms JointThermoComplexity.Complexity.CountRewind.hoareTime
