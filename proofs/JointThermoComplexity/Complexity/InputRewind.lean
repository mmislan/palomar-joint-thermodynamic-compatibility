module
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Restart an input scan while retaining the output and every work register. -/

namespace JointThermoComplexity.Complexity.InputRewind
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem hoareTime (before remaining emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (rewindInputTM (n := w)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ R work)
      (fun inp work out => Cursor [] (before ++ remaining) emitted inp work out ∧ R work)
      (before.length + 3) := by
  let P : _root_.Complexity.TM.TapePred w := fun inp work out =>
    inp.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells ∧
    (∀ j, (work j).read ≠ Γ.start ∧ 1 ≤ (work j).head) ∧
    out.HasBinaryPrefix emitted ∧ out.cells 0 = Γ.start ∧ R work
  have hp : ∀ (inp : Tape) (work : Fin w → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin w → Tape) (out' : Tape),
      P inp work out → inp'.cells = inp.cells → inp'.head = 1 → work' = work → out' = out → P inp' work' out' := by
    rintro inp work out inp' work' out' ⟨hc, hw, ho, hz, hr⟩ hi _ hew heo
    exact ⟨hi.trans hc, by simpa only [hew] using hw, by simpa only [heo] using ho,
      by simpa only [heo] using hz, by simpa only [hew] using hr⟩
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hhead, hpost⟩ :=
    rewindInputTM_hoareTime_frame (before.length + 1) hp inp work out
      ⟨by rw [hc.cells]; simp [Tape.init],
        (fun j hj => by rw [hc.cells]; exact Tape.init_ofBool_cells_ne_start _ j hj),
        by rw [hc.head], hc.output_read, by rw [hc.tapePrefix.1]; omega,
        hc.works, hc.cells, hc.works, hc.tapePrefix, hc.zero, hr⟩
  exact ⟨d, t, by omega, hreach, hhalt,
    ⟨by simpa only [List.nil_append] using hpost.1, by simpa using hhead,
      hpost.2.1, hpost.2.2.1, hpost.2.2.2.1⟩, hpost.2.2.2.2⟩

end JointThermoComplexity.Complexity.InputRewind

#print axioms JointThermoComplexity.Complexity.InputRewind.hoareTime
