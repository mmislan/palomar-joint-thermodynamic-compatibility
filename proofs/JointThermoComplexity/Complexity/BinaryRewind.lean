module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementMachine
public import proofs.JointThermoComplexity.Complexity.BinaryTape

set_option autoImplicit false
@[expose] public section

/-! Park a binary work string using the checked rewind and a complete frame. -/

namespace JointThermoComplexity.Complexity.BinaryRewind
open _root_.Complexity
open _root_.Complexity.TM
open BinaryIncrementMachine

variable {w : ℕ}

theorem run (idx : Fin w) (bits : List Bool) (B : ℕ) (c : Cfg w State)
    (hs : c.state = .rewind .moveLeft) (hc : (c.work idx).HasBinaryContent bits)
    (hz : (c.work idx).cells 0 = Γ.start) (hh : (c.work idx).head ≤ B)
    (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) (hohead : 1 ≤ c.output.head)
    (hw : ∀ j, j ≠ idx → (c.work j).read ≠ Γ.start ∧ 1 ≤ (c.work j).head) :
    ∃ d t, t ≤ B + 2 ∧ (machine idx).reachesIn t c d ∧ (machine idx).halted d ∧
      d.input = c.input ∧ d.output = c.output ∧ (∀ j, j ≠ idx → d.work j = c.work j) ∧
      (d.work idx).HasBinaryString bits ∧ (d.work idx).cells 0 = Γ.start := by
  let P : Tape → (Fin w → Tape) → Tape → Prop := fun inp work out =>
    inp = c.input ∧ out = c.output ∧ (work idx).cells = (c.work idx).cells ∧
      ∀ j, j ≠ idx → work j = c.work j
  have hP : ∀ (inp : Tape) (work : Fin w → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin w → Tape) (out' : Tape),
      P inp work out → (work' idx).cells = (work idx).cells → (work' idx).head = 1 →
      (∀ j, j ≠ idx → work' j = work j) → inp' = inp → out'.cells = out.cells → out'.head = out.head → P inp' work' out' := by
    rintro inp work out inp' work' out' ⟨hinp, hout, hcells, hothers⟩ hc' _ hw' hi' hoc hoh
    exact ⟨hi'.trans hinp, (Tape.ext hoh hoc).trans hout, hc'.trans hcells,
      fun j hj => (hw' j hj).trans (hothers j hj)⟩
  obtain ⟨d', t, ht, hreach, hhalt, hdhead, hp⟩ :=
    rewindWorkTM_hoareTime_frame idx B hP c.input c.work c.output
      ⟨hz, hc.cells_ne_start, hh, hi, ho, hohead, hw, rfl, rfl, rfl, fun _ _ => rfl⟩
  let c₀ : Cfg w RewindPhase := ⟨.moveLeft, c.input, c.work, c.output⟩
  have hwrap : wrap idx c₀ = c := by
    apply Cfg.ext
    · exact hs.symm
    · rfl
    · rfl
    · rfl
  have hparent : (machine idx).reachesIn t c (wrap idx d') := by
    rw [← hwrap]
    exact rewind_reaches idx hreach
  have hcontent : (d'.work idx).HasBinaryContent bits := by
    simpa only [Tape.HasBinaryContent, hp.2.2.1] using hc
  exact ⟨wrap idx d', t, ht, hparent, rewind_halted idx hhalt, hp.1, hp.2.1, hp.2.2.2,
    ⟨hdhead, hcontent⟩, by simpa only [wrap, hp.2.2.1] using hz⟩

end JointThermoComplexity.Complexity.BinaryRewind

#print axioms JointThermoComplexity.Complexity.BinaryRewind.run
