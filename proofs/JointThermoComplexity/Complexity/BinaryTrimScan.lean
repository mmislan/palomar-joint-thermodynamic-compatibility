module
public import proofs.JointThermoComplexity.Complexity.BinaryTrimStep
public import proofs.JointThermoComplexity.Complexity.BinaryEraseLast
public import proofs.JointThermoComplexity.Complexity.BinaryTrimSuffix
public import Mathlib.Data.List.Induction

set_option autoImplicit false
@[expose] public section

/-! The backward normalization scan erases only high zeros and takes at most one step per digit plus one. -/

namespace JointThermoComplexity.Complexity.BinaryTrimScan
open _root_.Complexity
open _root_.Complexity.TM
open BinaryTrimMachine BinaryTrimStep

variable {w : ℕ}

structure Result (idx : Fin w) (bits : List Bool) (c d : Cfg w (Option Bool)) : Prop where
  input_eq : d.input = c.input
  output_eq : d.output = c.output
  others : ∀ j, j ≠ idx → d.work j = c.work j
  normalized : (d.work idx).HasBinaryPrefix (BinaryTrim.trim bits)
  zero : (d.work idx).cells 0 = Γ.start

theorem scan (bits : List Bool) : ∀ (idx : Fin w) (c : Cfg w (Option Bool)),
    c.state = some true → (c.work idx).HasBinaryContent bits → (c.work idx).head = bits.length →
    (c.work idx).cells 0 = Γ.start → c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
    (∀ j, j ≠ idx → (c.work j).read ≠ Γ.start) →
    ∃ d t, t ≤ bits.length + 1 ∧ (machine idx).reachesIn t c d ∧ (machine idx).halted d ∧ Result idx bits c d := by
  induction bits using List.reverseRecOn with
  | nil =>
    intro idx c hs hc hh hz hi ho hw
    let d := cfg idx none false .right c
    have hr : (c.work idx).read = Γ.start := by simpa only [Tape.read, hh, List.length_nil] using hz
    have hsel : d.work idx = (c.work idx).move .right := marker_selected idx c.work hh hz
    refine ⟨d, 1, by simp, .step (stop_step idx c hs (by simp [hr])) .zero, rfl,
      cfg_input idx none false .right c hi, cfg_output idx none false .right c ho,
      (fun j hj => cfg_other idx j none false .right c hj (hw j hj)), ?_, ?_⟩
    · rw [hsel]
      exact ⟨by simp [Tape.move, hh, BinaryTrim.trim], hc.move .right⟩
    · simpa only [hsel, Tape.move_cells] using hz
  | append_singleton xs b ih =>
    intro idx c hs hc hh hz hi ho hw
    have hhead : (c.work idx).head = xs.length + 1 := by simpa using hh
    have hr := BinaryTape.read_cons xs [] b hc hhead
    cases b with
    | false =>
      let d := cfg idx (some true) true .left c
      have hsel : d.work idx = (c.work idx).writeAndMove Γ.blank .left := erase_selected idx c.work hr
      have hdi : d.input = c.input := cfg_input idx (some true) true .left c hi
      have hdo : d.output = c.output := cfg_output idx (some true) true .left c ho
      have hdw : ∀ j, j ≠ idx → d.work j = c.work j := fun j hj => cfg_other idx j (some true) true .left c hj (hw j hj)
      have hdc : (d.work idx).HasBinaryContent xs := by
        rw [hsel]
        exact (BinaryEraseLast.content xs false hc hhead).move .left
      have hdh : (d.work idx).head = xs.length := by
        rw [hsel]
        simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hhead, Nat.add_sub_cancel]
      have hdz : (d.work idx).cells 0 = Γ.start := by
        rw [hsel]
        exact Tape.write_move_cell0 Γ.blank .left hz
      obtain ⟨e, t, ht, he, hh, hres⟩ := ih idx d rfl hdc hdh hdz
        (by simpa only [hdi] using hi) (by simpa only [hdo] using ho)
        (fun j hj => by simpa only [hdw j hj] using hw j hj)
      refine ⟨e, t + 1, by simp only [List.length_append, List.length_singleton]; omega,
        .step (erase_step idx c hs hr) he, hh, hres.input_eq.trans hdi, hres.output_eq.trans hdo,
        (fun j hj => (hres.others j hj).trans (hdw j hj)), ?_, hres.zero⟩
      simpa only [BinaryTrimSuffix.append_false] using hres.normalized
    | true =>
      let d := cfg idx none false .right c
      have hread : (c.work idx).read ≠ Γ.start := by simp [hr, Γ.ofBool]
      have hsel : d.work idx = (c.work idx).move .right := move_selected idx .right c.work hread
      refine ⟨d, 1, by simp, .step (stop_step idx c hs (by simp [hr, Γ.ofBool])) .zero, rfl,
        cfg_input idx none false .right c hi, cfg_output idx none false .right c ho,
        (fun j hj => cfg_other idx j none false .right c hj (hw j hj)), ?_, ?_⟩
      · rw [hsel, BinaryTrimSuffix.append_true]
        exact ⟨by simp [Tape.move, hhead], hc.move .right⟩
      · simpa only [hsel, Tape.move_cells] using hz

end JointThermoComplexity.Complexity.BinaryTrimScan

#print axioms JointThermoComplexity.Complexity.BinaryTrimScan.scan
