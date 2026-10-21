module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementMachine
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementControl
public import proofs.JointThermoComplexity.Complexity.BinaryTape

set_option autoImplicit false
@[expose] public section

/-! Carry propagation changes exactly the binary suffix and preserves the full frame. -/

namespace JointThermoComplexity.Complexity.BinaryIncrementScan
open _root_.Complexity
open _root_.Complexity.TM
open BinaryIncrementMachine BinaryIncrementControl

variable {w : ℕ}

theorem changed_other (idx j : Fin w) (bit : Bool) (dir : Dir3) (work : Fin w → Tape)
    (hj : j ≠ idx) (hw : (work j).read ≠ Γ.start) : changedWork idx bit dir work j = work j := by
  rw [changedWork, ite_eq_right hj]
  exact transitionTape_eq_self hw

theorem finish (idx : Fin w) (c : Cfg w State) (bits : List Bool) (hs : c.state = .carry)
    (hr : (c.work idx).read = Γ.zero ∨ (c.work idx).read = Γ.blank)
    (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start)
    (hw : ∀ j, j ≠ idx → (c.work j).read ≠ Γ.start)
    (hbits : ((c.work idx).write Γ.one).HasBinaryContent bits)
    (hz : (c.work idx).cells 0 = Γ.start) :
    ∃ d, (machine idx).step c = some d ∧ d.state = .rewind .moveLeft ∧
      d.input = c.input ∧ d.output = c.output ∧ (∀ j, j ≠ idx → d.work j = c.work j) ∧
      (d.work idx).HasBinaryContent bits ∧ (d.work idx).cells 0 = Γ.start ∧
      (d.work idx).head = (c.work idx).head := by
  let d : Cfg w State := ⟨.rewind .moveLeft, transitionInput c.input,
    changedWork idx true .stay c.work, transitionTape c.output⟩
  refine ⟨d, finish_step idx c hs hr, rfl, transitionInput_eq_self hi, transitionTape_eq_self ho,
    (fun j hj => changed_other idx j true .stay c.work hj (hw j hj)), ?_, ?_, ?_⟩
  · simpa [d, changedWork, Γ.ofBool, Tape.writeAndMove, Tape.move] using hbits
  · simpa only [d, changedWork, ↓reduceIte, Γ.ofBool, Tape.writeAndMove] using Tape.write_move_cell0 Γ.one .stay hz
  · simp [d, changedWork, Tape.writeAndMove, Tape.move, Tape.write_head]

theorem scan (remaining : List Bool) : ∀ (before : List Bool) (idx : Fin w) (c : Cfg w State),
    c.state = .carry → (c.work idx).HasBinaryContent (before ++ remaining) →
    (c.work idx).head = before.length + 1 → (c.work idx).cells 0 = Γ.start →
    c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
    (∀ j, j ≠ idx → (c.work j).read ≠ Γ.start) →
    ∃ d t, t ≤ remaining.length + 1 ∧ (machine idx).reachesIn t c d ∧ d.state = .rewind .moveLeft ∧
      d.input = c.input ∧ d.output = c.output ∧ (∀ j, j ≠ idx → d.work j = c.work j) ∧
      (d.work idx).HasBinaryContent (before ++ increment remaining) ∧ (d.work idx).cells 0 = Γ.start ∧
      1 ≤ (d.work idx).head ∧ (d.work idx).head ≤ before.length + remaining.length + 1 := by
  induction remaining with
  | nil =>
    intro before idx c hs hc hh hz hi ho hw
    have hc' : (c.work idx).HasBinaryContent before := by simpa only [List.append_nil] using hc
    have hread := BinaryTape.read_end before hc' hh
    have hwrite : ((c.work idx).write Γ.one).HasBinaryContent (before ++ [true]) := BinaryTape.append before true hc' hh
    obtain ⟨d, hstep, hstate, hinp, hout, hwork, hbits, hzero, hhead⟩ :=
      finish idx c (before ++ [true]) hs (Or.inr hread) hi ho hw hwrite hz
    exact ⟨d, 1, by simp, .step hstep .zero, hstate, hinp, hout, hwork, hbits, hzero,
      by rw [hhead, hh]; omega, by rw [hhead, hh]; simp⟩
  | cons bit rest ih =>
    intro before idx c hs hc hh hz hi ho hw
    have hread := BinaryTape.read_cons before rest bit hc hh
    cases bit with
    | false =>
      have hwrite : ((c.work idx).write Γ.one).HasBinaryContent (before ++ true :: rest) :=
        BinaryTape.overwrite before rest false true hc hh
      obtain ⟨d, hstep, hstate, hinp, hout, hwork, hbits, hzero, hhead⟩ :=
        finish idx c (before ++ true :: rest) hs (Or.inl hread) hi ho hw hwrite hz
      exact ⟨d, 1, by simp, .step hstep .zero, hstate, hinp, hout, hwork, hbits, hzero,
        by rw [hhead, hh]; omega, by rw [hhead, hh]; simp⟩
    | true =>
      let d : Cfg w State := ⟨.carry, transitionInput c.input, changedWork idx false .right c.work, transitionTape c.output⟩
      have hstep : (machine idx).step c = some d := carry_step idx c hs hread
      have hdin : d.input = c.input := transitionInput_eq_self hi
      have hdout : d.output = c.output := transitionTape_eq_self ho
      have hdwork : ∀ j, j ≠ idx → d.work j = c.work j :=
        fun j hj => changed_other idx j false .right c.work hj (hw j hj)
      have hcontent : (d.work idx).HasBinaryContent ((before ++ [false]) ++ rest) := by
        have h := (BinaryTape.overwrite before rest true false hc hh).move .right
        simpa only [d, changedWork, ↓reduceIte, Γ.ofBool, List.append_assoc, List.singleton_append] using h
      have hhead : (d.work idx).head = (before ++ [false]).length + 1 := by
        simp [d, changedWork, Tape.writeAndMove, Tape.move, Tape.write_head, hh, Nat.add_assoc]
      have hzero : (d.work idx).cells 0 = Γ.start := by
        simpa only [d, changedWork, ↓reduceIte, Γ.ofBool, Tape.writeAndMove] using Tape.write_move_cell0 Γ.zero .right hz
      obtain ⟨e, t, ht, hreach, hstate, hinp, hout, hwork, hbits, hezero, hepos, hehead⟩ :=
        ih (before ++ [false]) idx d rfl hcontent hhead hzero
          (by simpa only [hdin] using hi) (by simpa only [hdout] using ho)
          (fun j hj => by simpa only [hdwork j hj] using hw j hj)
      refine ⟨e, t + 1, by simp only [List.length_cons]; omega, .step hstep hreach,
        hstate, hinp.trans hdin, hout.trans hdout, ?_, ?_, hezero, hepos, ?_⟩
      · intro j hj
        exact (hwork j hj).trans (hdwork j hj)
      · simpa only [increment, List.append_assoc, List.singleton_append] using hbits
      · simp only [List.length_append, List.length_singleton] at hehead
        simp only [List.length_cons]
        omega

end JointThermoComplexity.Complexity.BinaryIncrementScan

#print axioms JointThermoComplexity.Complexity.BinaryIncrementScan.scan
