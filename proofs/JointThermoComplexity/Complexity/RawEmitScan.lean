module
public import proofs.JointThermoComplexity.Complexity.RawEmitMachine

set_option autoImplicit false
@[expose] public section

/-! Exact literal work-buffer emission in one transition per bit and one final transition. -/

namespace JointThermoComplexity.Complexity.RawEmitScan
open _root_.Complexity
open _root_.Complexity.TM
open BinaryEmitMachine RawEmitMachine

variable {w : ℕ}

theorem scan (remaining : List Bool) : ∀ (before emitted : List Bool) (idx : Fin w) (c : Cfg w State),
    c.state = .read → (c.work idx).HasBinaryContent (before ++ remaining) →
    (c.work idx).head = before.length + 1 → c.input.read ≠ Γ.start →
    (∀ j, j ≠ idx → (c.work j).read ≠ Γ.start) →
    c.output.HasBinaryPrefix emitted → c.output.cells 0 = Γ.start →
    ∃ d t, t ≤ remaining.length + 1 ∧ (RawEmitMachine.machine idx).reachesIn t c d ∧
      (RawEmitMachine.machine idx).halted d ∧ d.input = c.input ∧
      (d.work idx).cells = (c.work idx).cells ∧
      (d.work idx).head = before.length + remaining.length + 1 ∧
      (∀ j, j ≠ idx → d.work j = c.work j) ∧
      d.output.HasBinaryPrefix (emitted ++ remaining) ∧ d.output.cells 0 = Γ.start := by
  induction remaining with
  | nil =>
    intro before emitted idx c hs hc hh hi hw hp hz
    have hsource : (c.work idx).HasBinaryContent before := by simpa only [List.append_nil] using hc
    have hr := BinaryTape.read_end before hsource hh
    have hwork : (fun j => transitionTape (c.work j)) = c.work := by
      funext j
      apply transitionTape_eq_self
      by_cases hj : j = idx
      · subst j; simp [hr]
      · exact hw j hj
    let d : Cfg w State := ⟨.done, transitionInput c.input,
      (fun j => transitionTape (c.work j)), transitionTape c.output⟩
    have hdin : d.input = c.input := transitionInput_eq_self hi
    have hdwork : d.work = c.work := hwork
    have hdout : d.output = c.output := transitionTape_eq_self (by simp [hp.read_blank])
    refine ⟨d, 1, by simp, .step (RawEmitMachine.end_step idx c hs hr) .zero, rfl,
      hdin, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdwork]
    · simpa only [hdwork, List.length_nil, Nat.add_zero] using hh
    · intro j _; exact congrFun hdwork j
    · simpa only [hdout, List.append_nil] using hp
    · simpa only [hdout] using hz
  | cons bit rest ih =>
    intro before emitted idx c hs hc hh hi hw hp hz
    have hr := BinaryTape.read_cons before rest bit hc hh
    have hsource : (c.work idx).read ≠ Γ.start := by rw [hr]; exact Γ.ofBool_ne_start bit
    let c₁ : Cfg w State := ⟨.read, transitionInput c.input, readWork idx c.work,
      c.output.writeAndMove (Γ.ofBool bit) .right⟩
    have hstep : (RawEmitMachine.machine idx).step c = some c₁ := RawEmitMachine.bit_step idx c bit hs hr
    have hi₁ : c₁.input = c.input := transitionInput_eq_self hi
    have hw₁ : c₁.work = Function.update c.work idx ((c.work idx).move .right) := by
      funext j
      change readWork idx c.work j = _
      by_cases hj : j = idx
      · subst j
        simp only [readWork, ↓reduceIte, Function.update_self]
        exact writeAndMove_readBack (c.work idx) hsource .right
      · rw [readWork, ite_eq_right hj, Function.update_of_ne hj]
        exact transitionTape_eq_self (hw j hj)
    have hc₁ : (c₁.work idx).HasBinaryContent ((before ++ [bit]) ++ rest) := by
      rw [hw₁, Function.update_self]
      simpa only [List.append_assoc, List.singleton_append] using hc.move .right
    have hh₁ : (c₁.work idx).head = (before ++ [bit]).length + 1 := by
      simp [hw₁, Tape.move, hh, Nat.add_assoc]
    have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [bit]) := Tape.hasBinaryPrefix_write_bit bit hp
    have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 bit hp hz
    have hother₁ : ∀ j, j ≠ idx → c₁.work j = c.work j := by
      intro j hj; rw [hw₁, Function.update_of_ne hj]
    obtain ⟨d, t, ht, hreach, hhalt, hinp, hcells, hhead, hother, hprefix, hzero⟩ :=
      ih (before ++ [bit]) (emitted ++ [bit]) idx c₁ rfl hc₁ hh₁
        (by simpa only [hi₁] using hi) (fun j hj => by simpa only [hother₁ j hj] using hw j hj) hp₁ hz₁
    refine ⟨d, t + 1, by simp only [List.length_cons]; omega,
      .step hstep hreach, hhalt, hinp.trans hi₁, ?_, ?_, ?_, ?_, hzero⟩
    · simpa only [hw₁, Function.update_self, Tape.move_cells] using hcells
    · simp only [List.length_append, List.length_singleton] at hhead
      simp only [List.length_cons]
      omega
    · intro j hj; exact (hother j hj).trans (hother₁ j hj)
    · simpa only [List.append_assoc, List.singleton_append] using hprefix

end JointThermoComplexity.Complexity.RawEmitScan

#print axioms JointThermoComplexity.Complexity.RawEmitScan.scan
