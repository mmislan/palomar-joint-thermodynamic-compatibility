module
public import proofs.JointThermoComplexity.Complexity.BinaryScaleFlush

set_option autoImplicit false
@[expose] public section

/-! One transition consumes each input bit, then a bounded finite carry flush
finishes the exact scaled word. Source contents and every other tape survive. -/

namespace JointThermoComplexity.Complexity.BinaryScaleScan
open _root_.Complexity _root_.Complexity.TM BinaryScaleMachine BinaryScaleControl
variable {w k : ℕ}

theorem scan (remaining : List Bool) : ∀ (before emitted : List Bool) (idx : Fin w)
    (carry : Fin (k + 1)) (c : Cfg w (State k)),
    c.state = .scan carry → (c.work idx).HasBinaryContent (before ++ remaining) →
    (c.work idx).head = before.length + 1 → c.input.read ≠ Γ.start →
    (∀ j, j ≠ idx → (c.work j).read ≠ Γ.start) →
    c.output.HasBinaryPrefix emitted → c.output.cells 0 = Γ.start →
    ∃ d t, t ≤ remaining.length + k + 2 ∧ (machine k idx).reachesIn t c d ∧
      (machine k idx).halted d ∧ d.input = c.input ∧
      (d.work idx).cells = (c.work idx).cells ∧
      (d.work idx).head = before.length + remaining.length + 1 ∧
      (∀ j, j ≠ idx → d.work j = c.work j) ∧
      d.output.HasBinaryPrefix (emitted ++ scale k carry.val remaining) ∧ d.output.cells 0 = Γ.start := by
  induction remaining with
  | nil =>
    intro before emitted idx carry c hs hc hh hi hw hp hz
    have hsource : (c.work idx).HasBinaryContent before := by simpa only [List.append_nil] using hc
    have hr := BinaryTape.read_end before hsource hh
    have hwork : (fun j => transitionTape (c.work j)) = c.work := by
      funext j
      apply transitionTape_eq_self
      by_cases hj : j = idx
      · subst j
        simp [hr]
      · exact hw j hj
    let c₀ : Cfg w (State k) := ⟨.flush carry, transitionInput c.input,
      (fun j => transitionTape (c.work j)), transitionTape c.output⟩
    have hi₀ : c₀.input = c.input := transitionInput_eq_self hi
    have hw₀ : c₀.work = c.work := hwork
    have ho₀ : c₀.output = c.output := transitionTape_eq_self (by simp [hp.read_blank])
    obtain ⟨d, t, ht, hreach, hhalt, hinp, hworks, hprefix, hzero⟩ :=
      BinaryScaleFlush.run idx carry c₀ emitted rfl (by simpa only [hi₀] using hi)
        (fun j => by rw [hw₀]; by_cases hj : j = idx
                     · subst j; simp [hr]
                     · exact hw j hj)
        (by simpa only [ho₀] using hp) (by simpa only [ho₀] using hz)
    have hdwork : d.work = c.work := hworks.trans hw₀
    have hlen := BinaryIncrementControl.bits_length_le carry.val
    have hcarry := carry.isLt
    refine ⟨d, t + 1, by simp only [List.length_nil]; omega,
      .step (end_step idx carry c hs hr) hreach, hhalt, hinp.trans hi₀, ?_, ?_, ?_, ?_, hzero⟩
    · rw [hdwork]
    · simpa only [hdwork, List.length_nil, Nat.add_zero] using hh
    · intro j _
      exact congrFun hdwork j
    · exact hprefix
  | cons b rest ih =>
    intro before emitted idx carry c hs hc hh hi hw hp hz
    have hr := BinaryTape.read_cons before rest b hc hh
    have hsource : (c.work idx).read ≠ Γ.start := by rw [hr]; exact Γ.ofBool_ne_start b
    let c₁ : Cfg w (State k) := ⟨.scan (nextCarry carry b), transitionInput c.input,
      BinaryEmitMachine.readWork idx c.work,
      c.output.writeAndMove (Γ.ofBool (digit k carry.val b)) .right⟩
    have hstep : (machine k idx).step c = some c₁ := bit_step idx carry c b hs hr
    have hi₁ : c₁.input = c.input := transitionInput_eq_self hi
    have hw₁ : c₁.work = Function.update c.work idx ((c.work idx).move .right) := by
      funext j
      change BinaryEmitMachine.readWork idx c.work j = _
      by_cases hj : j = idx
      · subst j
        simp only [BinaryEmitMachine.readWork, ↓reduceIte, Function.update_self]
        exact writeAndMove_readBack (c.work idx) hsource .right
      · rw [BinaryEmitMachine.readWork, ite_eq_right hj, Function.update_of_ne hj]
        exact transitionTape_eq_self (hw j hj)
    have hc₁ : (c₁.work idx).HasBinaryContent ((before ++ [b]) ++ rest) := by
      rw [hw₁, Function.update_self]
      simpa only [List.append_assoc, List.singleton_append] using hc.move .right
    have hh₁ : (c₁.work idx).head = (before ++ [b]).length + 1 := by
      simp [hw₁, Tape.move, hh, Nat.add_assoc]
    have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [digit k carry.val b]) :=
      Tape.hasBinaryPrefix_write_bit _ hp
    have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 _ hp hz
    have hother₁ : ∀ j, j ≠ idx → c₁.work j = c.work j := by
      intro j hj
      rw [hw₁, Function.update_of_ne hj]
    obtain ⟨d, t, ht, hreach, hhalt, hinp, hcells, hhead, hother, hprefix, hzero⟩ :=
      ih (before ++ [b]) (emitted ++ [digit k carry.val b]) idx (nextCarry carry b) c₁ rfl hc₁ hh₁
        (by simpa only [hi₁] using hi) (fun j hj => by simpa only [hother₁ j hj] using hw j hj) hp₁ hz₁
    refine ⟨d, t + 1, by simp only [List.length_cons]; omega,
      .step hstep hreach, hhalt, hinp.trans hi₁, ?_, ?_, ?_, ?_, hzero⟩
    · simpa only [hw₁, Function.update_self, Tape.move_cells] using hcells
    · simp only [List.length_append, List.length_singleton] at hhead
      simp only [List.length_cons]
      omega
    · intro j hj
      exact (hother j hj).trans (hother₁ j hj)
    · simpa only [scale, nextCarry, List.append_assoc, List.singleton_append] using hprefix

end JointThermoComplexity.Complexity.BinaryScaleScan

#print axioms JointThermoComplexity.Complexity.BinaryScaleScan.scan
