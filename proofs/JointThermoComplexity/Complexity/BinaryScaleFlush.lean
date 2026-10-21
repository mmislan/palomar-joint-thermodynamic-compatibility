module
public import proofs.JointThermoComplexity.Complexity.BinaryScaleMachine

set_option autoImplicit false
@[expose] public section

/-! The finite carry flush emits its canonical bits and preserves every input
and work tape. Its transition count is linear in the carry bit length. -/

namespace JointThermoComplexity.Complexity.BinaryScaleFlush
open _root_.Complexity _root_.Complexity.TM BinaryScaleMachine
variable {w k : ℕ}

theorem run (idx : Fin w) (carry : Fin (k + 1)) (c : Cfg w (State k)) (emitted : List Bool)
    (hs : c.state = .flush carry) (hi : c.input.read ≠ Γ.start)
    (hw : ∀ j, (c.work j).read ≠ Γ.start)
    (hp : c.output.HasBinaryPrefix emitted) (hz : c.output.cells 0 = Γ.start) :
    ∃ d t, t ≤ carry.val.bits.length + 1 ∧ (machine k idx).reachesIn t c d ∧
      (machine k idx).halted d ∧ d.input = c.input ∧ d.work = c.work ∧
      d.output.HasBinaryPrefix (emitted ++ carry.val.bits) ∧ d.output.cells 0 = Γ.start := by
  have hw0 : (fun j => transitionTape (c.work j)) = c.work := by
    funext j
    exact transitionTape_eq_self (hw j)
  by_cases hc : carry.val = 0
  · let d : Cfg w (State k) := ⟨.done, transitionInput c.input,
      (fun j => transitionTape (c.work j)), transitionTape c.output⟩
    have hdin : d.input = c.input := transitionInput_eq_self hi
    have hdwork : d.work = c.work := hw0
    have hdout : d.output = c.output := transitionTape_eq_self (by simp [hp.read_blank])
    refine ⟨d, 1, by simp [hc], .step (flush_zero_step idx carry c hs hc) .zero, rfl,
      hdin, hdwork, ?_, ?_⟩
    · simpa only [hdout, hc, Nat.zero_bits, List.append_nil] using hp
    · simpa only [hdout] using hz
  · let b : Bool := decide (carry.val % 2 = 1)
    let c₁ : Cfg w (State k) := ⟨.flush (half carry), transitionInput c.input,
      (fun j => transitionTape (c.work j)), c.output.writeAndMove (Γ.ofBool b) .right⟩
    have hstep : (machine k idx).step c = some c₁ := flush_bit_step idx carry c hs hc
    have hi₁ : c₁.input = c.input := transitionInput_eq_self hi
    have hw₁ : c₁.work = c.work := hw0
    have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [b]) := Tape.hasBinaryPrefix_write_bit b hp
    have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 b hp hz
    obtain ⟨d, t, ht, hreach, hhalt, hinp, hwork, hprefix, hzero⟩ :=
      run idx (half carry) c₁ (emitted ++ [b]) rfl (by simpa only [hi₁] using hi)
        (fun j => by simpa only [hw₁] using hw j) hp₁ hz₁
    have hb : b :: (half carry).val.bits = carry.val.bits :=
      BinaryScaleCanonical.finish_bits carry.val (Nat.pos_of_ne_zero hc)
    have hlen := congrArg List.length hb
    simp only [List.length_cons] at hlen
    refine ⟨d, t + 1, by omega, .step hstep hreach, hhalt, hinp.trans hi₁, hwork.trans hw₁, ?_, hzero⟩
    simpa only [List.append_assoc, List.singleton_append, hb] using hprefix
termination_by carry.val
decreasing_by
  dsimp [half]
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)

end JointThermoComplexity.Complexity.BinaryScaleFlush

#print axioms JointThermoComplexity.Complexity.BinaryScaleFlush.run
