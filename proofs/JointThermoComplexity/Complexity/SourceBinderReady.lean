module
public import proofs.JointThermoComplexity.Complexity.SourceBinderBuffer

set_option autoImplicit false
@[expose] public section

/-! Place the source header count in the outer pending register without disturbing nested-parser state. -/

namespace JointThermoComplexity.Complexity.SourceBinderReady
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters BoxBufferState
variable {n : ℕ}

def permutation (d : Layout (n + 1)) : Fin (n + 2) ≃ Fin (n + 2) :=
  Equiv.swap (HeaderMachine.counterIndex n) d.formulaPending

theorem counter_eq (d : Layout (n + 1)) : HeaderAt.counter (permutation d) = d.formulaPending := by
  exact Equiv.swap_apply_left _ _

theorem flag_eq (d : Layout (n + 1)) : HeaderAt.flag (permutation d) = NaturalMachine.flagIndex (n + 1) := by
  exact Equiv.swap_apply_of_ne_of_ne (HeaderMachine.counter_ne_flag n).symm d.formulaSep.flag.symm

def afterHeader (before input : List Bool) : SourceTermLoopState.State :=
  ⟨before ++ HeaderControl.copied input, HeaderControl.suffix input, HeaderControl.count input, HeaderControl.valid input⟩

def machine (d : Layout (n + 1)) : TM (n + 3) := SourceBinderBuffer.machine (permutation d)

theorem hoareTime (d : Layout (n + 1)) (L : ℕ) (old : Bool) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 2) → Tape) → Prop) (hR : Stable d R) :
    (machine d).HoareTime
      (fun inp work out => Inv d L 0 emitted R ⟨before, input, 0, old⟩ inp work out ∧
        IsReg 0 (work (NaturalScanBuffer.buffer (n + 1))))
      (Inv d L 0 emitted R (afterHeader before input)) (2 * HeaderControl.count input + 5) := by
  rintro inp work out ⟨⟨hc, hr, hp, _hf⟩, hb⟩
  let C : (Fin (n + 3) → Tape) → Prop := fun work' => ∀ j,
    j ≠ SourceBinderBuffer.buffer n → j ≠ SourceBinderBuffer.counter (permutation d) →
      j ≠ SourceBinderBuffer.flag (permutation d) → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ SourceBinderBuffer.buffer n →
      j ≠ SourceBinderBuffer.counter (permutation d) → j ≠ SourceBinderBuffer.flag (permutation d) → work'' j = work' j) →
      C work' → C work'' := by
    intro work' work'' he hp j hjb hjc hjf
    exact (he j hjb hjc hjf).trans (hp j hjb hjc hjf)
  have hcounter : IsReg 0 (work (SourceBinderBuffer.counter (permutation d))) := by
    simpa only [SourceBinderBuffer.counter, counter_eq] using hp
  have hflag : (work (SourceBinderBuffer.flag (permutation d))).head = 1 := by
    simpa only [SourceBinderBuffer.flag, flag_eq, NaturalScanBuffer.flag] using hr.base.flagHead
  obtain ⟨c, t, ht, hd, hh, hc', hs', hbuf, hcount, hfh, hfv, hother⟩ :=
    SourceBinderBuffer.hoareTime (permutation d) before input emitted C hC inp work out
      ⟨hc, hr.base.safe, CountTape.empty_prefix_of_zero hb, hb.cell0, hcounter, hflag, fun _ _ _ _ => rfl⟩
  have he : ∀ j, j ≠ NaturalScanBuffer.buffer (n + 1) → j ≠ d.formulaPending.castSucc →
      j ≠ NaturalScanBuffer.flag (n + 1) → c.work j = work j := by
    simpa only [C, SourceBinderBuffer.buffer, SourceBinderBuffer.counter, SourceBinderBuffer.flag,
      counter_eq, flag_eq, NaturalScanBuffer.buffer, NaturalScanBuffer.flag] using hother
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.base.markers j, (hr.base.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hleft := he d.left.castSucc (SourcePendingFrame.buffer_ne d.left).symm
    (SourcePendingFrame.cast_ne d.formulaSep.left.symm) (SourcePendingFrame.cast_ne d.operandSep.flagLeft.symm)
  have hright := he d.right.castSucc (SourcePendingFrame.buffer_ne d.right).symm
    (SourcePendingFrame.cast_ne d.formulaSep.right.symm) (SourcePendingFrame.cast_ne d.operandSep.flagRight.symm)
  have hFuel := he d.termFuel.castSucc (SourcePendingFrame.buffer_ne d.termFuel).symm
    (SourcePendingFrame.cast_ne d.fuelFormula) (SourcePendingFrame.cast_ne d.fuelSep.flag)
  have hPending := he d.termPending.castSucc (SourcePendingFrame.buffer_ne d.termPending).symm
    (SourcePendingFrame.cast_ne d.pendingDistinct) (SourcePendingFrame.cast_ne d.termSep.flag)
  have htags (i : Fin 3) := he (d.tags i).castSucc (SourcePendingFrame.buffer_ne (d.tags i)).symm
    (SourcePendingFrame.cast_ne (d.formulaSep.tags i).symm) (SourcePendingFrame.cast_ne (d.tagSep.flag i))
  have henc : Reusable L (c.work (NaturalScanBuffer.buffer (n + 1))) :=
    hbuf.reusable (by have hbnd := HeaderControl.copied_length_le input; omega)
  have hr' : Ready d L 0 R c.work :=
    ⟨⟨hs', fun j => (hm.2.1 j).1, henc, by simpa only [hleft] using hr.base.candidate,
      by simpa only [hright] using hr.base.arityBits, by simpa only [hright] using hr.base.arityZero,
      by simpa only [SourceBinderBuffer.flag, flag_eq, NaturalScanBuffer.flag] using hfh,
      hR _ _ (fun j hj => he j.castSucc (SourcePendingFrame.buffer_ne j).symm
        (SourcePendingFrame.cast_ne hj.formulaPending) (SourcePendingFrame.cast_ne hj.flag)) hr.base.frame⟩,
      by simpa only [hFuel] using hr.termFuel, by simpa only [hPending] using hr.termPending,
      fun i => by simpa only [htags i] using hr.tagHeads i⟩
  exact ⟨c, t, ht, hd, hh, hc', hr',
    by simpa only [afterHeader, SourceBinderBuffer.counter, counter_eq] using hcount,
    by simpa only [afterHeader, SourceBinderBuffer.flag, flag_eq, NaturalScanBuffer.flag] using hfv⟩

end JointThermoComplexity.Complexity.SourceBinderReady

#print axioms JointThermoComplexity.Complexity.SourceBinderReady.hoareTime
