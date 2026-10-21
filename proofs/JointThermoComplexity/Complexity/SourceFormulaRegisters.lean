module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaQueueProof

set_option autoImplicit false
@[expose] public section

/-! A fixed compile-time tape layout with separate inner/outer pending registers. -/

namespace JointThermoComplexity.Complexity.SourceFormulaRegisters
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {n : ℕ}

structure Layout (n : ℕ) where
  tags : Fin 3 → Fin (n + 1)
  termFuel : Fin (n + 1)
  termPending : Fin (n + 1)
  formulaPending : Fin (n + 1)
  left : Fin (n + 1)
  right : Fin (n + 1)
  tagSep : SourceTermTagRead.Separate tags left right
  operandSep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n)
  termSep : SourcePendingFrame.Separate tags termPending left right
  formulaSep : SourcePendingFrame.Separate tags formulaPending left right
  fuelSep : SourcePendingFrame.Separate tags termFuel left right
  fuelTerm : termFuel ≠ termPending
  fuelFormula : termFuel ≠ formulaPending
  pendingDistinct : termPending ≠ formulaPending

structure Outside (d : Layout n) (j : Fin (n + 1)) : Prop where
  left : j ≠ d.left
  right : j ≠ d.right
  flag : j ≠ NaturalMachine.flagIndex n
  tags : ∀ i, j ≠ d.tags i
  termPending : j ≠ d.termPending
  termFuel : j ≠ d.termFuel
  formulaPending : j ≠ d.formulaPending

def Stable (d : Layout n) (R : (Fin (n + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, Outside d j → work' j = work j) → R work → R work'

structure Ready (d : Layout n) (L arity : ℕ) (R : (Fin (n + 1) → Tape) → Prop) (work : Fin (n + 2) → Tape) : Prop where
  base : SourceIndexField.Ready L d.left d.right arity R work
  termFuel : IsReg L (work d.termFuel.castSucc)
  termPending : ∃ q, q ≤ L + 2 ∧ IsReg q (work d.termPending.castSucc)
  tagHeads : ∀ i, (work (d.tags i).castSucc).head = 1

def Inv (d : Layout n) (L arity : ℕ) (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (s : SourceTermLoopState.State) : _root_.Complexity.TM.TapePred (n + 2) :=
  fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready d L arity R work ∧
    IsReg s.pending (work d.formulaPending.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.ofBool s.valid

theorem reframe (d : Layout n) (L arity : ℕ) (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R)
    (work work' : Fin (n + 2) → Tape) (h : Ready d L arity R work)
    (hw : ∀ j, j ≠ d.formulaPending.castSucc → j ≠ NaturalScanBuffer.flag n → work' j = work j)
    (hs : ∀ j, Parked (work' j)) (hz : ∀ j, (work' j).cells 0 = Γ.start)
    (hf : (work' (NaturalScanBuffer.flag n)).head = 1) : Ready d L arity R work' := by
  have hl := hw d.left.castSucc (SourcePendingFrame.cast_ne d.formulaSep.left.symm)
    (SourcePendingFrame.cast_ne d.operandSep.flagLeft.symm)
  have hr := hw d.right.castSucc (SourcePendingFrame.cast_ne d.formulaSep.right.symm)
    (SourcePendingFrame.cast_ne d.operandSep.flagRight.symm)
  have hb := hw (NaturalScanBuffer.buffer n) (SourcePendingFrame.buffer_ne d.formulaPending) NaturalScanBuffer.separate.symm
  have hFuel := hw d.termFuel.castSucc (SourcePendingFrame.cast_ne d.fuelFormula) (SourcePendingFrame.cast_ne d.fuelSep.flag)
  have hPending := hw d.termPending.castSucc (SourcePendingFrame.cast_ne d.pendingDistinct) (SourcePendingFrame.cast_ne d.termSep.flag)
  have hbase : SourceIndexField.Ready L d.left d.right arity R work' :=
    ⟨hs, hz, by simpa only [hb] using h.base.encoded, by simpa only [hl] using h.base.candidate,
      by simpa only [hr] using h.base.arityBits, by simpa only [hr] using h.base.arityZero, hf,
      hR _ _ (fun j hj => hw j.castSucc (SourcePendingFrame.cast_ne hj.formulaPending) (SourcePendingFrame.cast_ne hj.flag)) h.base.frame⟩
  have htags (i : Fin 3) : work' (d.tags i).castSucc = work (d.tags i).castSucc :=
    hw (d.tags i).castSucc (SourcePendingFrame.cast_ne (d.formulaSep.tags i).symm) (SourcePendingFrame.cast_ne (d.tagSep.flag i))
  exact ⟨hbase, by simpa only [hFuel] using h.termFuel, by simpa only [hPending] using h.termPending,
    fun i => by simpa only [htags i] using h.tagHeads i⟩

end JointThermoComplexity.Complexity.SourceFormulaRegisters

#print axioms JointThermoComplexity.Complexity.SourceFormulaRegisters.reframe
