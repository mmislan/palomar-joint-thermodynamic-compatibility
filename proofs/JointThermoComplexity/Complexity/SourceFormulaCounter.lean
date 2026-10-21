module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaRegisters

set_option autoImplicit false
@[expose] public section

/-! Outer formula-counter and status operations preserve the nested parser registers. -/

namespace JointThermoComplexity.Complexity.SourceFormulaCounter
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
variable {n : ℕ}

def moveCount (up : Bool) (v : ℕ) : ℕ := if up then v + 2 else v
def move (d : Layout n) (up : Bool) : TM (n + 2) :=
  if up then UnarySuccessor.machine d.formulaPending.castSucc else UnaryPredecessor.machine d.formulaPending.castSucc

theorem move_hoareTime (d : Layout n) (up : Bool) (L arity v : ℕ) (valid : Bool)
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (move d up).HoareTime (Inv d L arity emitted R ⟨before, input, v + 1, valid⟩)
      (Inv d L arity emitted R ⟨before, input, moveCount up v, valid⟩) (2 * v + 12) := by
  rintro inp work out ⟨hc, hr, hp, hf⟩
  let C : (Fin (n + 2) → Tape) → Prop := fun work' => ∀ j, j ≠ d.formulaPending.castSucc → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ d.formulaPending.castSucc → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  have hraw : (move d up).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (v + 1) (work d.formulaPending.castSucc) ∧ C work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (moveCount up v) (work d.formulaPending.castSucc) ∧ C work) (2 * v + 12) := by
    cases up with
    | false => simpa only [move, moveCount, Bool.false_eq_true, ↓reduceIte] using
        UnaryPredecessor.hoareTime d.formulaPending.castSucc v before input emitted C hC
    | true =>
      have h := UnarySuccessor.hoareTime d.formulaPending.castSucc (v + 1) before input emitted C hC
      simpa only [move, moveCount, ↓reduceIte, Nat.add_assoc] using
        h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 2 * (v + 1) + 6 ≤ 2 * v + 12)
  obtain ⟨c, t, ht, hd, hh, hc', hs', hp', hother⟩ := hraw inp work out ⟨hc, hr.base.safe, hp, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.base.markers j, (hr.base.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hflag := hother (NaturalScanBuffer.flag n) (SourcePendingFrame.cast_ne d.formulaSep.flag.symm)
  have hr' := SourceFormulaRegisters.reframe d L arity R hR work c.work hr (fun j hj _ => hother j hj)
    hs' (fun j => (hm.2.1 j).1) (by simpa only [hflag] using hr.base.flagHead)
  exact ⟨c, t, ht, hd, hh, hc', hr', hp', by simpa only [hflag] using hf⟩

theorem status_hoareTime (d : Layout n) (L arity count : ℕ) (old value : Bool)
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (SourceTermToken.setStatus (NaturalScanBuffer.flag n) value).HoareTime
      (Inv d L arity emitted R ⟨before, input, count, old⟩)
      (Inv d L arity emitted R ⟨before, input, count, value⟩) 1 := by
  rintro inp work out ⟨hc, hr, hp, _hf⟩
  let C : (Fin (n + 2) → Tape) → Prop := fun work' => ∀ j, j ≠ NaturalScanBuffer.flag n → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ NaturalScanBuffer.flag n → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨c, t, ht, hd, hh, hc', hs', hfh', hv', hother⟩ :=
    SourceTermToken.setStatus_hoareTime (NaturalScanBuffer.flag n) value before input emitted C hC
      inp work out ⟨hc, hr.base.safe, hr.base.flagHead, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.base.markers j, (hr.base.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hr' := SourceFormulaRegisters.reframe d L arity R hR work c.work hr (fun j _ hj => hother j hj)
    hs' (fun j => (hm.2.1 j).1) hfh'
  have hpend := hother d.formulaPending.castSucc (SourcePendingFrame.cast_ne d.formulaSep.flag)
  exact ⟨c, t, ht, hd, hh, hc', hr', by simpa only [hpend] using hp, hv'⟩

def decrementIf (d : Layout n) : TM (n + 2) :=
  FlagBranch.machine (NaturalScanBuffer.flag n) (move d false) (emitBitsTM [])

theorem decrementIf_hoareTime (d : Layout n) (L arity v : ℕ) (valid : Bool)
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (decrementIf d).HoareTime (Inv d L arity emitted R ⟨before, input, v + 1, valid⟩)
      (Inv d L arity emitted R ⟨before, input, if valid then v else v + 1, valid⟩) (2 * v + 14) := by
  cases valid with
  | false =>
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready d L arity R work ∧
      IsReg (v + 1) (work d.formulaPending.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.zero
    have hem := FixedOutput.hoareTime (w := n + 2) [] before input emitted P
    have hno : (emitBitsTM (n := n + 2) []).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before input emitted inp work out ∧ P work) 0 :=
      hem.consequence (by rintro inp work out ⟨hc, hr, hp⟩; exact ⟨hc, hr.base.safe, hr, hp⟩)
        (by simpa only [List.append_nil] using fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl
    have hb := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag n) (move d false) (emitBitsTM [])
      before input emitted before input emitted P P 0 hno
    exact hb.consequence (fun _ _ _ h => ⟨h, h.2.2.2⟩) (fun _ _ _ h => h) (by omega)
  | true =>
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready d L arity R work ∧
      IsReg (v + 1) (work d.formulaPending.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.one
    let Q : (Fin (n + 2) → Tape) → Prop := fun work => Ready d L arity R work ∧
      IsReg v (work d.formulaPending.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.one
    have hy := move_hoareTime d false L arity v true before input emitted R hR
    have hb := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag n) (move d false) (emitBitsTM [])
      before input emitted before input emitted P Q (2 * v + 12) hy
    exact hb.consequence (fun _ _ _ h => ⟨h, h.2.2.2⟩) (fun _ _ _ h => h) (by omega)

end JointThermoComplexity.Complexity.SourceFormulaCounter

#print axioms JointThermoComplexity.Complexity.SourceFormulaCounter.move_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaCounter.status_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaCounter.decrementIf_hoareTime
