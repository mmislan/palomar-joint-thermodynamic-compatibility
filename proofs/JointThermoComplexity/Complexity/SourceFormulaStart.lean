module
public import proofs.JointThermoComplexity.Complexity.SourceArityBuild
public import proofs.JointThermoComplexity.Complexity.UnaryReset

set_option autoImplicit false
@[expose] public section

/-! Reset the temporary binder count to one pending formula, preserving its parsed validity. -/

namespace JointThermoComplexity.Complexity.SourceFormulaStart
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
variable {w n : ℕ}

def resetOne (pending : Fin w) : TM w := seqTM (clearWorkTM pending) (UnarySuccessor.machine pending)

theorem resetOne_hoareTime (pending : Fin w) (old : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ pending → work' j = work j) → R work → R work') :
    (resetOne pending).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg old (work pending) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg 1 (work pending) ∧ R work)
      (2 * old + 12) := by
  have hr := UnaryReset.hoareTime pending old before input emitted R hR
  have hs := UnarySuccessor.hoareTime pending 0 before input emitted R hR
  have h := seqTM_hoareTime (clearWorkTM pending) (UnarySuccessor.machine pending) hr (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) hs
  exact h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega)

def machine (d : Layout n) : TM (n + 2) := resetOne d.formulaPending.castSucc

theorem hoareTime (d : Layout n) (L arity old : ℕ) (valid : Bool) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d).HoareTime (Inv d L arity emitted R ⟨before, input, old, valid⟩)
      (Inv d L arity emitted R ⟨before, input, 1, valid⟩) (2 * old + 12) := by
  rintro inp work out ⟨hc, hr, hp, hf⟩
  let C : (Fin (n + 2) → Tape) → Prop := fun work' => ∀ j, j ≠ d.formulaPending.castSucc → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ d.formulaPending.castSucc → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨c, t, ht, hd, hh, hc', hs', hp', hother⟩ :=
    resetOne_hoareTime d.formulaPending.castSucc old before input emitted C hC
      inp work out ⟨hc, hr.base.safe, hp, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.base.markers j, (hr.base.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hflag := hother (NaturalScanBuffer.flag n) (SourcePendingFrame.cast_ne d.formulaSep.flag.symm)
  have hr' := SourceFormulaRegisters.reframe d L arity R hR work c.work hr (fun j hj _ => hother j hj)
    hs' (fun j => (hm.2.1 j).1) (by simpa only [hflag] using hr.base.flagHead)
  exact ⟨c, t, ht, hd, hh, hc', hr', hp', by simpa only [hflag] using hf⟩

end JointThermoComplexity.Complexity.SourceFormulaStart

#print axioms JointThermoComplexity.Complexity.SourceFormulaStart.hoareTime
