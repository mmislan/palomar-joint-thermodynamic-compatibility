module
public import proofs.JointThermoComplexity.Complexity.DirectionFlagOutput
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! Actual mask and orientation reads choose a direction formula or the canonical truth clause. -/

namespace JointThermoComplexity.Complexity.MaskedDirectionOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt DirectionOutput RealSyntax

variable {w arity : ℕ}

def word (selected forward : Bool) (idx : Fin arity) : List Bool :=
  (if selected then NetworkFormula.directionFormula forward idx else Formula.truth).code

def machine (mask flag scratch source : Fin w) : TM w := FlagBranch.machine mask
  (DirectionFlagOutput.machine flag scratch source) (emitBitsTM (Formula.truth : Formula 0).code)

theorem hoareTime (mask flag scratch source : Fin w) (hne : source ≠ scratch)
    (selected forward : Bool) (idx : Fin arity) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine mask flag scratch source).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready scratch source idx.val R work ∧
        (work flag).read = Γ.ofBool forward ∧ (work mask).read = Γ.ofBool selected)
      (fun inp work out => Cursor before input (emitted ++ word selected forward idx) inp work out ∧
        Ready scratch source idx.val R work ∧ (work flag).read = Γ.ofBool forward)
      (VariableOutput.timeBound idx.val + 18) := by
  let P : (Fin w → Tape) → Prop := fun work => Ready scratch source idx.val R work ∧ (work flag).read = Γ.ofBool forward
  have hy := DirectionFlagOutput.hoareTime flag scratch source hne forward idx before input emitted R
  have hn : (emitBitsTM (Formula.truth : Formula 0).code).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before input (emitted ++ (Formula.truth : Formula arity).code) inp work out ∧ P work) 3 := by
    have h := FixedOutput.hoareTime (Formula.truth : Formula 0).code before input emitted
      (fun work => BinaryIncrementRun.Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧
        R work ∧ (work flag).read = Γ.ofBool forward)
    exact h.consequence (by
      rintro inp work out ⟨hc, ⟨hs, hz, hi, hr⟩, hf⟩
      exact ⟨hc, hs, hz, hi, hr, hf⟩) (by
        rintro inp work out ⟨hc, hs, hz, hi, hr, hf⟩
        exact ⟨hc, ⟨hs, hz, hi, hr⟩, hf⟩) (by rfl)
  cases selected
  · have hb := FlagBranchRun.no_hoareTime mask (DirectionFlagOutput.machine flag scratch source)
      (emitBitsTM (Formula.truth : Formula 0).code) before input emitted before input
      (emitted ++ (Formula.truth : Formula arity).code) P P 3 hn
    rintro inp work out ⟨hc, hp, hf, hm⟩
    obtain ⟨d, t, ht, hr, hh, hdc, hdp, hdf⟩ := hb inp work out ⟨⟨hc, hp, hf⟩, hm⟩
    exact ⟨d, t, by omega, hr, hh, hdc, hdp, hdf⟩
  · have hb := FlagBranchRun.yes_hoareTime mask (DirectionFlagOutput.machine flag scratch source)
      (emitBitsTM (Formula.truth : Formula 0).code) before input emitted before input
      (emitted ++ (NetworkFormula.directionFormula forward idx).code) P P (VariableOutput.timeBound idx.val + 16) hy
    rintro inp work out ⟨hc, hp, hf, hm⟩
    obtain ⟨d, t, ht, hr, hh, hdc, hdp, hdf⟩ := hb inp work out ⟨⟨hc, hp, hf⟩, hm⟩
    exact ⟨d, t, by omega, hr, hh, hdc, hdp, hdf⟩

end JointThermoComplexity.Complexity.MaskedDirectionOutput

#print axioms JointThermoComplexity.Complexity.MaskedDirectionOutput.hoareTime
