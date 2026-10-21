module
public import proofs.JointThermoComplexity.Complexity.DirectionOutput
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! An actual retained orientation bit selects the exact forward or reverse formula. -/

namespace JointThermoComplexity.Complexity.DirectionFlagOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt DirectionOutput

variable {w arity : ℕ}

def machine (flag scratch source : Fin w) : TM w :=
  FlagBranch.machine flag (DirectionOutput.machine scratch source true) (DirectionOutput.machine scratch source false)

theorem hoareTime (flag scratch source : Fin w) (hne : source ≠ scratch) (forward : Bool) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine flag scratch source).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready scratch source idx.val R work ∧
        (work flag).read = Γ.ofBool forward)
      (fun inp work out => Cursor before input (emitted ++ (NetworkFormula.directionFormula forward idx).code) inp work out ∧
        Ready scratch source idx.val R work ∧ (work flag).read = Γ.ofBool forward)
      (VariableOutput.timeBound idx.val + 16) := by
  let P : (Fin w → Tape) → Prop := fun work => Ready scratch source idx.val R work ∧ (work flag).read = Γ.ofBool forward
  have hc (b : Bool) : (DirectionOutput.machine scratch source b).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before input (emitted ++ (NetworkFormula.directionFormula b idx).code) inp work out ∧ P work)
      (VariableOutput.timeBound idx.val + 14) :=
    (DirectionOutput.hoareTime scratch source hne b idx before input emitted
      (fun work => R work ∧ (work flag).read = Γ.ofBool forward)).consequence (by
        rintro inp work out ⟨hc, ⟨hs, hz, hi, hr⟩, hf⟩
        exact ⟨hc, hs, hz, hi, hr, hf⟩) (by
          rintro inp work out ⟨hc, hs, hz, hi, hr, hf⟩
          exact ⟨hc, ⟨hs, hz, hi, hr⟩, hf⟩) le_rfl
  cases forward
  · have hb := FlagBranchRun.no_hoareTime flag (DirectionOutput.machine scratch source true)
      (DirectionOutput.machine scratch source false) before input emitted before input
      (emitted ++ (NetworkFormula.directionFormula false idx).code) P P (VariableOutput.timeBound idx.val + 14) (hc false)
    rintro inp work out ⟨hc, hp, hf⟩
    obtain ⟨d, t, ht, hr, hh, hdc, hdp, hdf⟩ := hb inp work out ⟨⟨hc, hp, hf⟩, hf⟩
    exact ⟨d, t, by omega, hr, hh, hdc, hdp, hdf⟩
  · have hb := FlagBranchRun.yes_hoareTime flag (DirectionOutput.machine scratch source true)
      (DirectionOutput.machine scratch source false) before input emitted before input
      (emitted ++ (NetworkFormula.directionFormula true idx).code) P P (VariableOutput.timeBound idx.val + 14) (hc true)
    rintro inp work out ⟨hc, hp, hf⟩
    obtain ⟨d, t, ht, hr, hh, hdc, hdp, hdf⟩ := hb inp work out ⟨⟨hc, hp, hf⟩, hf⟩
    exact ⟨d, t, by omega, hr, hh, hdc, hdp, hdf⟩

end JointThermoComplexity.Complexity.DirectionFlagOutput

#print axioms JointThermoComplexity.Complexity.DirectionFlagOutput.hoareTime
