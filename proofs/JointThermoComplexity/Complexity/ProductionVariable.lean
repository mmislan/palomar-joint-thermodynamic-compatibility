module
public import proofs.JointThermoComplexity.Complexity.ProductionTermFrame
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Emit a shared-current variable from its actual address while retaining reusable production operands and indices. -/

namespace JointThermoComplexity.Complexity.ProductionVariable
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts

variable {arity : ℕ}

def machine (m : ℕ) : TM (m + 20) := VariableOutput.machine (current m) (PowerPorts.scratch (m + 7))

theorem state_frame (m L n ri si : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ current m → j ≠ PowerPorts.scratch (m + 7) → work' j = work j)
    (hs : ∀ j, Parked (work' j)) (hp : ProductionOperandLoad.State m L n ri si work) :
    ProductionOperandLoad.State m L n ri si work' := by
  have hx (j : Fin (m + 20)) (hj : j.val = 6 ∨ 8 ≤ j.val) : work' j = work j := by
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 5 at hv; omega
  exact ⟨hs, by simpa only [hx (left m) (Or.inr (by change 8 ≤ (9 : ℕ); omega))] using hp.productReusable,
    by simpa only [hx (right m) (Or.inr (by change 8 ≤ (10 : ℕ); omega))] using hp.reactantReusable,
    by simpa only [hx (magnitude m) (Or.inr (by change 8 ≤ (8 : ℕ); omega))] using hp.magnitudeReusable,
    by simpa only [hx (sign m) (Or.inr (by change 8 ≤ (11 : ℕ); omega))] using hp.signHead,
    by simpa only [hx (species m) (Or.inr (by change 8 ≤ (12 : ℕ); omega))] using hp.speciesPosition,
    by simpa only [hx (count m) (Or.inr (by change 8 ≤ m + 15; omega))] using hp.speciesCount,
    by simpa only [hx (reaction m) (Or.inl rfl)] using hp.reactionPosition⟩

theorem hoareTime (m L n ri si : ℕ) (idx : Fin arity) (hidx : idx.val ≤ 4 * L)
    (before remaining emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', ProductionTermFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n ri si work ∧
        IsReg idx.val (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work)
      (fun inp work out => Cursor before remaining (emitted ++ (RealSyntax.Term.var idx).code) inp work out ∧
        ProductionOperandLoad.State m L n ri si work ∧ IsReg idx.val (work (current m)) ∧
        BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work)
      (32 * L ^ 2 + 48 * L + 18) := by
  rintro inp work out ⟨hc, hp, hi, hz, hr⟩
  let P : (Fin (m + 20) → Tape) → Prop := fun work' =>
    ∀ j, j ≠ current m → j ≠ PowerPorts.scratch (m + 7) → work' j = work j
  have hP : ∀ work' work'',
      (∀ j, j ≠ current m → j ≠ PowerPorts.scratch (m + 7) → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj hz
    exact (hw j hj hz).trans (hp j hj hz)
  have hne : current m ≠ PowerPorts.scratch (m + 7) := by
    intro he; have hv := congrArg Fin.val he; change (7 : ℕ) = 5 at hv; omega
  obtain ⟨d, t, ht, hd, hh, hc', hs, hi', hz', hw⟩ :=
    VariableOutput.hoareTime (current m) (PowerPorts.scratch (m + 7)) hne idx before remaining emitted P hP
      inp work out ⟨hc, hp.safe, hi, hz, fun _ _ _ => rfl⟩
  exact ⟨d, t, ht.trans (TemplateRuntime.variable_bound hidx), hd, hh, hc',
    state_frame m L n ri si work d.work hw hs hp, hi', hz',
    hR work d.work (ProductionTermFrame.of_variable m work d.work hw) hr⟩

end JointThermoComplexity.Complexity.ProductionVariable

#print axioms JointThermoComplexity.Complexity.ProductionVariable.state_frame
#print axioms JointThermoComplexity.Complexity.ProductionVariable.hoareTime
