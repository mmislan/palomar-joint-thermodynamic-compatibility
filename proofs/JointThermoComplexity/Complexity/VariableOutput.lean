module
public import proofs.JointThermoComplexity.Complexity.ReusableIndexEmitter
public import proofs.JointThermoComplexity.Complexity.FixedOutput
public import proofs.JointThermoComplexity.Complexity.SafeExecution
public import proofs.JointThermoComplexity.Complexity.RealSyntax

set_option autoImplicit false
@[expose] public section

/-! Emit the exact finite real-term variable code from a bounded index register. -/

namespace JointThermoComplexity.Complexity.VariableOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w arity : ℕ}

def tag : List Bool := [false, false, true]

def machine (fuel scratch : Fin w) : TM w :=
  seqTM (emitBitsTM tag) (ReusableIndexEmitter.machine fuel scratch)

def timeBound (v : ℕ) : ℕ := ReusableIndexEmitter.timeBound v + 4

theorem hoareTime (fuel scratch : Fin w) (hne : fuel ≠ scratch) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel → j ≠ scratch → work' j = work j) → R work → R work') :
    (machine fuel scratch).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg idx.val (work fuel) ∧ Register 0 (work scratch) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (Term.var idx).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg idx.val (work fuel) ∧ Register 0 (work scratch) ∧ R work)
      (timeBound idx.val) := by
  let P : (Fin w → Tape) → Prop := fun work => IsReg idx.val (work fuel) ∧ Register 0 (work scratch) ∧ R work
  have ht := FixedOutput.hoareTime tag before input emitted P
  have hi := ReusableIndexEmitter.hoareTime fuel scratch hne idx.val before input (emitted ++ tag) R hR
  have his := SafeExecution.hoareTime (ReusableIndexEmitter.machine fuel scratch) _ _ _ hi (by
    rintro inp work out ⟨_, hc, _, _⟩ j
    exact (hc.works j).2)
  have hseq := seqTM_hoareTime (emitBitsTM tag) (ReusableIndexEmitter.machine fuel scratch) ht (by
    rintro inp work out ⟨hc, hs, hf, hb, hr⟩
    obtain ⟨hip, hwp, hop⟩ := hc.phase
    rw [hip, hwp, hop]
    exact ⟨⟨hf, hc, hb, hr⟩, hs⟩) his
  apply HoareTime.mono_bound (b := tag.length + 1 + ReusableIndexEmitter.timeBound idx.val)
  · apply HoareTime.strengthen_post hseq
    rintro inp work out ⟨⟨hf, hc, hb, hr⟩, hs⟩
    exact ⟨by simpa only [Term.code, tag, List.append_assoc] using hc, hs, hf, hb, hr⟩
  · simp only [timeBound, tag, List.length_cons, List.length_nil]
    omega

end JointThermoComplexity.Complexity.VariableOutput

#print axioms JointThermoComplexity.Complexity.VariableOutput.hoareTime
