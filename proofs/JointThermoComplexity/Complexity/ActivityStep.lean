module
public import proofs.JointThermoComplexity.Complexity.ActivityState
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime
public import proofs.JointThermoComplexity.Complexity.UnarySuccessor

set_option autoImplicit false
@[expose] public section

/-! Emit a right-nested activity-positivity clause and advance its actual variable-address cursor. -/

namespace JointThermoComplexity.Complexity.ActivityStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ActivityState CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM
  (seqTM (emitBitsTM conjunctionTag) (FixedGateOutput.positiveMachine (scratch (m + 2)) (species (m + 1))))
  (UnarySuccessor.machine (species (m + 1)))

def word {arity : ℕ} (idx : Fin arity) : List Bool :=
  conjunctionTag ++ (RealSyntax.Formula.lt (.int 0) (.var idx)).code

def timeBound (L : ℕ) : ℕ := 32 * L ^ 2 + 56 * L + 40

theorem hoareTime {arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m idx.val R work)
      (fun inp work out => Cursor before input (emitted ++ word idx) inp work out ∧ Ready m (idx.val + 1) R work)
      (timeBound L) := by
  have ht := FixedOutput.hoareTime conjunctionTag before input emitted (fun work =>
    BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ IsReg idx.val (work (species (m + 1))) ∧ R work)
  have hp := FixedGateOutput.positive_hoareTime (scratch (m + 2)) (species (m + 1)) (species_ne_scratch (m + 1))
    idx before input (emitted ++ conjunctionTag) R
  have hprefix := seqTM_hoareTime (emitBitsTM conjunctionTag)
    (FixedGateOutput.positiveMachine (scratch (m + 2)) (species (m + 1))) ht (by
      intro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) hp
  let S : (Fin (m + 15) → Tape) → Prop := fun work => BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hz, hr⟩
    exact ⟨by simpa only [hw _ (species_ne_scratch (m + 1)).symm] using hz, hR work work' hw hr⟩
  have hs := UnarySuccessor.hoareTime (species (m + 1)) idx.val before input
    ((emitted ++ conjunctionTag) ++ (RealSyntax.Formula.lt (.int 0) (.var idx)).code) S hS
  have hfull := seqTM_hoareTime (seqTM (emitBitsTM conjunctionTag)
    (FixedGateOutput.positiveMachine (scratch (m + 2)) (species (m + 1)))) (UnarySuccessor.machine (species (m + 1)))
    hprefix (by
      rintro inp work out ⟨hc, hsafe, hz, hi, hr⟩
      obtain ⟨hip, hw, ho⟩ := hc.phase
      rw [hip, hw, ho]
      exact ⟨hc, hsafe, hi, hz, hr⟩) hs
  exact hfull.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hs, hi, hz, hr⟩
    exact ⟨by simpa only [word, List.append_assoc] using hc, hs, hz, hi, hr⟩) (by
      have hi := idx.isLt.le.trans ha
      have hv := TemplateRuntime.variable_bound hi
      unfold timeBound
      simp only [conjunctionTag, List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.ActivityStep

#print axioms JointThermoComplexity.Complexity.ActivityStep.hoareTime
