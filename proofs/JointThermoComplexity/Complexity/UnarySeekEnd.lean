module
public import proofs.JointThermoComplexity.Complexity.UnaryTrim
public import proofs.JointThermoComplexity.Complexity.UnarySuccessorScan

set_option autoImplicit false
@[expose] public section

/-! Reach the end of a bounded unary register without changing its value or surrounding tapes. -/

namespace JointThermoComplexity.Complexity.UnarySeekEnd
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx : Fin w) : TM w := seqTM (UnarySuccessorMachine.machine idx) (UnaryTrimMachine.machine idx)

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate v true) ∧ (work idx).cells 0 = Γ.start ∧ R work) (v + 4) := by
  have hs := UnarySuccessorScan.hoareTime idx v before input emitted R hR
  have ht := UnaryTrim.hoareTime idx v before input emitted R hR
  have hseq := seqTM_hoareTime (UnarySuccessorMachine.machine idx) (UnaryTrimMachine.machine idx) hs (by
    rintro inp work out ⟨hc, hsafe, hp, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hsafe, hp, hz, hr⟩) ht
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by omega)

end JointThermoComplexity.Complexity.UnarySeekEnd

#print axioms JointThermoComplexity.Complexity.UnarySeekEnd.hoareTime
