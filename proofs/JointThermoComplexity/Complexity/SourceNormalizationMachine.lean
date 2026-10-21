module
public import proofs.JointThermoComplexity.Complexity.SourceNormalizationBranch

set_option autoImplicit false
@[expose] public section

/-! An actual eleven-tape total source normalizer, including every malformed input. -/

namespace JointThermoComplexity.Complexity.SourceNormalizationMachine
open _root_.Complexity _root_.Complexity.TM HeaderAt

def continuation : TM 11 := seqTM rewindInputTM SourceNormalizationBranch.machine
def machine : TM 11 := seqTM SourceValidityRun.machine continuation
def timeBound (L : ℕ) : ℕ := 34 * L ^ 3 + 97 * L ^ 2 + 87 * L + 54

theorem continuation_hoareTime (input : List Bool) :
    continuation.HoareTime (SourceValidityRun.Post input) (SourceNormalizationBranch.Post input) (5 * input.length + 10) := by
  have hr := SourceValidityRewind.hoareTime input
  have hb := SourceNormalizationBranch.hoareTime input
  have h := seqTM_hoareTime (rewindInputTM (n := 11)) SourceNormalizationBranch.machine hr (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp⟩) hb
  exact h.mono_bound (by omega)

theorem hoareTime (input : List Bool) :
    machine.HoareTime (SourceScannerInit.Initial input) (SourceNormalizationBranch.Post input) (timeBound input.length) := by
  have hv := SourceValidityRun.hoareTime input
  have hc := continuation_hoareTime input
  have h := seqTM_hoareTime SourceValidityRun.machine continuation hv (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.1.phase
    rw [hi, hw, ho]
    exact hp) hc
  exact h.mono_bound (by unfold timeBound SourceValidityRun.timeBound; omega)

theorem run (input : List Bool) :
    ∃ c t, t ≤ timeBound input.length ∧ machine.reachesIn t (machine.initCfg input) c ∧ machine.halted c ∧
      c.output.HasBinaryPrefix (SourceNormalization.normalize input).code ∧ c.output.cells 0 = Γ.start := by
  obtain ⟨c, t, ht, hr, hh, hp⟩ := hoareTime input _ _ _ ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨c, t, ht, hr, hh, by simpa only [SourceNormalizationBranch.code_eq_normalize] using hp.1, hp.2⟩

theorem computesInTime : machine.ComputesInTime (fun input => (SourceNormalization.normalize input).code) timeBound := by
  intro input
  obtain ⟨c, t, ht, hr, hh, hp, _hz⟩ := run input
  exact ⟨c, t, ht, hr, hh, hp.2.1, hp.2.2 _ le_rfl⟩

end JointThermoComplexity.Complexity.SourceNormalizationMachine

#print axioms JointThermoComplexity.Complexity.SourceNormalizationMachine.run
#print axioms JointThermoComplexity.Complexity.SourceNormalizationMachine.computesInTime
