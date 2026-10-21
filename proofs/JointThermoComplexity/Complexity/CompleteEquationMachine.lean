module
public import proofs.JointThermoComplexity.Complexity.EquationFinalFraming
public import proofs.JointThermoComplexity.Complexity.PreorderRowCode

set_option autoImplicit false
@[expose] public section

/-! The complete binary transducer emits a computed binder and the exact total equation row code. -/

namespace JointThermoComplexity.Complexity.CompleteEquationMachine
open _root_.Complexity _root_.Complexity.TM

def code (input : List Bool) : List Bool :=
  RealSyntax.binderCode (EquationLoopInitialization.variableCount input) ++ PreorderRowCode.code input

def machine : TM 32 := seqTM EquationLoopInitialization.runMachine EquationFinalFraming.machine

theorem result_eq (input : List Bool) : EquationLoopInitialization.result input = PreorderFormulaEmission.result input := rfl

theorem rows_eq (input : List Bool) : PreorderFormulaEmission.rows input =
    (EquationLoopInitialization.result input).emitted ++ EquationRootActivation.rows (EquationLoopInitialization.arity input) := by
  rw [result_eq]
  rfl

theorem code_eq (input : List Bool) : code input =
    RealSyntax.binderCode (EquationLoopInitialization.variableCount input) ++
      RowWordCodec.rows ((EquationLoopInitialization.result input).emitted ++ EquationRootActivation.rows (EquationLoopInitialization.arity input)) := by
  rw [code, PreorderRowCode.code, rows_eq]

noncomputable def runtimePolynomial : Polynomial ℕ :=
  EquationLoopInitialization.runTimePolynomial + EquationFinalFraming.timePolynomial.comp (7 * Polynomial.X + 1) + 1

noncomputable def timeBound (L : ℕ) : ℕ := runtimePolynomial.eval L

theorem polynomial_eval (L : ℕ) : runtimePolynomial.eval L =
    EquationLoopInitialization.runTimePolynomial.eval L + EquationFinalFraming.timeBound (7 * L + 1) + 1 := by
  simp [runtimePolynomial, EquationFinalFraming.timePolynomial_eval]

def Post (input : List Bool) : _root_.Complexity.TM.TapePred 32 := fun _ _ out =>
  out.HasBinaryPrefix (code input) ∧ out.cells 0 = Γ.start

theorem hoareTime (input : List Bool) :
    machine.HoareTime (EquationLengthEntry.Initial input) (Post input) (timeBound input.length) := by
  have hi := EquationLoopInitialization.run_hoareTime input
  have ha : EquationLoopInitialization.arity input ≤ EquationLoopInitialization.stateBound input := by
    dsimp [EquationLoopInitialization.stateBound, EquationLoopBounds.bound]
    omega
  have hf := EquationFinalFraming.hoareTime (EquationLoopInitialization.result input).scan
    (EquationLoopInitialization.arity input) input.length (EquationLoopInitialization.stateBound input) ha
    (RealSyntax.binderCode (EquationLoopInitialization.variableCount input) ++
      RowEntriesCodec.entries (EquationLoopInitialization.result input).emitted)
  have hseq := seqTM_hoareTime EquationLoopInitialization.runMachine EquationFinalFraming.machine hi (by
    rintro inp tapes out ⟨hp, _⟩
    obtain ⟨hin, hwork, hout⟩ := hp.1.phase
    rw [hin, hwork, hout]
    exact ⟨hp.1, hp.2⟩) hf
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp tapes out ⟨hc, _⟩
    have hout := hc.tapePrefix
    rw [EquationFinalFraming.combine, ← code_eq] at hout
    exact ⟨hout, hc.zero⟩
  · have hm := EquationFinalFraming.time_mono (EquationLoopInitialization.state_bound input)
    rw [timeBound, polynomial_eval]
    omega

theorem run (input : List Bool) :
    ∃ c t, t ≤ timeBound input.length ∧ machine.reachesIn t (machine.initCfg input) c ∧ machine.halted c ∧
      c.output.HasBinaryPrefix (code input) ∧ c.output.cells 0 = Γ.start := by
  obtain ⟨c, t, ht, hr, hh, hp⟩ := hoareTime input _ _ _ ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨c, t, ht, hr, hh, hp⟩

theorem computesInTime : machine.ComputesInTime code timeBound := by
  intro input
  obtain ⟨c, t, ht, hr, hh, hp, _⟩ := run input
  exact ⟨c, t, ht, hr, hh, hp.2.1, hp.2.2 _ le_rfl⟩

end JointThermoComplexity.Complexity.CompleteEquationMachine

#print axioms JointThermoComplexity.Complexity.CompleteEquationMachine.hoareTime
#print axioms JointThermoComplexity.Complexity.CompleteEquationMachine.computesInTime
