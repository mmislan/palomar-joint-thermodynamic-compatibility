module
public import proofs.JointThermoComplexity.Complexity.EquationTotalBinder

set_option autoImplicit false
@[expose] public section

/-! Actual blank-tape initialization establishes the prefixed main-loop invariant with a computed binder. -/

namespace JointThermoComplexity.Complexity.EquationLoopInitialization
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork MainNodeEquation
open HeaderAt (Cursor)

def initialState (input : List Bool) : PreorderEmissionControl.State := ⟨EquationBootstrapState.state input, []⟩
def arity (input : List Bool) : ℕ := HeaderControl.count input
def variableCount (input : List Bool) : ℕ := EquationTotalBinder.total (arity input) input.length (HeaderControl.suffix input)
def stateBound (input : List Bool) : ℕ := EquationLoopBounds.bound (arity input) input.length (initialState input)
def Fuel (input : List Bool) (tapes : Work) : Prop := IsReg input.length (tapes EquationFuelFrame.fuel)

theorem fuel_stable (input : List Bool) : MainEquationWork.Stable (Fuel input) := by
  rintro tapes tapes' he hr
  simpa only [Fuel, he EquationFuelFrame.fuel (by unfold ExtraPort; decide)] using hr

theorem suffix_bound (input : List Bool) : (HeaderControl.suffix input).length ≤ input.length := by
  have h := congrArg List.length (HeaderControl.consumed_and_suffix input)
  simp only [List.length_append] at h
  omega

theorem count_bound (input : List Bool) : variableCount input ≤ 5 * input.length := by
  have hm := EquationTotalBinder.total_le (arity input) input.length (HeaderControl.suffix input)
  have ha := HeaderControl.count_le_length input
  change variableCount input ≤ arity input + 4 * input.length at hm
  dsimp [arity] at hm ⊢
  omega

theorem state_bound (input : List Bool) : stateBound input ≤ 7 * input.length + 1 := by
  have ha := HeaderControl.count_le_length input
  have hp := HeaderControl.copied_length_le input
  dsimp [stateBound, EquationLoopBounds.bound, initialState, EquationBootstrapState.state, arity]
  omega

theorem initial_size_bound (input : List Bool) : EquationLoopBounds.size (arity input) input.length (initialState input) ≤ 3 * input.length + 1 := by
  have ha := HeaderControl.count_le_length input
  have hp := HeaderControl.copied_length_le input
  dsimp [EquationLoopBounds.size, initialState, EquationBootstrapState.state, arity]
  omega

def machine : TM 32 := seqTM EquationBootstrapState.machine EquationTotalBinder.machine
def timeBound (L : ℕ) : ℕ := 39 * L ^ 2 + 300 * L + 200
noncomputable def timePolynomial : Polynomial ℕ := 39 * Polynomial.X ^ 2 + 300 * Polynomial.X + 200

theorem timePolynomial_eval (L : ℕ) : timePolynomial.eval L = timeBound L := by simp [timePolynomial, timeBound]

theorem hoareTime (input : List Bool) :
    machine.HoareTime (EquationLengthEntry.Initial input)
      (fun inp tapes out =>
        EquationLoopPolynomial.WithPrefix.Logical (RealSyntax.binderCode (variableCount input)) (initialState input)
          (arity input) input.length (stateBound input) inp tapes out ∧ IsReg input.length (tapes EquationFuelFrame.fuel))
      (timeBound input.length) := by
  let s := EquationBootstrapState.state input
  have hb := EquationBootstrapState.hoareTime input
  have ht := EquationTotalBinder.hoareTime s (arity input) input.length [] (Fuel input) (fuel_stable input) (suffix_bound input)
  have hseq := seqTM_hoareTime EquationBootstrapState.machine EquationTotalBinder.machine hb (by
    rintro inp tapes out ⟨hc, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hc.phase
    rw [hin, hwork, hout]
    have hfuel := (EquationBootstrapState.prepared input tapes hr (fun _ => True) trivial).2
    exact ⟨hc, (EquationBootstrapState.prepared input tapes hr (Fuel input) hfuel).1⟩) ht
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp tapes out ⟨hc, hs, hp, hr⟩
    let N := stateBound input
    have hm := EquationTotalBinder.total_le (arity input) input.length s.input
    have hq := InitializedSpanQuery.formula_counts_bound input.length s.input
    have hmN : EquationTotalBinder.total (arity input) input.length s.input ≤ N := by
      dsimp [N, stateBound, EquationLoopBounds.bound, initialState, s, EquationBootstrapState.state] at hm ⊢
      omega
    have hqN : (EquationTotalBinder.counts input.length s.input).total ≤ 14 * N + 2 := by
      change (EquationTotalBinder.counts input.length s.input).total ≤ 7 * input.length + 1 at hq
      dsimp [N, stateBound, EquationLoopBounds.bound, initialState, s, EquationBootstrapState.state] at hq ⊢
      omega
    have hbounded : Bounded s (arity input) input.length N (Fuel input) tapes :=
      ⟨EquationTotalBinder.total (arity input) input.length s.input, EquationTotalBinder.counts input.length s.input,
        EquationWorkReset.zeroValues, ⟨hs, hp, hr⟩, hmN, hqN, fun _ => Nat.zero_le _, rfl⟩
    have htrue := EquationFuelFrame.map_bounded s (arity input) input.length N (Fuel input) (fun _ => True) tapes (fun _ => trivial) hbounded
    refine ⟨⟨?_, htrue⟩, hr.basic.frame.extra⟩
    simpa only [initialState, variableCount, s, EquationBootstrapState.state, RowEntriesCodec.entries, List.append_nil, List.nil_append] using hc
  · have hm := count_bound input
    have hp := HeaderControl.copied_length_le input
    dsimp only [timeBound, EquationTotalBinder.timeBound, InitializedSpanQuery.formulaTime, RestoredSpanQuery.formulaTime,
      EquationWorkReset.zeroCounts, Counts.total]
    change 8 * input.length + 32 + 1 +
      (2 * (0 + 0 + 0) + (39 * input.length ^ 2 + 106 * input.length + 13 * (HeaderControl.copied input).length + 25) + 25 +
        9 * variableCount input + 21) ≤ _
    omega

def result (input : List Bool) : PreorderEmissionControl.State :=
  PreorderEmissionControl.run input.length (arity input) input.length (initialState input)

def runMachine : TM 32 := seqTM machine EquationEmissionLoop.machine

noncomputable def runTimePolynomial : Polynomial ℕ :=
  timePolynomial + EquationLoopPolynomial.timePolynomial.comp (3 * Polynomial.X + 1) + 1

theorem runTimePolynomial_eval (L : ℕ) : runTimePolynomial.eval L =
    timeBound L + EquationLoopPolynomial.timePolynomial.eval (3 * L + 1) + 1 := by
  simp [runTimePolynomial, timePolynomial_eval]

theorem run_hoareTime (input : List Bool) :
    runMachine.HoareTime (EquationLengthEntry.Initial input)
      (fun inp tapes out =>
        EquationLoopPolynomial.WithPrefix.Logical (RealSyntax.binderCode (variableCount input)) (result input)
          (arity input) input.length (stateBound input) inp tapes out ∧ IsReg input.length (tapes EquationFuelFrame.fuel))
      (runTimePolynomial.eval input.length) := by
  have hi := hoareTime input
  have hl := EquationLoopPolynomial.WithPrefix.hoareTime (RealSyntax.binderCode (variableCount input))
    (arity input) input.length (initialState input) (suffix_bound input)
  have hseq := seqTM_hoareTime machine EquationEmissionLoop.machine hi (by
    rintro inp tapes out ⟨hp, hf⟩
    obtain ⟨hin, hwork, hout⟩ := hp.1.phase
    rw [hin, hwork, hout]
    exact ⟨hp, hf⟩) hl
  apply hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
  · have hm := initial_size_bound input
    have hpoly : EquationLoopPolynomial.timePolynomial.eval (EquationLoopBounds.size (arity input) input.length (initialState input)) ≤
        EquationLoopPolynomial.timePolynomial.eval (3 * input.length + 1) := by
      rw [EquationLoopPolynomial.timePolynomial_eval, EquationLoopPolynomial.timePolynomial_eval]
      exact EquationLoopPolynomial.time_mono hm (by omega)
    rw [runTimePolynomial_eval]
    omega

end JointThermoComplexity.Complexity.EquationLoopInitialization

#print axioms JointThermoComplexity.Complexity.EquationLoopInitialization.hoareTime
#print axioms JointThermoComplexity.Complexity.EquationLoopInitialization.run_hoareTime
