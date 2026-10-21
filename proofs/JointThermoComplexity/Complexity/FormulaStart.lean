module
public import proofs.JointThermoComplexity.Complexity.FormulaPrefix
public import proofs.JointThermoComplexity.Complexity.FalseOutput
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! Fresh total formula entry: exact validated sentence prefix, or the complete false sentence. -/

namespace JointThermoComplexity.Complexity.FormulaStart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountLayout

def code (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => FalseOutput.sentence.code
  | some Q => FormulaPrefix.word (NetworkMembership.arity Q.network) (NetworkMembership.gates Q.network)

theorem code_prefix (input : List Bool) : ∃ rest, (NetworkCodec.toSentence input).code = code input ++ rest := by
  cases hd : NetworkCodec.decode input with
  | none =>
    refine ⟨[], ?_⟩
    simp only [code, NetworkCodec.toSentence, hd, FalseOutput.sentence, List.append_nil]
  | some Q =>
    exact ⟨FormulaPrefix.suffix Q, by simpa only [code, NetworkCodec.toSentence, hd] using FormulaPrefix.sentence_code Q⟩

def Registers (m : ℕ) (input : List Bool) (work : Fin (m + 8) → Tape) : Prop :=
  IsReg (GateCountValue.count input) (work (raw m)) ∧ IsReg (ArityValue.offset input) (work (offset m)) ∧
  IsReg (ArityValue.arity input) (work (binder m)) ∧ ParserRegisters.Kept (m + 2) input (CountAppend.oldWork work) ∧ FreshArity.Spare m work

def branch (m : ℕ) : TM (m + 8) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 2)) (FormulaPrefix.machine m) FalseOutput.machine

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (branch m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Registers m input work)
      (fun inp work out => Cursor [] input (emitted ++ code input) inp work out ∧ (∀ j, Parked (work j)) ∧ Registers m input work)
      (34 * input.length + 16) := by
  let P : (Fin (m + 8) → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Registers m input work
  cases ha : NetworkInputControl.accepted input with
  | false =>
    have hf := FalseOutput.hoareTime [] input emitted (Registers m input)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 2)) (FormulaPrefix.machine m) FalseOutput.machine
      [] input emitted [] input (emitted ++ FalseOutput.sentence.code) P P 4 hf
    rintro inp work out ⟨hc, hs, hg, ho, hbi, hk, hsp⟩
    have hflag : (work (RoutedNetworkParser.master (m + 2))).read = Γ.zero := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdP⟩ := hb inp work out ⟨⟨hc, hs, hg, ho, hbi, hk, hsp⟩, hflag⟩
    exact ⟨d, t, by omega, hreach, hhalt,
      by simpa only [code, GateCountValue.rejected_decode ha] using hdcur, hdP⟩
  | true =>
    obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp ha
    have hv := FormulaPrefix.hoareTime m input [] input emitted (Registers m input)
    have hv' : (FormulaPrefix.machine m).HoareTime
        (fun inp work out => Cursor [] input emitted inp work out ∧ P work)
        (fun inp work out => Cursor [] input (emitted ++ code input) inp work out ∧ P work) (34 * input.length + 15) := by
      exact hv.consequence
        (fun _ _ _ ⟨hc, hs, hp⟩ => ⟨hp.2.2.1, hp.1, hc, hs, hp⟩)
        (fun _ _ _ ⟨_, _, hc, hs, hp⟩ => ⟨by
          simpa only [code, hQ, ArityValue.on_decode hQ, GateCountValue.on_decode hQ] using hc, hs, hp⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 2)) (FormulaPrefix.machine m) FalseOutput.machine
      [] input emitted [] input (emitted ++ code input) P P (34 * input.length + 15) hv'
    rintro inp work out ⟨hc, hs, hg, ho, hbi, hk, hsp⟩
    have hflag : (work (RoutedNetworkParser.master (m + 2))).read = Γ.one := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdP⟩ := hb inp work out ⟨⟨hc, hs, hg, ho, hbi, hk, hsp⟩, hflag⟩
    exact ⟨d, t, by omega, hreach, hhalt, hdcur, hdP⟩

def machine (m : ℕ) : TM (m + 8) := seqTM (FreshArity.machine m) (branch m)

def timeBound (L : ℕ) : ℕ := FreshArity.timeBound L + 34 * L + 17

theorem timeBound_eq (L : ℕ) : timeBound L = 4 * L ^ 3 + 44 * L ^ 2 + 150 * L + 107 := by
  rw [timeBound, FreshArity.timeBound_eq]
  ring1

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor [] input (code input) d.input d.work d.output ∧
      (∀ j, Parked (d.work j)) ∧ Registers m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hs, hg, ho, hbi, hk, hsp⟩ := FreshArity.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdsafe, hdregs⟩ :=
    branch_hoareTime m input [] c.input c.work c.output ⟨hc, hs, hg, ho, hbi, hk, hsp⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (branch m).reachesIn td
      ⟨(branch m).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (FreshArity.machine m) (branch m) hcreach hchalt hr
  have hstart : phase1Wrap (FreshArity.machine m) (branch m)
      ((FreshArity.machine m).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (FreshArity.machine m) (branch m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt,
    by simpa only [phase2Wrap, List.nil_append] using hdcur, hdsafe, hdregs⟩

end JointThermoComplexity.Complexity.FormulaStart

#print axioms JointThermoComplexity.Complexity.FormulaStart.code_prefix
#print axioms JointThermoComplexity.Complexity.FormulaStart.run
