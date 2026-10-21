module
public import proofs.JointThermoComplexity.Complexity.NetworkCircuitBody

set_option autoImplicit false
@[expose] public section

/-! A fresh total machine emits the exact circuit prefix on valid inputs and retains the complete false sentence on malformed inputs. -/

namespace JointThermoComplexity.Complexity.NetworkCircuitEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt NetworkEmitReady CircuitSerialization

def before (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some Q => NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q

def remaining (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => input
  | some Q => NetworkTallyData.tail Q

def word (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some Q => equationStream (NetworkCircuit.dense Q.network.reactions).circuit
      (NetworkMembership.activityIndex Q.network) (NetworkMembership.auxiliaryIndex Q.network)

def Advanced (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  match NetworkCodec.decode input with
  | none => (∀ j, Parked (work j)) ∧ NetworkPins.Kept m input work
  | some Q => Ready m input.length (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network) Q.speciesCount
      (NetworkPins.Kept m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m))

def branch (m : ℕ) : TM (m + 15) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 9)) (NetworkCircuitBody.machine m) (emitBitsTM [])

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (branch m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        FormulaStart.Registers (m + 7) input work)
      (fun inp work out => Cursor (before input) (remaining input) (emitted ++ word input) inp work out ∧ Advanced m input work)
      (NetworkCircuitBody.timeBound input.length + 2) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ FormulaStart.Registers (m + 7) input work
  cases hd : NetworkCodec.decode input with
  | none =>
    have ha : NetworkInputControl.accepted input = false := by
      cases he : NetworkInputControl.accepted input with
      | false => rfl
      | true =>
        obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp he
        rw [hd] at hQ
        cases hQ
    have hn := FixedOutput.hoareTime [] [] input emitted (FormulaStart.Registers (m + 7) input)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 9))
      (NetworkCircuitBody.machine m) (emitBitsTM []) [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hs, hg, ho, hbi, hk, hsp⟩
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.zero := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hr, hh, hdc, hds, hdg, hdo, hdb, hdk, _⟩ :=
      hb inp work out ⟨⟨hc, hs, hg, ho, hbi, hk, hsp⟩, hflag⟩
    exact ⟨d, t, by unfold NetworkCircuitBody.timeBound; omega, hr, hh,
      by simpa only [before, remaining, word, hd] using hdc,
      by simpa only [Advanced, hd] using And.intro hds (show NetworkPins.Kept m input d.work from ⟨hdg, hdo, hdb, hdk⟩)⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    have hy := NetworkCircuitBody.hoareTime m input Q hd emitted
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 9)) (NetworkCircuitBody.machine m) (emitBitsTM [])
      [] input emitted (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
      (emitted ++ word input) P (Advanced m input) (NetworkCircuitBody.timeBound input.length)
      (by simpa only [word, Advanced, hd] using hy)
    rintro inp work out ⟨hc, hs, hg, ho, hbi, hk, hsp⟩
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.one := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hr, hh, hdc, hpost⟩ := hb inp work out ⟨⟨hc, hs, hg, ho, hbi, hk, hsp⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh, by simpa only [before, remaining, hd] using hdc, hpost⟩

def machine (m : ℕ) : TM (m + 15) := seqTM (FormulaStart.machine (m + 7)) (branch m)

def timeBound (L : ℕ) : ℕ := FormulaStart.timeBound L + NetworkCircuitBody.timeBound L + 3

theorem timeBound_eq (L : ℕ) :
    timeBound L = 384 * L ^ 5 + 1104 * L ^ 4 + 1516 * L ^ 3 + 1272 * L ^ 2 + 606 * L + 134 := by
  rw [timeBound, FormulaStart.timeBound_eq]
  unfold NetworkCircuitBody.timeBound ReactionLoopEntry.timeBound
  ring1

def code (input : List Bool) : List Bool := FormulaStart.code input ++ word input

theorem code_prefix (input : List Bool) : ∃ rest, (NetworkCodec.toSentence input).code = code input ++ rest := by
  cases hd : NetworkCodec.decode input with
  | none =>
    refine ⟨[], ?_⟩
    simp only [NetworkCodec.toSentence, code, FormulaStart.code, word, hd, FalseOutput.sentence, List.append_nil]
  | some Q =>
    refine ⟨(RealSyntax.Formula.conj (NetworkMembership.equationsFormula Q.network)
      (NetworkFormula.constraintsFormula Q.network (NetworkMembership.activityIndex Q.network) (NetworkMembership.currentIndex Q.network))).code, ?_⟩
    simpa only [NetworkCodec.toSentence, code, FormulaStart.code, word, hd, FormulaPrefix.suffix, List.append_assoc] using FormulaPrefix.sentence_code Q

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor (before input) (remaining input) (code input) d.input d.work d.output ∧ Advanced m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hs, hregs⟩ := FormulaStart.run (m + 7) input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    branch_hoareTime m input (FormulaStart.code input) c.input c.work c.output ⟨hc, hs, hregs⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (branch m).reachesIn td
      ⟨(branch m).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (FormulaStart.machine (m + 7)) (branch m) hcreach hchalt hr
  have hstart : phase1Wrap (FormulaStart.machine (m + 7)) (branch m)
      ((FormulaStart.machine (m + 7)).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (FormulaStart.machine (m + 7)) (branch m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs⟩

end JointThermoComplexity.Complexity.NetworkCircuitEntry

#print axioms JointThermoComplexity.Complexity.NetworkCircuitEntry.code_prefix
#print axioms JointThermoComplexity.Complexity.NetworkCircuitEntry.timeBound_eq
#print axioms JointThermoComplexity.Complexity.NetworkCircuitEntry.run
