module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaForest
public import proofs.JointThermoComplexity.Complexity.EndScanner

set_option autoImplicit false
@[expose] public section

/-! The actual formula parser rejects every trailing bit and keeps every earlier rejection. -/

namespace JointThermoComplexity.Complexity.SourceFormulaEOF
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
open SourceTermLoopState (State)
variable {n : ℕ}

def endState (s : State) : State := {s with valid := s.valid && s.input.isEmpty}
def finalState (arity L count : ℕ) (s : State) : State := endState (SourceFormulaForest.finalState arity L count s)

theorem end_hoareTime (d : Layout n) (L arity : ℕ) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hR : Stable d R) :
    (EndScanner.machine (NaturalScanBuffer.flag n)).HoareTime
      (Inv d L arity emitted R s) (Inv d L arity emitted R (endState s)) 1 := by
  rintro inp work out ⟨hc, hr, hp, hf⟩
  let C : (Fin (n + 2) → Tape) → Prop := fun work' => ∀ j, j ≠ NaturalScanBuffer.flag n → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ NaturalScanBuffer.flag n → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨c, t, ht, hd, hh, hc', hfh', hv', hother⟩ :=
    EndScanner.hoareTime (NaturalScanBuffer.flag n) s.valid s.before s.input emitted C hC
      inp work out ⟨hc, hr.base.flagHead, hf, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.base.markers j, (hr.base.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hs' : ∀ j, Parked (c.work j) := by
    intro j
    refine ⟨?_, (hm.2.1 j).2⟩
    by_cases hj : j = NaturalScanBuffer.flag n
    · subst j
      rw [hfh']
    · rw [hother j hj]
      exact (hr.base.safe j).1
  have hr' := SourceFormulaRegisters.reframe d L arity R hR work c.work hr (fun j _ hj => hother j hj)
    hs' (fun j => (hm.2.1 j).1) hfh'
  have hpend := hother d.formulaPending.castSucc (SourcePendingFrame.cast_ne d.formulaSep.flag)
  exact ⟨c, t, ht, hd, hh, hc', hr', by simpa only [endState, hpend] using hp, hv'⟩

def machine (d : Layout n) (fuel : Fin (n + 1)) : TM (n + 2) :=
  seqTM (SourceFormulaForest.machine d fuel) (EndScanner.machine (NaturalScanBuffer.flag n))

def timeBound (L pending count : ℕ) : ℕ := SourceFormulaForest.timeBound L pending count + 2

theorem hoareTime (d : Layout n) (fuel : Fin (n + 1)) (hfu : Outside d fuel)
    (L arity count : ℕ) (ha : arity.bits.length ≤ L) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, Outside d j → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine d fuel).HoareTime
      (fun inp work out => Inv d L arity emitted R s inp work out ∧ IsReg count (work fuel.castSucc))
      (fun inp work out => Inv d L arity emitted R (finalState arity L count s) inp work out ∧
        IsReg count (work fuel.castSucc)) (timeBound L s.pending count) := by
  let RF : (Fin (n + 1) → Tape) → Prop := fun work => IsReg count (work fuel) ∧ R work
  have hRF : Stable d RF := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw fuel hfu] using hf, hR _ _ (fun j hj _ => hw j hj) hr⟩
  have hforest := SourceFormulaForest.hoareTime d fuel hfu L arity count ha emitted R s hlen hR
  have hend := end_hoareTime d L arity emitted RF (SourceFormulaForest.finalState arity L count s) hRF
  have hfull := seqTM_hoareTime (SourceFormulaForest.machine d fuel) (EndScanner.machine (NaturalScanBuffer.flag n)) hforest (by
    rintro inp work out ⟨⟨hc, hr, hv, hf⟩, hFuel⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, ⟨⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits,
      hr.base.arityZero, hr.base.flagHead, hFuel, hr.base.frame⟩, hr.termFuel, hr.termPending, hr.tagHeads⟩, hv, hf⟩) hend
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hr, hv, hf⟩
    exact ⟨⟨hc, ⟨⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits,
      hr.base.arityZero, hr.base.flagHead, hr.base.frame.2⟩, hr.termFuel, hr.termPending, hr.tagHeads⟩, hv, hf⟩,
      hr.base.frame.1⟩) (by unfold timeBound; omega)

theorem cubic_timeBound (L : ℕ) : timeBound L 1 L = 34 * L ^ 3 + 95 * L ^ 2 + 67 * L + 7 := by
  rw [timeBound, SourceFormulaForest.cubic_timeBound]

theorem status_criterion (arity L : ℕ) (before input : List Bool) (hlen : input.length ≤ L) :
    (finalState arity L L ⟨before, input, 1, true⟩).valid = true ↔ ∃ p : RealSyntax.Formula arity, input = p.code := by
  let sf := SourceFormulaForest.finalState arity L L ⟨before, input, 1, true⟩
  change (sf.valid && sf.input.isEmpty) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hv, he⟩
    have hnil : sf.input = [] := List.isEmpty_iff.mp he
    obtain ⟨p, hp⟩ := (SourceFormulaForest.formula_status_criterion arity L before input hlen).mp hv
    change input = p.code ++ sf.input at hp
    exact ⟨p, by simpa only [hnil, List.append_nil] using hp⟩
  · rintro ⟨p, rfl⟩
    have hc := SourceFormulaForest.formula_code_result arity L p before [] (by simpa only [List.append_nil] using hlen)
    have hc' : sf.input = [] ∧ sf.valid = true := by simpa only [List.append_nil] using hc
    exact ⟨hc'.2, by rw [hc'.1]; rfl⟩

theorem initial_false (arity L count pending : ℕ) (before input : List Bool) :
    finalState arity L count ⟨before, input, pending, false⟩ = ⟨before, input, pending, false⟩ := by
  simp only [finalState, SourceFormulaForest.finalState, SourceFormulaLoopState.run_false,
    SourceFormulaFinish.finishState, endState, Bool.false_and]

end JointThermoComplexity.Complexity.SourceFormulaEOF

#print axioms JointThermoComplexity.Complexity.SourceFormulaEOF.end_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaEOF.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaEOF.cubic_timeBound
#print axioms JointThermoComplexity.Complexity.SourceFormulaEOF.status_criterion
