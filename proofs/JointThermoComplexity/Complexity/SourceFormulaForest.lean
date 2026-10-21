module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaFinish

set_option autoImplicit false
@[expose] public section

/-! An actual formula-forest parser with exact independent syntax and restored fuel. -/

namespace JointThermoComplexity.Complexity.SourceFormulaForest
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
open SourceTermLoopState (State outcome)
open SourceFormulaLoopState
variable {n : ℕ}

def finalState (arity L count : ℕ) (s : State) : State := SourceFormulaFinish.finishState (run arity L count s)

def machine (d : Layout n) (fuel : Fin (n + 1)) : TM (n + 2) :=
  seqTM (SourceFormulaLoop.machine d fuel) (SourceFormulaFinish.machine d)

def timeBound (L pending count : ℕ) : ℕ := SourceFormulaLoop.timeBound L pending count + 3

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
  have hloop := SourceFormulaLoop.hoareTime d fuel hfu L arity count ha emitted R s hlen hR
  have hfinish := SourceFormulaFinish.hoareTime d L arity emitted RF (run arity L count s) hRF
  have hfull := seqTM_hoareTime (SourceFormulaLoop.machine d fuel) (SourceFormulaFinish.machine d) hloop (by
    rintro inp work out ⟨⟨hc, hr, hv, hf⟩, hFuel⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, ⟨⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits,
      hr.base.arityZero, hr.base.flagHead, hFuel, hr.base.frame⟩, hr.termFuel, hr.termPending, hr.tagHeads⟩, hv, hf⟩) hfinish
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hr, hv, hf⟩
    exact ⟨⟨hc, ⟨⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits,
      hr.base.arityZero, hr.base.flagHead, hr.base.frame.2⟩, hr.termFuel, hr.termPending, hr.tagHeads⟩, hv, hf⟩,
      hr.base.frame.1⟩) (by unfold timeBound; omega)

theorem cubic_timeBound (L : ℕ) : timeBound L 1 L = 34 * L ^ 3 + 95 * L ^ 2 + 67 * L + 5 := by
  rw [timeBound, SourceFormulaLoop.cubic_timeBound]

theorem status_criterion (arity L count pending : ℕ) (before input : List Bool) (hlen : input.length ≤ L) :
    (finalState arity L count ⟨before, input, pending, true⟩).valid = true ↔
      ∃ ps : List (RealSyntax.Formula arity), ps.length = pending ∧ SourceFormulaScan.forestNodes ps ≤ count ∧
        input = SourceFormulaScan.forestCode ps ++ (finalState arity L count ⟨before, input, pending, true⟩).input := by
  let sf := run arity L count ⟨before, input, pending, true⟩
  have he : (sf.valid && decide (sf.pending = 0)) = true ↔ outcome sf = some sf.input := by
    cases hb : sf.valid && decide (sf.pending = 0) <;> simp [outcome, hb]
  change (sf.valid && decide (sf.pending = 0)) = true ↔ _
  rw [he]
  exact SourceFormulaLoop.source_forest_criterion arity L count pending before input sf.input hlen

theorem formula_status_criterion (arity L : ℕ) (before input : List Bool) (hlen : input.length ≤ L) :
    (finalState arity L L ⟨before, input, 1, true⟩).valid = true ↔
      ∃ p : RealSyntax.Formula arity, input = p.code ++ (finalState arity L L ⟨before, input, 1, true⟩).input := by
  let sf := run arity L L ⟨before, input, 1, true⟩
  have he : (sf.valid && decide (sf.pending = 0)) = true ↔ outcome sf = some sf.input := by
    cases hb : sf.valid && decide (sf.pending = 0) <;> simp [outcome, hb]
  change (sf.valid && decide (sf.pending = 0)) = true ↔ _
  rw [he]
  exact SourceFormulaLoop.source_formula_criterion arity L before input sf.input hlen

theorem code_result (arity L count : ℕ) (ps : List (RealSyntax.Formula arity)) (before suffix : List Bool)
    (hn : SourceFormulaScan.forestNodes ps ≤ count) (hlen : (SourceFormulaScan.forestCode ps ++ suffix).length ≤ L) :
    (finalState arity L count ⟨before, SourceFormulaScan.forestCode ps ++ suffix, ps.length, true⟩).input = suffix ∧
    (finalState arity L count ⟨before, SourceFormulaScan.forestCode ps ++ suffix, ps.length, true⟩).valid = true := by
  let sf := run arity L count ⟨before, SourceFormulaScan.forestCode ps ++ suffix, ps.length, true⟩
  have ho : outcome sf = some suffix := by
    rw [outcome_run]
    exact SourceFormulaScan.scan_complete L count ps suffix hn hlen
  cases hb : sf.valid && decide (sf.pending = 0) with
  | false => simp [outcome, hb] at ho
  | true =>
    have hi : sf.input = suffix := by simpa only [outcome, hb, ↓reduceIte, Option.some.injEq] using ho
    exact ⟨hi, hb⟩

theorem formula_code_result (arity L : ℕ) (p : RealSyntax.Formula arity) (before suffix : List Bool)
    (hlen : (p.code ++ suffix).length ≤ L) :
    (finalState arity L L ⟨before, p.code ++ suffix, 1, true⟩).input = suffix ∧
    (finalState arity L L ⟨before, p.code ++ suffix, 1, true⟩).valid = true := by
  have hnodes := SourceFormulaScan.nodes_le_code_length p
  have hl : p.code.length ≤ L := by rw [List.length_append] at hlen; omega
  have h := code_result arity L L [p] before suffix (by
    simpa only [SourceFormulaScan.forestNodes_cons, SourceFormulaScan.forestNodes_nil, Nat.add_zero] using hnodes.trans hl)
    (by simpa only [SourceFormulaScan.forestCode_cons, SourceFormulaScan.forestCode_nil, List.append_nil] using hlen)
  simpa only [SourceFormulaScan.forestCode_cons, SourceFormulaScan.forestCode_nil, List.append_nil,
    List.length_cons, List.length_nil] using h

end JointThermoComplexity.Complexity.SourceFormulaForest

#print axioms JointThermoComplexity.Complexity.SourceFormulaForest.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaForest.cubic_timeBound
#print axioms JointThermoComplexity.Complexity.SourceFormulaForest.formula_status_criterion
#print axioms JointThermoComplexity.Complexity.SourceFormulaForest.formula_code_result
