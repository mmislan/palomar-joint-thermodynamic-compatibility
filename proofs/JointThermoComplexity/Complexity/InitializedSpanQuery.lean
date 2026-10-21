module
public import proofs.JointThermoComplexity.Complexity.RestoredSpanQuery
public import proofs.JointThermoComplexity.Complexity.QueryCounterInit

set_option autoImplicit false
@[expose] public section

/-! Repeated lookahead starts from arbitrary old query counts and returns exact raw sizes. -/

namespace JointThermoComplexity.Complexity.InitializedSpanQuery
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryWorkFrame QueryCounterInit

def termMachine : TM 32 := seqTM (QueryCounterInit.machine .term) RestoredSpanQuery.termMachine
def formulaMachine : TM 32 := seqTM (QueryCounterInit.machine .formula) RestoredSpanQuery.formulaMachine

def termTime (L p : ℕ) (old : Counts) : ℕ := 2 * old.total + RestoredSpanQuery.termTime L p + 25
def formulaTime (L p : ℕ) (old : Counts) : ℕ := 2 * old.total + RestoredSpanQuery.formulaTime L p + 25

theorem term_counts_bound (L : ℕ) (input : List Bool) :
    (⟨(PreorderLookahead.termResult L input).pending, 0, (PreorderLookahead.termResult L input).nodes⟩ : Counts).total ≤
      7 * L + 1 := by
  have hb := TermSpanControl.run_bounds L ⟨[], input, 1, 0⟩
  have hp : (PreorderLookahead.termResult L input).pending ≤ 1 + L := hb.1
  have hn : (PreorderLookahead.termResult L input).nodes ≤ L := by simpa only [PreorderLookahead.termResult, Nat.zero_add] using hb.2.1
  change (PreorderLookahead.termResult L input).pending + 0 + (PreorderLookahead.termResult L input).nodes ≤ _
  omega

theorem formula_counts_bound (L : ℕ) (input : List Bool) :
    (⟨(PreorderLookahead.formulaResult L input).terms, (PreorderLookahead.formulaResult L input).formulas,
      (PreorderLookahead.formulaResult L input).coordinates⟩ : Counts).total ≤ 7 * L + 1 := by
  have hb := FormulaSpanControl.run_bounds L ⟨[], input, 0, 1, 0⟩
  have ht : (PreorderLookahead.formulaResult L input).terms ≤ 2 * L := by simpa only [PreorderLookahead.formulaResult, Nat.zero_add] using hb.1
  have hf : (PreorderLookahead.formulaResult L input).formulas ≤ 1 + L := hb.2.1
  have hn : (PreorderLookahead.formulaResult L input).coordinates ≤ 4 * L := by simpa only [PreorderLookahead.formulaResult, Nat.zero_add] using hb.2.2.1
  change (PreorderLookahead.formulaResult L input).terms + (PreorderLookahead.formulaResult L input).formulas +
    (PreorderLookahead.formulaResult L input).coordinates ≤ _
  omega

theorem termTime_uniform (L p : ℕ) (old : Counts) (ho : old.total ≤ 7 * L + 1) (hp : p ≤ L) :
    termTime L p old ≤ 5 * L ^ 2 + 75 * L + 52 := by
  unfold termTime RestoredSpanQuery.termTime
  omega

theorem formulaTime_uniform (L p : ℕ) (old : Counts) (ho : old.total ≤ 7 * L + 1) (hp : p ≤ L) :
    formulaTime L p old ≤ 39 * L ^ 2 + 133 * L + 52 := by
  unfold formulaTime RestoredSpanQuery.formulaTime
  omega

theorem term_hoareTime (L : ℕ) (old : Counts) (before input emitted : List Bool) (R : Work → Prop)
    (hR : Stable R) (hlen : input.length ≤ L) :
    termMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ HasCounts old L R work)
      (fun inp work out =>
        let q := PreorderLookahead.termResult L input
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg 0 (work position) ∧ Ready q.pending 0 q.nodes L R work)
      (termTime L before.length old) := by
  have hi := QueryCounterInit.hoareTime .term old L 0 before input emitted R hR
  have hq := RestoredSpanQuery.term_hoareTime L before input emitted R hR hlen
  have hseq := seqTM_hoareTime (QueryCounterInit.machine .term) RestoredSpanQuery.termMachine hi (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) hq
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold termTime; omega)

theorem formula_hoareTime (L : ℕ) (old : Counts) (before input emitted : List Bool) (R : Work → Prop)
    (hR : Stable R) (hlen : input.length ≤ L) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ HasCounts old L R work)
      (fun inp work out =>
        let q := PreorderLookahead.formulaResult L input
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg 0 (work position) ∧ Ready q.terms q.formulas q.coordinates L R work)
      (formulaTime L before.length old) := by
  have hi := QueryCounterInit.hoareTime .formula old L 0 before input emitted R hR
  have hq := RestoredSpanQuery.formula_hoareTime L before input emitted R hR hlen
  have hseq := seqTM_hoareTime (QueryCounterInit.machine .formula) RestoredSpanQuery.formulaMachine hi (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) hq
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold formulaTime; omega)

theorem term_code {n : ℕ} (L : ℕ) (old : Counts) (t : RealSyntax.Term n)
    (before suffix emitted : List Bool) (R : Work → Prop) (hR : Stable R)
    (hlen : (t.code ++ suffix).length ≤ L) :
    termMachine.HoareTime
      (fun inp work out => Cursor before (t.code ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ HasCounts old L R work)
      (fun inp work out => Cursor before (t.code ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ Ready 0 0 t.size L R work) (termTime L before.length old) := by
  have hn : t.size ≤ L := by have := t.size_le_code_length; rw [List.length_append] at hlen; omega
  have h := TermSpanCorrect.run_term L t hn [] suffix 0
  have hq : PreorderLookahead.termResult L (t.code ++ suffix) = ⟨t.code, suffix, 0, t.size⟩ := by
    simpa only [PreorderLookahead.termResult, List.nil_append, Nat.zero_add] using h
  simpa only [hq] using term_hoareTime L old before (t.code ++ suffix) emitted R hR hlen

theorem formula_code {n : ℕ} (L : ℕ) (old : Counts) (f : RealSyntax.Formula n)
    (before suffix emitted : List Bool) (R : Work → Prop) (hR : Stable R)
    (hlen : (f.code ++ suffix).length ≤ L) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before (f.code ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ HasCounts old L R work)
      (fun inp work out => Cursor before (f.code ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ Ready 0 0 (SourceCoordinateEnumeration.formulaCount f) L R work)
      (formulaTime L before.length old) := by
  have hn : SmallSyntaxForests.formulaTokens f ≤ L := by
    have := SmallSyntaxForests.formulaTokens_le_code_length f
    rw [List.length_append] at hlen
    omega
  have h := FormulaSpanCorrect.run_formula L f hn [] suffix 0
  have hq : PreorderLookahead.formulaResult L (f.code ++ suffix) =
      ⟨f.code, suffix, 0, 0, SourceCoordinateEnumeration.formulaCount f⟩ := by
    simpa only [PreorderLookahead.formulaResult, List.nil_append, Nat.zero_add] using h
  simpa only [hq] using formula_hoareTime L old before (f.code ++ suffix) emitted R hR hlen

end JointThermoComplexity.Complexity.InitializedSpanQuery

#print axioms JointThermoComplexity.Complexity.InitializedSpanQuery.term_hoareTime
#print axioms JointThermoComplexity.Complexity.InitializedSpanQuery.formula_code
