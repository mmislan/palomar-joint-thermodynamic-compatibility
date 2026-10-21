module
public import proofs.JointThermoComplexity.Complexity.PhysicalSpanQuery
public import proofs.JointThermoComplexity.Complexity.QueryCounterInit

set_option autoImplicit false
@[expose] public section

/-! Initialized forward queries support consecutive term lookahead before an outer cursor restoration. -/

namespace JointThermoComplexity.Complexity.InitializedForwardQuery
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryWorkFrame QueryCounterInit

def termMachine : TM 32 := seqTM (QueryCounterInit.machine .term) RelocatedSpanQuery.termMachine
def formulaMachine : TM 32 := seqTM (QueryCounterInit.machine .formula) RelocatedSpanQuery.formulaMachine

def termTime (L : ℕ) (old : Counts) : ℕ := 2 * old.total + 5 * L ^ 2 + 47 * L + 27
def formulaTime (L : ℕ) (old : Counts) : ℕ := 2 * old.total + 39 * L ^ 2 + 105 * L + 27

theorem term_hoareTime (L p : ℕ) (old : Counts) (before input emitted : List Bool) (R : Work → Prop)
    (hR : Stable R) (hlen : input.length ≤ L) :
    termMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts old L R work)
      (fun inp work out =>
        let q := TermSpanControl.run L ⟨before, input, 1, 0⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work position) ∧ Ready q.pending 0 q.nodes L R work) (termTime L old) := by
  have hi := QueryCounterInit.hoareTime .term old L p before input emitted R hR
  have hq := PhysicalSpanQuery.term_hoareTime L L p 1 0 0 before input emitted R hR hlen
  have hseq := seqTM_hoareTime (QueryCounterInit.machine .term) RelocatedSpanQuery.termMachine hi (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) hq
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by rw [TermSpanLoop.quadratic_timeBound]; unfold termTime; omega)

theorem formula_hoareTime (L p : ℕ) (old : Counts) (before input emitted : List Bool) (R : Work → Prop)
    (hR : Stable R) (hlen : input.length ≤ L) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts old L R work)
      (fun inp work out =>
        let q := FormulaSpanControl.run L ⟨before, input, 0, 1, 0⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work position) ∧ Ready q.terms q.formulas q.coordinates L R work) (formulaTime L old) := by
  have hi := QueryCounterInit.hoareTime .formula old L p before input emitted R hR
  have hq := PhysicalSpanQuery.formula_hoareTime L L p 0 1 0 before input emitted R hR hlen
  have hseq := seqTM_hoareTime (QueryCounterInit.machine .formula) RelocatedSpanQuery.formulaMachine hi (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) hq
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by rw [FormulaSpanLoop.quadratic_timeBound]; unfold formulaTime; omega)

theorem term_code {n : ℕ} (L p : ℕ) (old : Counts) (t : RealSyntax.Term n)
    (before suffix emitted : List Bool) (R : Work → Prop) (hR : Stable R)
    (hlen : (t.code ++ suffix).length ≤ L) :
    termMachine.HoareTime
      (fun inp work out => Cursor before (t.code ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts old L R work)
      (fun inp work out => Cursor (before ++ t.code) suffix emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ Ready 0 0 t.size L R work) (termTime L old) := by
  have hn : t.size ≤ L := by have := t.size_le_code_length; rw [List.length_append] at hlen; omega
  have h := term_hoareTime L p old before (t.code ++ suffix) emitted R hR hlen
  rw [TermSpanCorrect.run_term L t hn] at h
  simpa only [Nat.zero_add] using h

theorem formula_code {n : ℕ} (L p : ℕ) (old : Counts) (f : RealSyntax.Formula n)
    (before suffix emitted : List Bool) (R : Work → Prop) (hR : Stable R)
    (hlen : (f.code ++ suffix).length ≤ L) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before (f.code ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts old L R work)
      (fun inp work out => Cursor (before ++ f.code) suffix emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ Ready 0 0 (SourceCoordinateEnumeration.formulaCount f) L R work) (formulaTime L old) := by
  have hn : SmallSyntaxForests.formulaTokens f ≤ L := by
    have := SmallSyntaxForests.formulaTokens_le_code_length f
    rw [List.length_append] at hlen
    omega
  have h := formula_hoareTime L p old before (f.code ++ suffix) emitted R hR hlen
  rw [FormulaSpanCorrect.run_formula L f hn] at h
  simpa only [Nat.zero_add] using h

end JointThermoComplexity.Complexity.InitializedForwardQuery

#print axioms JointThermoComplexity.Complexity.InitializedForwardQuery.term_hoareTime
#print axioms JointThermoComplexity.Complexity.InitializedForwardQuery.formula_code
