module
public import proofs.JointThermoComplexity.Complexity.LocalBranchState
public import proofs.JointThermoComplexity.Complexity.SelectedAddressArithmetic

set_option autoImplicit false
@[expose] public section

/-! Queries preserve the branch frame and store computed sizes without altering the main traversal. -/

namespace JointThermoComplexity.Complexity.LocalBranchQuery
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryWorkFrame QueryCounterInit LocalBranchState

def termCounts (q : TermSpanControl.State) : Counts := ⟨q.pending, 0, q.nodes⟩
def formulaCounts (q : FormulaSpanControl.State) : Counts := ⟨q.terms, q.formulas, q.coordinates⟩

theorem term_hoareTime (L p : ℕ) (old : Counts) (values : Fin 9 → ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) (hlen : input.length ≤ L) :
    InitializedForwardQuery.termMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ LocalBranchState.Ready old values L R work)
      (fun inp work out =>
        let q := TermSpanControl.run L ⟨before, input, 1, 0⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work anchor) ∧ LocalBranchState.Ready (termCounts q) values L R work)
      (InitializedForwardQuery.termTime L old) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hp', hr'⟩ :=
    InitializedForwardQuery.term_hoareTime L 0 old before input emitted (QueryExtra p values R)
      (query_extra_stable p values R hR) hlen inp work out
      ⟨hc, hs, hr.basic.positionReg, to_query old values L p R work hr hp⟩
  have he := from_query (termCounts (TermSpanControl.run L ⟨before, input, 1, 0⟩)) values L p R d.work hr' hp'
  exact ⟨d, t, ht, hd, hh, hc', hs', he.2, he.1⟩

theorem formula_hoareTime (L p : ℕ) (old : Counts) (values : Fin 9 → ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) (hlen : input.length ≤ L) :
    InitializedForwardQuery.formulaMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ LocalBranchState.Ready old values L R work)
      (fun inp work out =>
        let q := FormulaSpanControl.run L ⟨before, input, 0, 1, 0⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work anchor) ∧ LocalBranchState.Ready (formulaCounts q) values L R work)
      (InitializedForwardQuery.formulaTime L old) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hp', hr'⟩ :=
    InitializedForwardQuery.formula_hoareTime L 0 old before input emitted (QueryExtra p values R)
      (query_extra_stable p values R hR) hlen inp work out
      ⟨hc, hs, hr.basic.positionReg, to_query old values L p R work hr hp⟩
  have he := from_query (formulaCounts (FormulaSpanControl.run L ⟨before, input, 0, 1, 0⟩)) values L p R d.work hr' hp'
  exact ⟨d, t, ht, hd, hh, hc', hs', he.2, he.1⟩

inductive Size where
  | left | right
  deriving DecidableEq

def Size.index : Size → Fin 9
  | .left => 6
  | .right => 7

def Size.port (size : Size) : Fin 32 := AddressCounterPlacement.slot size.index

theorem size_basic (size : Size) : ∀ j, BasicPorts j → j ≠ size.port := by
  cases size <;> unfold BasicPorts <;> decide
theorem size_protected (size : Size) : ∀ j, Protected j → j ≠ size.port := by
  cases size <;> unfold Protected <;> decide
theorem size_anchor (size : Size) : anchor ≠ size.port := by cases size <;> decide

def store (size : Size) : TM 32 := SelectedAddressArithmetic.machine size.port result
  (AddressCounterPlacement.slot 8) (by cases size <;> decide) (by cases size <;> decide)

theorem store_hoareTime (size : Size) (counts : Counts) (values : Fin 9 → ℕ) (hz : values 8 = 0)
    (L p : ℕ) (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (store size).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ LocalBranchState.Ready counts values L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ LocalBranchState.Ready counts (Function.update values size.index counts.nodes) L R work)
      (2 * values size.index + 5 * counts.nodes + 15) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  let C : Work → Prop := fun work' => ∀ j, j ≠ size.port → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ size.port → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hh j hj
    exact (he j hj).trans (hh j hj)
  have hzero : IsReg 0 (work (AddressCounterPlacement.slot 8)) := by simpa only [hz] using hr.addresses 8
  obtain ⟨d, t, ht, hd, hh, hc', hs', hdst, _, _, ho⟩ :=
    SelectedAddressArithmetic.copy_hoareTime size.port result (AddressCounterPlacement.slot 8)
      (by cases size <;> decide) (by cases size <;> decide) (values size.index) counts.nodes
      before input emitted C hC inp work out ⟨hc, hs, hr.addresses size.index, hr.basic.nodeReg, hzero, fun _ _ => rfl⟩
  have hb := basic_transfer counts L R work d.work hr.basic (fun j hj => ho j (size_basic size j hj))
    (hR work d.work (fun j hj => ho j (size_protected size j hj)) hr.basic.frame)
  have hm : ∀ j, j ≠ anchor → (d.work j).cells 0 = Γ.start := by
    intro j hj
    by_cases he : j = size.port
    · subst j
      exact hdst.cell0
    · rw [ho j he]
      exact hr.markers j hj
  have ha : AddressCounterPlacement.Registers (Function.update values size.index counts.nodes) d.work := by
    intro i
    by_cases hi : i = size.index
    · subst i
      simpa only [Function.update_self, Size.port] using hdst
    · rw [Function.update_of_ne hi, ho _ (by
        intro he
        apply hi
        exact placeWorkIdx_injective 19 4 he)]
      exact hr.addresses i
  exact ⟨d, t, ht, hd, hh, hc', hs', by simpa only [ho anchor (size_anchor size)] using hp, hb, hm, ha⟩

def termStore (size : Size) : TM 32 := seqTM InitializedForwardQuery.termMachine (store size)
def formulaStore (size : Size) : TM 32 := seqTM InitializedForwardQuery.formulaMachine (store size)

theorem term_store (size : Size) (L p B : ℕ) (old : Counts) (values : Fin 9 → ℕ) (hz : values 8 = 0)
    (hv : values size.index ≤ B) (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R)
    (hlen : input.length ≤ L) :
    (termStore size).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ LocalBranchState.Ready old values L R work)
      (fun inp work out =>
        let q := TermSpanControl.run L ⟨before, input, 1, 0⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧
          LocalBranchState.Ready (termCounts q) (Function.update values size.index q.nodes) L R work)
      (InitializedForwardQuery.termTime L old + 2 * B + 5 * L + 16) := by
  let q := TermSpanControl.run L ⟨before, input, 1, 0⟩
  have hq := term_hoareTime L p old values before input emitted R hR hlen
  have hs := store_hoareTime size (termCounts q) values hz L p q.before q.input emitted R hR
  have hseq := seqTM_hoareTime InitializedForwardQuery.termMachine (store size) hq (by
    rintro inp work out ⟨hc, hw, hp, hr⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hp, hr⟩) hs
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    have hn := (TermSpanControl.run_bounds L ⟨before, input, 1, 0⟩).2.1
    change q.nodes ≤ 0 + L at hn
    change InitializedForwardQuery.termTime L old + 1 + (2 * values size.index + 5 * q.nodes + 15) ≤ _
    omega)

theorem formula_store (size : Size) (L p B : ℕ) (old : Counts) (values : Fin 9 → ℕ) (hz : values 8 = 0)
    (hv : values size.index ≤ B) (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R)
    (hlen : input.length ≤ L) :
    (formulaStore size).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ LocalBranchState.Ready old values L R work)
      (fun inp work out =>
        let q := FormulaSpanControl.run L ⟨before, input, 0, 1, 0⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧
          LocalBranchState.Ready (formulaCounts q) (Function.update values size.index q.coordinates) L R work)
      (InitializedForwardQuery.formulaTime L old + 2 * B + 20 * L + 16) := by
  let q := FormulaSpanControl.run L ⟨before, input, 0, 1, 0⟩
  have hq := formula_hoareTime L p old values before input emitted R hR hlen
  have hs := store_hoareTime size (formulaCounts q) values hz L p q.before q.input emitted R hR
  have hseq := seqTM_hoareTime InitializedForwardQuery.formulaMachine (store size) hq (by
    rintro inp work out ⟨hc, hw, hp, hr⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hp, hr⟩) hs
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    have hn := (FormulaSpanControl.run_bounds L ⟨before, input, 0, 1, 0⟩).2.2.1
    change q.coordinates ≤ 0 + 4 * L at hn
    change InitializedForwardQuery.formulaTime L old + 1 + (2 * values size.index + 5 * q.coordinates + 15) ≤ _
    omega)

end JointThermoComplexity.Complexity.LocalBranchQuery

#print axioms JointThermoComplexity.Complexity.LocalBranchQuery.store_hoareTime
#print axioms JointThermoComplexity.Complexity.LocalBranchQuery.term_store
#print axioms JointThermoComplexity.Complexity.LocalBranchQuery.formula_store
