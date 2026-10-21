module
public import proofs.JointThermoComplexity.Complexity.LocalBranchPrepare
public import proofs.JointThermoComplexity.Complexity.LeafLocalEquation

set_option autoImplicit false
@[expose] public section

/-! Finite query plans produce exact local rows and restore the node cursor on every raw input. -/

namespace JointThermoComplexity.Complexity.NonleafEquationBranch
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryCounterInit LocalBranchState LocalBranchQuery

inductive Scan where
  | none | term (size : Size) | formula (size : Size)

structure Snapshot where
  before : List Bool
  input : List Bool
  counts : Counts
  values : Fin 9 → ℕ

def scanResult (scan : Scan) (L : ℕ) (s : Snapshot) : Snapshot := match scan with
  | .none => s
  | .term size =>
    let q := TermSpanControl.run L ⟨s.before, s.input, 1, 0⟩
    ⟨q.before, q.input, termCounts q, Function.update s.values size.index q.nodes⟩
  | .formula size =>
    let q := FormulaSpanControl.run L ⟨s.before, s.input, 0, 1, 0⟩
    ⟨q.before, q.input, formulaCounts q, Function.update s.values size.index q.coordinates⟩

def scanMachine : Scan → TM 32
  | .none => LeafLocalEquation.skip 0
  | .term size => termStore size
  | .formula size => formulaStore size

def scanTime (scan : Scan) (L B : ℕ) (counts : Counts) : ℕ := match scan with
  | .none => 0
  | .term _ => InitializedForwardQuery.termTime L counts + 2 * B + 5 * L + 16
  | .formula _ => InitializedForwardQuery.formulaTime L counts + 2 * B + 20 * L + 16

def scanBound (L B C : ℕ) : ℕ := 2 * C + 39 * L ^ 2 + 125 * L + 2 * B + 43

theorem scan_time_bound (scan : Scan) (L B C : ℕ) (counts : Counts) (hc : counts.total ≤ C) :
    scanTime scan L B counts ≤ scanBound L B C := by
  cases scan <;> simp only [scanTime, scanBound, InitializedForwardQuery.termTime, InitializedForwardQuery.formulaTime] <;> omega

theorem scan_bounds (scan : Scan) (L B : ℕ) (s : Snapshot) (hv : ∀ i, s.values i ≤ B) :
    let q := scanResult scan L s
    q.input.length ≤ s.input.length ∧ q.before ++ q.input = s.before ++ s.input ∧
      q.counts.total ≤ s.counts.total + 7 * L + 1 ∧ (∀ i, q.values i ≤ B + 4 * L) := by
  cases scan with
  | none =>
    change s.input.length ≤ s.input.length ∧ s.before ++ s.input = s.before ++ s.input ∧
      s.counts.total ≤ s.counts.total + 7 * L + 1 ∧ (∀ i, s.values i ≤ B + 4 * L)
    exact ⟨le_rfl, rfl, by omega, fun i => (hv i).trans (by omega)⟩
  | term size =>
    let q := TermSpanControl.run L ⟨s.before, s.input, 1, 0⟩
    obtain ⟨hp, hn, hi, hw⟩ := TermSpanControl.run_bounds L ⟨s.before, s.input, 1, 0⟩
    change q.pending ≤ 1 + L at hp
    change q.nodes ≤ 0 + L at hn
    refine ⟨hi, hw, ?_, ?_⟩
    · change q.pending + 0 + q.nodes ≤ _
      omega
    · intro i
      change Function.update s.values size.index q.nodes i ≤ _
      by_cases he : i = size.index
      · subst i
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne he]
        exact (hv i).trans (by omega)
  | formula size =>
    let q := FormulaSpanControl.run L ⟨s.before, s.input, 0, 1, 0⟩
    obtain ⟨ht, hf, hn, hi, hw⟩ := FormulaSpanControl.run_bounds L ⟨s.before, s.input, 0, 1, 0⟩
    change q.terms ≤ 0 + 2 * L at ht
    change q.formulas ≤ 1 + L at hf
    change q.coordinates ≤ 0 + 4 * L at hn
    refine ⟨hi, hw, ?_, ?_⟩
    · change q.terms + q.formulas + q.coordinates ≤ _
      omega
    · intro i
      change Function.update s.values size.index q.coordinates i ≤ _
      by_cases he : i = size.index
      · subst i
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne he]
        exact (hv i).trans (by omega)

theorem scan_zero (scan : Scan) (L : ℕ) (s : Snapshot) (hz : s.values 8 = 0) :
    (scanResult scan L s).values 8 = 0 := by
  cases scan with
  | none => exact hz
  | term size => simpa only [scanResult, Function.update_of_ne (by cases size <;> decide : (8 : Fin 9) ≠ size.index)] using hz
  | formula size => simpa only [scanResult, Function.update_of_ne (by cases size <;> decide : (8 : Fin 9) ≠ size.index)] using hz

theorem scan_hoareTime (scan : Scan) (L p B : ℕ) (s : Snapshot) (emitted : List Bool)
    (hz : s.values 8 = 0) (hv : ∀ i, s.values i ≤ B) (hlen : s.input.length ≤ L)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (scanMachine scan).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready s.counts s.values L R work)
      (fun inp work out =>
        let q := scanResult scan L s
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work anchor) ∧ Ready q.counts q.values L R work)
      (scanTime scan L B s.counts) := by
  cases scan with
  | none =>
    have h := LeafLocalEquation.skip_hoareTime 0 s.before s.input emitted
      (fun work _ => (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧ Ready s.counts s.values L R work)
    simpa only [scanMachine, scanResult, scanTime, List.take_zero, List.drop_zero, List.append_nil, Nat.mul_zero] using h
  | term size => exact term_store size L p B s.counts s.values hz (hv _) s.before s.input emitted R hR hlen
  | formula size => exact formula_store size L p B s.counts s.values hz (hv _) s.before s.input emitted R hR hlen

def queries (first second : Scan) : TM 32 := seqTM (scanMachine first) (scanMachine second)

def queryResult (first second : Scan) (L : ℕ) (s : Snapshot) : Snapshot := scanResult second L (scanResult first L s)

theorem queries_hoareTime (first second : Scan) (L p B C : ℕ) (s : Snapshot) (emitted : List Bool)
    (hz : s.values 8 = 0) (hv : ∀ i, s.values i ≤ B) (hc : s.counts.total ≤ C) (hlen : s.input.length ≤ L)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (queries first second).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready s.counts s.values L R work)
      (fun inp work out =>
        let q := queryResult first second L s
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work anchor) ∧ Ready q.counts q.values L R work)
      (scanBound L B C + 1 + scanBound L (B + 4 * L) (C + 7 * L + 1)) := by
  let mid := scanResult first L s
  obtain ⟨hi, _, hn, hb⟩ := scan_bounds first L B s hv
  have hfirst := (scan_hoareTime first L p B s emitted hz hv hlen R hR).mono_bound
    (scan_time_bound first L B C s.counts hc)
  have hsecond := (scan_hoareTime second L p (B + 4 * L) mid emitted (scan_zero first L s hz) hb
    (hi.trans hlen) R hR).mono_bound (scan_time_bound second L (B + 4 * L) (C + 7 * L + 1) mid.counts (by dsimp [mid]; omega))
  exact seqTM_hoareTime (scanMachine first) (scanMachine second) hfirst (by
    rintro inp work out ⟨hcur, hw, hp, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hw, hp, hr⟩) hsecond

def start (counts : Counts) (values : Fin 9 → ℕ) (before input : List Bool) : Snapshot :=
  ⟨before ++ input.take 3, input.drop 3, counts, values⟩

def result (first second : Scan) (L : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (before input : List Bool) : Snapshot :=
  queryResult first second L (start counts values before input)

def output (kind : LocalEquationTemplates.Kind) (first second : Scan) (L : ℕ) (counts : Counts)
    (values : Fin 9 → ℕ) (before input : List Bool) : List Bool :=
  RowEntriesCodec.entries (LocalEquationTemplates.wordRows kind
    (LocalAddressSetup.addressValues (result first second L counts values before input).values))

def forward (kind : LocalEquationTemplates.Kind) (first second : Scan) : TM 32 :=
  seqTM (LeafLocalEquation.skip 3) (seqTM (queries first second) (PreparedLocalEquation.machine kind))

def machine (kind : LocalEquationTemplates.Kind) (first second : Scan) : TM 32 :=
  InputCheckpoint.around anchor (forward kind first second)

def forwardTime (L B C : ℕ) : ℕ :=
  9 + scanBound L B C + scanBound L (B + 4 * L) (C + 7 * L + 1) + PreparedLocalEquation.timeBound (B + 8 * L)

theorem result_bounds (first second : Scan) (L B : ℕ) (counts : Counts) (values : Fin 9 → ℕ)
    (before input : List Bool) (hv : ∀ i, values i ≤ B) :
    let q := result first second L counts values before input
    q.input.length ≤ input.length ∧ q.before ++ q.input = before ++ input ∧
      (∀ i, q.values i ≤ B + 8 * L) := by
  let s := start counts values before input
  obtain ⟨hi, hw, _, hb⟩ := scan_bounds first L B s hv
  obtain ⟨hi', hw', _, hb'⟩ := scan_bounds second L (B + 4 * L) (scanResult first L s) hb
  refine ⟨hi'.trans (hi.trans (by dsimp [s, start]; simp only [List.length_drop]; omega)), ?_, ?_⟩
  · change (scanResult second L (scanResult first L s)).before ++ (scanResult second L (scanResult first L s)).input = _
    rw [hw', hw]
    simp only [s, start, List.append_assoc, List.take_append_drop]
  · intro i
    have h := hb' i
    change (result first second L counts values before input).values i ≤ _ at h
    omega

theorem forward_hoareTime (kind : LocalEquationTemplates.Kind) (first second : Scan) (L p B C : ℕ)
    (counts : Counts) (values : Fin 9 → ℕ) (before input emitted : List Bool)
    (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C) (hlen : input.length ≤ L)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (forward kind first second).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready counts values L R work)
      (fun inp work out =>
        let q := result first second L counts values before input
        Cursor q.before q.input (emitted ++ output kind first second L counts values before input) inp work out ∧
          (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧ Ready q.counts (LocalAddressSetup.prepared q.values) L R work)
      (forwardTime L B C) := by
  let s := start counts values before input
  let q := result first second L counts values before input
  have hskip := LeafLocalEquation.skip_hoareTime 3 before input emitted
    (fun work _ => (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧ Ready counts values L R work)
  have hquery := queries_hoareTime first second L p B C s emitted hz hv hc
    (by dsimp [s, start]; simp only [List.length_drop]; omega) R hR
  have hprepare := LocalBranchPrepare.hoareTime kind q.counts q.values L p (B + 8 * L)
    (result_bounds first second L B counts values before input hv).2.2 q.before q.input emitted R hR
  have hbody := seqTM_hoareTime (queries first second) (PreparedLocalEquation.machine kind) hquery (by
    rintro inp work out ⟨hcur, hw, hp, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hw, hp, hr⟩) hprepare
  have hseq := seqTM_hoareTime (LeafLocalEquation.skip 3)
    (seqTM (queries first second) (PreparedLocalEquation.machine kind)) hskip (by
      rintro inp work out ⟨hcur, hw, hp, hr⟩
      obtain ⟨hin, hwork, hout⟩ := hcur.phase
      rw [hin, hwork, hout]
      exact ⟨hcur, hw, hp, hr⟩) hbody
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by dsimp [forwardTime]; omega)

theorem hoareTime (kind : LocalEquationTemplates.Kind) (first second : Scan) (L B C : ℕ)
    (counts : Counts) (values : Fin 9 → ℕ) (before input emitted : List Bool)
    (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C) (hlen : input.length ≤ L)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (machine kind first second).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work anchor) ∧ Ready counts values L R work)
      (fun inp work out =>
        let q := result first second L counts values before input
        Cursor before input (emitted ++ output kind first second L counts values before input) inp work out ∧
          (∀ j, Parked (work j)) ∧ IsReg 0 (work anchor) ∧ Ready q.counts (LocalAddressSetup.prepared q.values) L R work)
      (13 * before.length + L + forwardTime L B C + 23) := by
  let q := result first second L counts values before input
  have hb := result_bounds first second L B counts values before input hv
  have h := InputCheckpointTransition.hoareTime anchor (forward kind first second) before input q.before q.input
    emitted (emitted ++ output kind first second L counts values before input) hb.2.1
    (Ready counts values L R) (Ready q.counts (LocalAddressSetup.prepared q.values) L R)
    (ready_anchor counts values L R hR) (ready_anchor q.counts (LocalAddressSetup.prepared q.values) L R hR)
    (forwardTime L B C) (forward_hoareTime kind first second L before.length B C counts values before input emitted hz hv hc hlen R hR)
  apply h.mono_bound
  have hw := congrArg List.length hb.2.1
  simp only [List.length_append] at hw
  dsimp only [q]
  omega

end JointThermoComplexity.Complexity.NonleafEquationBranch

#print axioms JointThermoComplexity.Complexity.NonleafEquationBranch.scan_bounds
#print axioms JointThermoComplexity.Complexity.NonleafEquationBranch.forward_hoareTime
#print axioms JointThermoComplexity.Complexity.NonleafEquationBranch.hoareTime
