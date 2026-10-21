module
public import proofs.JointThermoComplexity.Complexity.BranchLeafEmission
public import proofs.JointThermoComplexity.Complexity.RestoredEquationTag

set_option autoImplicit false
@[expose] public section

/-! Fresh present/tag dispatch emits the exact local preorder rows on every binary input. -/

namespace JointThermoComplexity.Complexity.EquationTagDispatch
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryWorkFrame QueryCounterInit LocalBranchState
open HeaderAt (Cursor)

def Before (counts : Counts) (values : Fin 9 → ℕ) (L : ℕ) (R : Work → Prop) (work : Work) : Prop :=
  (∀ j, Parked (work j)) ∧ IsReg 0 (work anchor) ∧ Ready counts values L R work

def After (root L B C : ℕ) (R : Work → Prop) (work : Work) : Prop :=
  (∀ j, Parked (work j)) ∧ IsReg 0 (work anchor) ∧
    ∃ counts values, Ready counts values L R work ∧ values 0 = root ∧ values 8 = 0 ∧
      (∀ i, values i ≤ 3 * (B + 8 * L) + 3) ∧ counts.total ≤ C + 14 * L + 2

def leafTime (L B p : ℕ) : ℕ := ReusableIndexEmitter.timeBound B + 2 * L + 13 * p + 70
def nodeTime (L B C p : ℕ) : ℕ := 13 * p + L + NonleafEquationBranch.forwardTime L B C + 23
def branchTime (L B C p : ℕ) : ℕ := leafTime L B p + nodeTime L B C p
def timeBound (L B C p : ℕ) : ℕ := branchTime L B C p + 13 * p + L + 40

def rows (termMode : Bool) (L root : ℕ) (input : List Bool) : PreorderLocalRows.Rows :=
  if termMode then PreorderLocalRows.termRows L root input else PreorderLocalRows.formulaRows L root input

def branches (termMode : Bool) (bits : List Bool) : TM 32 :=
  if termMode then match SourceTermToken.classify bits with
    | .integer => LeafLocalEquation.machine false
    | .variable => LeafLocalEquation.machine true
    | .add => FormulaEquationBranch.machine .add
    | .mul => FormulaEquationBranch.machine .mul
    | .neg => FormulaEquationBranch.machine .neg
    | .invalid => LeafLocalEquation.skip 0
  else match SourceFormulaScan.classify bits with
    | .truth => FormulaEquationBranch.machine .truth
    | .falsity => FormulaEquationBranch.machine .falsity
    | .eq => FormulaEquationBranch.machine .eq
    | .lt => FormulaEquationBranch.machine .lt
    | .conj => FormulaEquationBranch.machine .conj
    | .disj => FormulaEquationBranch.machine .disj
    | .invalid => LeafLocalEquation.skip 0

def dispatchMachine (termMode : Bool) : TM 32 := SourceTagDispatch.machine (List.ofFn tags) (branches termMode)
def presentMachine (termMode : Bool) : TM 32 := FlagBranch.machine flag (dispatchMachine termMode) (LeafLocalEquation.skip 0)
def machine (termMode : Bool) : TM 32 := seqTM RestoredEquationTag.machine (presentMachine termMode)

theorem after_same (counts : Counts) (values : Fin 9 → ℕ) (L B C : ℕ) (R : Work → Prop) (work : Work)
    (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C) (h : Before counts values L R work) :
    After (values 0) L B C R work := by
  refine ⟨h.1, h.2.1, counts, values, h.2.2, rfl, hz, ?_, ?_⟩
  · intro i
    have hi := hv i
    omega
  · omega

theorem after_node (kind : FormulaEquationBranch.Kind) (counts : Counts) (values : Fin 9 → ℕ)
    (L B C : ℕ) (before input : List Bool) (R : Work → Prop) (work : Work)
    (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hs : ∀ j, Parked (work j)) (hp : IsReg 0 (work anchor))
    (hr : let q := NonleafEquationBranch.result (FormulaEquationBranch.first kind) (FormulaEquationBranch.second kind) L counts values before input
      Ready q.counts (LocalAddressSetup.prepared q.values) L R work) : After (values 0) L B C R work := by
  let first := FormulaEquationBranch.first kind
  let second := FormulaEquationBranch.second kind
  let s := NonleafEquationBranch.start counts values before input
  let mid := NonleafEquationBranch.scanResult first L s
  let q := NonleafEquationBranch.result first second L counts values before input
  obtain ⟨_, _, hn, hb⟩ := NonleafEquationBranch.scan_bounds first L B s hv
  obtain ⟨_, _, hn', _⟩ := NonleafEquationBranch.scan_bounds second L (B + 4 * L) mid hb
  have hq := (NonleafEquationBranch.result_bounds first second L B counts values before input hv).2.2
  have hz' := NonleafEquationBranch.scan_zero second L mid (NonleafEquationBranch.scan_zero first L s hz)
  refine ⟨hs, hp, q.counts, LocalAddressSetup.prepared q.values, hr, ?_, ?_,
    LocalAddressSetup.prepared_bound q.values (B + 8 * L) hq, ?_⟩
  · change q.values 0 = values 0
    exact FormulaEquationBranch.result_root kind L counts values before input
  · change q.values 8 = 0
    exact hz'
  · change mid.counts.total ≤ counts.total + 7 * L + 1 at hn
    change q.counts.total ≤ mid.counts.total + 7 * L + 1 at hn'
    omega

theorem noop_hoareTime (counts : Counts) (values : Fin 9 → ℕ) (L B C : ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (R : Work → Prop) :
    (LeafLocalEquation.skip 0).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Before counts values L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ After (values 0) L B C R work) 0 := by
  have h := LeafLocalEquation.skip_hoareTime 0 before input emitted (fun work _ => Before counts values L R work)
  apply h.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hcur, hp⟩
    exact ⟨by simpa only [List.take_zero, List.drop_zero, List.append_nil] using hcur,
      after_same counts values L B C R work hz hv hc hp⟩
  · omega

def leafRows (isVar : Bool) (root : ℕ) (input : List Bool) : PreorderLocalRows.Rows :=
  [SparseInteger.sub (PreorderLocalRows.variableWord root)
    (if isVar then SparseInteger.atom (PayloadControl.copied .empty (input.drop 3))
      else SparseInteger.constant (SmallIntegerLookup.value (input.drop 3)))]

theorem leaf_output (isVar : Bool) (root : ℕ) (input : List Bool) :
    LeafLocalEquation.output isVar root input = RowEntriesCodec.entries (leafRows isVar root input) := by
  cases isVar <;> simp [LeafLocalEquation.output, LeafRowEmitter.integer_output, LeafRowEmitter.variable_output,
    leafRows, RowEntriesCodec.entries, PreorderLocalRows.variableWord, SparseInteger.sub, SparseInteger.add,
    SparseInteger.atom, SparseInteger.constant, SparseInteger.neg, SparseInteger.scale]

theorem leaf_hoareTime (isVar : Bool) (counts : Counts) (values : Fin 9 → ℕ) (L B C : ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hlen : input.length ≤ L) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (LeafLocalEquation.machine isVar).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Before counts values L R work)
      (fun inp work out => Cursor before input (emitted ++ RowEntriesCodec.entries (leafRows isVar (values 0) input)) inp work out ∧
        After (values 0) L B C R work) (branchTime L B C before.length) := by
  have h := BranchLeafEmission.hoareTime isVar counts values L B (hv 0) before input emitted R hR
  apply h.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hcur, hs, hp, hr⟩
    rw [leaf_output] at hcur
    exact ⟨hcur, after_same counts values L B C R work hz hv hc ⟨hs, hp, hr⟩⟩
  · dsimp [branchTime, leafTime, nodeTime]
    omega

theorem node_hoareTime (kind : FormulaEquationBranch.Kind) (counts : Counts) (values : Fin 9 → ℕ) (L B C : ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hlen : input.length ≤ L) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (FormulaEquationBranch.machine kind).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Before counts values L R work)
      (fun inp work out => Cursor before input (emitted ++ RowEntriesCodec.entries (FormulaEquationBranch.rows kind L values input)) inp work out ∧
        After (values 0) L B C R work) (branchTime L B C before.length) := by
  have h := FormulaEquationBranch.hoareTime kind L B C counts values before input emitted hz hv hc hlen R hR
  apply h.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hcur, hs, hp, hr⟩
    exact ⟨hcur, after_node kind counts values L B C before input R work hz hv hc hs hp hr⟩
  · dsimp [branchTime, leafTime, nodeTime]
    omega

theorem selected_hoareTime (termMode : Bool) (counts : Counts) (values : Fin 9 → ℕ) (L B C : ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hlen : input.length ≤ L) (ha : SourceTags.accepted input = true) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (branches termMode (SourceTermToken.tagBits input)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Before counts values L R work)
      (fun inp work out => Cursor before input (emitted ++ RowEntriesCodec.entries (rows termMode L (values 0) input)) inp work out ∧
        After (values 0) L B C R work) (branchTime L B C before.length) := by
  have htcase (kind : FormulaEquationBranch.Kind) (hk : FormulaEquationBranch.isTerm kind = true)
      (hkind : SourceTermToken.classify (SourceTermToken.tagBits input) = FormulaEquationBranch.termKind kind) :=
    node_hoareTime kind counts values L B C before input emitted hz hv hc hlen R hR
      |>.consequence (fun _ _ _ hp => hp) (fun inp work out hp => by
        simpa only [FormulaEquationBranch.term_rows kind hk L values input ha hkind] using hp) le_rfl
  have hfcase (kind : FormulaEquationBranch.Kind) (hk : FormulaEquationBranch.isTerm kind = false)
      (hkind : SourceFormulaScan.classify (SourceTermToken.tagBits input) = FormulaEquationBranch.formulaKind kind) :=
    node_hoareTime kind counts values L B C before input emitted hz hv hc hlen R hR
      |>.consequence (fun _ _ _ hp => hp) (fun inp work out hp => by
        simpa only [FormulaEquationBranch.formula_rows kind hk L values input ha hkind] using hp) le_rfl
  cases termMode with
  | true =>
    cases hkind : SourceTermToken.classify (SourceTermToken.tagBits input) with
    | integer =>
      simpa only [branches, rows, ↓reduceIte, Bool.false_eq_true, hkind, PreorderLocalRows.termRows, ha, leafRows] using
        leaf_hoareTime false counts values L B C before input emitted hz hv hc hlen R hR
    | «variable» =>
      simpa only [branches, rows, ↓reduceIte, hkind, PreorderLocalRows.termRows, ha, leafRows] using
        leaf_hoareTime true counts values L B C before input emitted hz hv hc hlen R hR
    | add => simpa only [branches, rows, ↓reduceIte, hkind] using htcase .add rfl hkind
    | mul => simpa only [branches, rows, ↓reduceIte, hkind] using htcase .mul rfl hkind
    | neg => simpa only [branches, rows, ↓reduceIte, hkind] using htcase .neg rfl hkind
    | invalid =>
      have h := (noop_hoareTime counts values L B C before input emitted hz hv hc R).mono_bound
        (Nat.zero_le (branchTime L B C before.length))
      simpa [branches, rows, PreorderLocalRows.termRows, ha, hkind, RowEntriesCodec.entries] using h
  | false =>
    cases hkind : SourceFormulaScan.classify (SourceTermToken.tagBits input) with
    | truth => simpa only [branches, rows, Bool.false_eq_true, ↓reduceIte, hkind] using hfcase .truth rfl hkind
    | falsity => simpa only [branches, rows, Bool.false_eq_true, ↓reduceIte, hkind] using hfcase .falsity rfl hkind
    | eq => simpa only [branches, rows, Bool.false_eq_true, ↓reduceIte, hkind] using hfcase .eq rfl hkind
    | lt => simpa only [branches, rows, Bool.false_eq_true, ↓reduceIte, hkind] using hfcase .lt rfl hkind
    | conj => simpa only [branches, rows, Bool.false_eq_true, ↓reduceIte, hkind] using hfcase .conj rfl hkind
    | disj => simpa only [branches, rows, Bool.false_eq_true, ↓reduceIte, hkind] using hfcase .disj rfl hkind
    | invalid =>
      have h := (noop_hoareTime counts values L B C before input emitted hz hv hc R).mono_bound
        (Nat.zero_le (branchTime L B C before.length))
      simpa [branches, rows, PreorderLocalRows.formulaRows, ha, hkind, RowEntriesCodec.entries] using h

theorem present_hoareTime (termMode : Bool) (counts : Counts) (values : Fin 9 → ℕ) (L B C : ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hlen : input.length ≤ L) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (presentMachine termMode).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Before counts values L R work ∧ RestoredEquationTag.Reading input work)
      (fun inp work out => Cursor before input (emitted ++ RowEntriesCodec.entries (rows termMode L (values 0) input)) inp work out ∧
        After (values 0) L B C R work) (branchTime L B C before.length + 8) := by
  cases ha : SourceTags.accepted input with
  | true =>
    have hsel := selected_hoareTime termMode counts values L B C before input emitted hz hv hc hlen ha R hR
    have hdisp := SourceTagDispatch.hoareTime (List.ofFn tags) (SourceTermToken.tagBits input)
      (by simp [SourceTermToken.tagBits]) (branches termMode) before input emitted before input
      (emitted ++ RowEntriesCodec.entries (rows termMode L (values 0) input))
      (Before counts values L R) (After (values 0) L B C R) (branchTime L B C before.length) hsel
    have hb := FlagBranchRun.yes_hoareTime flag (dispatchMachine termMode) (LeafLocalEquation.skip 0)
      before input emitted before input (emitted ++ RowEntriesCodec.entries (rows termMode L (values 0) input))
      (fun work => Before counts values L R work ∧ SourceTagDispatch.Reads (List.ofFn tags) (SourceTermToken.tagBits input) work)
      (After (values 0) L B C R) (branchTime L B C before.length + 6) (by simpa [dispatchMachine] using hdisp)
    apply hb.consequence
    · rintro inp work out ⟨hcur, hp, hr⟩
      exact ⟨⟨hcur, hp, RestoredEquationTag.reads input work hr⟩, by simpa only [ha, Γ.ofBool] using hr.1⟩
    · exact fun _ _ _ hp => hp
    · omega
  | false =>
    have hn := noop_hoareTime counts values L B C before input emitted hz hv hc R
    have hb := FlagBranchRun.no_hoareTime flag (dispatchMachine termMode) (LeafLocalEquation.skip 0)
      before input emitted before input emitted (Before counts values L R) (After (values 0) L B C R) 0 hn
    apply hb.consequence
    · rintro inp work out ⟨hcur, hp, hr⟩
      exact ⟨⟨hcur, hp⟩, by simpa only [ha, Γ.ofBool] using hr.1⟩
    · intro inp work out hp
      simpa [rows, PreorderLocalRows.termRows, PreorderLocalRows.formulaRows, ha, RowEntriesCodec.entries] using hp
    · omega

theorem hoareTime (termMode : Bool) (counts : Counts) (values : Fin 9 → ℕ) (L B C : ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hlen : input.length ≤ L) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (machine termMode).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Before counts values L R work)
      (fun inp work out => Cursor before input (emitted ++ RowEntriesCodec.entries (rows termMode L (values 0) input)) inp work out ∧
        After (values 0) L B C R work) (timeBound L B C before.length) := by
  have ht := RestoredEquationTag.hoareTime counts values L before input emitted R hR
  have hp := present_hoareTime termMode counts values L B C before input emitted hz hv hc hlen R hR
  have hseq := seqTM_hoareTime RestoredEquationTag.machine (presentMachine termMode) ht (by
    rintro inp work out ⟨hcur, hs, ha, hr, ht⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, ⟨hs, ha, hr⟩, ht⟩) hp
  apply hseq.mono_bound
  dsimp [timeBound]
  omega

end JointThermoComplexity.Complexity.EquationTagDispatch

#print axioms JointThermoComplexity.Complexity.EquationTagDispatch.after_node
#print axioms JointThermoComplexity.Complexity.EquationTagDispatch.leaf_output
#print axioms JointThermoComplexity.Complexity.EquationTagDispatch.hoareTime
