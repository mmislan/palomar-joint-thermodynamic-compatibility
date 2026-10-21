module
public import proofs.JointThermoComplexity.Complexity.NonleafEquationBranch

set_option autoImplicit false
@[expose] public section

/-! The nine nonleaf/formula branches have fixed code and use the exact raw preorder child sizes. -/

namespace JointThermoComplexity.Complexity.FormulaEquationBranch
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryCounterInit LocalBranchState
open NonleafEquationBranch PreorderLookahead

inductive Kind where
  | add | mul | neg | truth | falsity | eq | lt | conj | disj
  deriving DecidableEq

def template : Kind → LocalEquationTemplates.Kind
  | .add => .add
  | .mul => .mul
  | .neg => .neg
  | .truth => .truth
  | .falsity => .falsity
  | .eq => .eq
  | .lt => .lt
  | .conj => .conj
  | .disj => .disj

def first : Kind → Scan
  | .add | .mul | .eq | .lt => .term .left
  | .conj | .disj => .formula .left
  | _ => .none

def second : Kind → Scan
  | .lt => .term .right
  | _ => .none

def leftSize (kind : Kind) (L : ℕ) (values : Fin 9 → ℕ) (input : List Bool) : ℕ := match kind with
  | .add | .mul | .eq | .lt => termSize L (input.drop 3)
  | .conj | .disj => formulaSize L (input.drop 3)
  | _ => values 6

def rightSize (kind : Kind) (L : ℕ) (values : Fin 9 → ℕ) (input : List Bool) : ℕ := match kind with
  | .lt => termSize L (termRest L (input.drop 3))
  | _ => values 7

theorem result_root (kind : Kind) (L : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (before input : List Bool) :
    (NonleafEquationBranch.result (first kind) (second kind) L counts values before input).values 0 = values 0 := by
  cases kind <;> simp [NonleafEquationBranch.result, queryResult, start, scanResult, first, second, LocalBranchQuery.Size.index]

theorem result_left (kind : Kind) (L : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (before input : List Bool) :
    (NonleafEquationBranch.result (first kind) (second kind) L counts values before input).values 6 = leftSize kind L values input := by
  cases kind <;> simp [NonleafEquationBranch.result, queryResult, start, scanResult, first, second, leftSize,
    LocalBranchQuery.Size.index, PhysicalSpanQuery.term_result_prefix, PhysicalSpanQuery.formula_result_prefix,
    PhysicalSpanQuery.termPrefix, PhysicalSpanQuery.formulaPrefix, termSize, formulaSize]

theorem result_right (kind : Kind) (L : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (before input : List Bool) :
    (NonleafEquationBranch.result (first kind) (second kind) L counts values before input).values 7 = rightSize kind L values input := by
  cases kind <;> simp [NonleafEquationBranch.result, queryResult, start, scanResult, first, second, rightSize,
    LocalBranchQuery.Size.index, PhysicalSpanQuery.term_result_prefix, PhysicalSpanQuery.termPrefix, termSize, termRest]

theorem result_addresses (kind : Kind) (L : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (before input : List Bool) :
    LocalAddressSetup.addressValues (NonleafEquationBranch.result (first kind) (second kind) L counts values before input).values =
      LocalEquationTemplates.formulaValues (values 0) (leftSize kind L values input) (rightSize kind L values input) := by
  rw [LocalAddressSetup.addressValues_eq, result_root, result_left, result_right]

def rows (kind : Kind) (L : ℕ) (values : Fin 9 → ℕ) (input : List Bool) : PreorderLocalRows.Rows :=
  LocalEquationTemplates.wordRows (template kind)
    (LocalEquationTemplates.formulaValues (values 0) (leftSize kind L values input) (rightSize kind L values input))

def isTerm : Kind → Bool
  | .add | .mul | .neg => true
  | _ => false

def termKind : Kind → SourceTermToken.Kind
  | .add => .add
  | .mul => .mul
  | .neg => .neg
  | _ => .invalid

def formulaKind : Kind → SourceFormulaScan.Kind
  | .truth => .truth
  | .falsity => .falsity
  | .eq => .eq
  | .lt => .lt
  | .conj => .conj
  | .disj => .disj
  | _ => .invalid

attribute [local simp] NumberedTermEquations.relabel_atom NumberedTermEquations.relabel_constant
  NumberedTermEquations.relabel_sub NumberedTermEquations.relabel_add NumberedTermEquations.relabel_product

theorem term_rows (kind : Kind) (hk : isTerm kind = true) (L : ℕ) (values : Fin 9 → ℕ) (input : List Bool)
    (ha : SourceTags.accepted input = true)
    (hc : SourceTermToken.classify (SourceTermToken.tagBits input) = termKind kind) :
    rows kind L values input = PreorderLocalRows.termRows L (values 0) input := by
  cases kind <;> simp_all [isTerm, rows, template, leftSize, rightSize, termKind,
    LocalEquationTemplates.wordRows, LocalEquationTemplates.rows, LocalEquationTemplates.formulaValues,
    NumberedFormulaEquations.signPorts, PreorderLocalRows.termRows, PreorderLocalRows.variableWord]

theorem formula_rows (kind : Kind) (hk : isTerm kind = false) (L : ℕ) (values : Fin 9 → ℕ) (input : List Bool)
    (ha : SourceTags.accepted input = true)
    (hc : SourceFormulaScan.classify (SourceTermToken.tagBits input) = formulaKind kind) :
    rows kind L values input = PreorderLocalRows.formulaRows L (values 0) input := by
  cases kind <;> simp_all [isTerm, rows, template, leftSize, rightSize, formulaKind,
    LocalEquationTemplates.wordRows_eq, LocalEquationTemplates.realize, LocalEquationTemplates.rows,
    LocalEquationTemplates.formulaValues, NumberedFormulaEquations.signPorts,
    PreorderLocalRows.formulaRows, PreorderLocalRows.words, PreorderLocalRows.variableWord]
  intro a _
  apply congrArg (SparseInteger.relabel BitCodec.naturalCode)
  rw [NumberedTermEquations.relabel_comp]
  exact congrArg (fun f => SparseInteger.relabel f a)
    (LocalEquationTemplates.equality_values (values 0) (termSize L (input.drop 3)) (values 7))

theorem output_eq (kind : Kind) (L : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (before input : List Bool) :
    NonleafEquationBranch.output (template kind) (first kind) (second kind) L counts values before input =
      RowEntriesCodec.entries (rows kind L values input) := by
  rw [NonleafEquationBranch.output, result_addresses]
  rfl

def machine (kind : Kind) : TM 32 := NonleafEquationBranch.machine (template kind) (first kind) (second kind)

theorem hoareTime (kind : Kind) (L B C : ℕ) (counts : Counts) (values : Fin 9 → ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hlen : input.length ≤ L) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (machine kind).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work anchor) ∧ Ready counts values L R work)
      (fun inp work out =>
        let q := NonleafEquationBranch.result (first kind) (second kind) L counts values before input
        Cursor before input (emitted ++ RowEntriesCodec.entries (rows kind L values input)) inp work out ∧
          (∀ j, Parked (work j)) ∧ IsReg 0 (work anchor) ∧ Ready q.counts (LocalAddressSetup.prepared q.values) L R work)
      (13 * before.length + L + NonleafEquationBranch.forwardTime L B C + 23) := by
  have h := NonleafEquationBranch.hoareTime (template kind) (first kind) (second kind) L B C counts values before input emitted
    hz hv hc hlen R hR
  simpa only [machine, output_eq] using h

end JointThermoComplexity.Complexity.FormulaEquationBranch

#print axioms JointThermoComplexity.Complexity.FormulaEquationBranch.result_addresses
#print axioms JointThermoComplexity.Complexity.FormulaEquationBranch.output_eq
#print axioms JointThermoComplexity.Complexity.FormulaEquationBranch.term_rows
#print axioms JointThermoComplexity.Complexity.FormulaEquationBranch.formula_rows
#print axioms JointThermoComplexity.Complexity.FormulaEquationBranch.hoareTime
