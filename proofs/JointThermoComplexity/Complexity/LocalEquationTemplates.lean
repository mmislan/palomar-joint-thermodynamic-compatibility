module
public import proofs.JointThermoComplexity.Complexity.AddressRowProgram
public import proofs.JointThermoComplexity.Complexity.PreorderLocalRows

set_option autoImplicit false
@[expose] public section

/-! Every nonleaf and formula case uses one fixed sparse row template. -/

namespace JointThermoComplexity.Complexity.LocalEquationTemplates
open SparseInteger RealSyntax SourceCoordinateEnumeration NumberedTermEquations
variable {n : ℕ}

inductive Kind where
  | add | mul | neg | truth | falsity | eq | lt | conj | disj | activate
  deriving DecidableEq

def embed (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩

def rows : Kind → List (Poly (Fin 6))
  | .add => [sub (atom 0) (add (atom 1) (atom 2))]
  | .mul => [sub (atom 0) (product (atom 1) (atom 2))]
  | .neg => [add (atom 0) (atom 1)]
  | .truth => [product (atom 0) (sub (atom 0) (constant 1))]
  | .falsity => [atom 0]
  | .eq => SparseCircuit.equalityActivation.map (relabel embed)
  | .lt => SparseCircuit.strictSign
  | .conj => [product (atom 0) (sub (atom 0) (constant 1)), sub (atom 1) (atom 0), sub (atom 2) (atom 0)]
  | .disj => [product (atom 0) (sub (atom 0) (constant 1)), sub (add (atom 1) (atom 2)) (atom 0)]
  | .activate => [sub (atom 0) (constant 1)]

def realize (kind : Kind) (values : Fin 6 → ℕ) : List (Poly ℕ) := (rows kind).map (relabel values)

def wordRows (kind : Kind) (values : Fin 6 → ℕ) : PreorderLocalRows.Rows :=
  (rows kind).map (relabel (fun i => BitCodec.naturalCode (values i)))

theorem wordRows_eq (kind : Kind) (values : Fin 6 → ℕ) :
    wordRows kind values = PreorderLocalRows.words (realize kind values) := by
  simp only [wordRows, PreorderLocalRows.words, realize, map_relabel_comp, Function.comp_def]

def termValues (offset leftSize : ℕ) : Fin 6 → ℕ := ![offset, offset + 1, offset + 1 + leftSize, 0, 0, 0]

def formulaValues (offset leftSize rightSize : ℕ) : Fin 6 → ℕ :=
  NumberedFormulaEquations.signPorts offset (offset + 1) (offset + 1 + leftSize) (offset + 1 + leftSize + rightSize)

attribute [local simp] relabel_atom relabel_constant relabel_sub relabel_add relabel_product relabel_square

theorem add_local (s t : Term n) (offset : ℕ) :
    realize .add (termValues offset s.size) = PreorderLocalRows.termLocal (.add s t) offset := by
  simp [realize, rows, termValues, PreorderLocalRows.termLocal]

theorem mul_local (s t : Term n) (offset : ℕ) :
    realize .mul (termValues offset s.size) = PreorderLocalRows.termLocal (.mul s t) offset := by
  simp [realize, rows, termValues, PreorderLocalRows.termLocal]

theorem neg_local (s : Term n) (offset : ℕ) :
    realize .neg (termValues offset 0) = PreorderLocalRows.termLocal (.neg s) offset := by
  simp [realize, rows, termValues, PreorderLocalRows.termLocal]

theorem equality_values (offset leftSize rightSize : ℕ) :
    formulaValues offset leftSize rightSize ∘ embed =
      NumberedFormulaEquations.equalityPorts offset (offset + 1) (offset + 1 + leftSize) := by
  funext i
  fin_cases i <;> rfl

theorem eq_local (s t : Term n) (offset : ℕ) :
    realize .eq (formulaValues offset s.size t.size) = PreorderLocalRows.formulaLocal (.eq s t) offset := by
  rw [realize, rows, map_relabel_comp, equality_values]
  rfl

theorem lt_local (s t : Term n) (offset : ℕ) :
    realize .lt (formulaValues offset s.size t.size) = PreorderLocalRows.formulaLocal (.lt s t) offset := rfl

theorem truth_local (offset : ℕ) :
    realize .truth (termValues offset 0) = PreorderLocalRows.formulaLocal (Formula.truth : Formula n) offset := by
  simp [realize, rows, termValues, PreorderLocalRows.formulaLocal]

theorem falsity_local (offset : ℕ) :
    realize .falsity (termValues offset 0) = PreorderLocalRows.formulaLocal (Formula.falsity : Formula n) offset := by
  simp [realize, rows, termValues, PreorderLocalRows.formulaLocal]

theorem conj_local (p q : Formula n) (offset : ℕ) :
    realize .conj (termValues offset (formulaCount p)) = PreorderLocalRows.formulaLocal (.conj p q) offset := by
  simp [realize, rows, termValues, PreorderLocalRows.formulaLocal]

theorem disj_local (p q : Formula n) (offset : ℕ) :
    realize .disj (termValues offset (formulaCount p)) = PreorderLocalRows.formulaLocal (.disj p q) offset := by
  simp [realize, rows, termValues, PreorderLocalRows.formulaLocal]

theorem activation (offset : ℕ) : realize .activate (termValues offset 0) = [sub (atom offset) (constant 1)] := by
  simp [realize, rows, termValues]

end JointThermoComplexity.Complexity.LocalEquationTemplates

#print axioms JointThermoComplexity.Complexity.LocalEquationTemplates.wordRows_eq
#print axioms JointThermoComplexity.Complexity.LocalEquationTemplates.eq_local
#print axioms JointThermoComplexity.Complexity.LocalEquationTemplates.lt_local
