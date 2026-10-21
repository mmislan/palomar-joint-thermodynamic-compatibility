module
public import proofs.JointThermoComplexity.Complexity.NetworkData

set_option autoImplicit false
@[expose] public section

/-! Finite formulas for activity, box, direction and per-motif production constraints. -/

namespace JointThermoComplexity.Complexity.NetworkFormula
open RealSyntax NetworkData
open scoped BigOperators

variable {n r c d m : ℕ}

def conjoin : List (Formula m) → Formula m
  | [] => .truth
  | p :: rest => .conj p (conjoin rest)

theorem eval_conjoin (ps : List (Formula m)) (η : Fin m → ℝ) :
    (conjoin ps).eval η ↔ ∀ p ∈ ps, p.eval η := by
  induction ps with
  | nil => simp [conjoin, Formula.eval]
  | cons p ps ih => simp [conjoin, Formula.eval, ih]

def allFin (f : Fin d → Formula m) : Formula m := conjoin (List.ofFn f)

theorem eval_allFin (f : Fin d → Formula m) (η : Fin m → ℝ) :
    (allFin f).eval η ↔ ∀ i, (f i).eval η := by
  simp [allFin, eval_conjoin]

def addTerms : List (Term m) → Term m
  | [] => .int 0
  | t :: rest => .add t (addTerms rest)

theorem eval_addTerms (ts : List (Term m)) (η : Fin m → ℝ) :
    (addTerms ts).eval η = (ts.map (Term.eval η)).sum := by
  induction ts with
  | nil => simp [addTerms, Term.eval]
  | cons t ts ih => simp [addTerms, Term.eval, ih]

def sumFin (f : Fin d → Term m) : Term m := addTerms (List.ofFn f)

theorem eval_sumFin (f : Fin d → Term m) (η : Fin m → ℝ) :
    (sumFin f).eval η = ∑ i, (f i).eval η := by
  simp [sumFin, eval_addTerms, List.map_ofFn, List.sum_ofFn, Function.comp_def]

def lessEqual (s t : Term m) : Formula m := .disj (.lt s t) (.eq s t)

theorem eval_lessEqual (s t : Term m) (η : Fin m → ℝ) :
    (lessEqual s t).eval η ↔ s.eval η ≤ t.eval η := by
  exact le_iff_lt_or_eq.symm

def boxFormula (box : Option ClosedBox) (z : Fin m) : Formula m :=
  match box with
  | none => .truth
  | some b => .conj
      (lessEqual (.int b.lower.numerator) (.mul (.int b.lower.denominator) (.var z)))
      (lessEqual (.mul (.int b.upper.denominator) (.var z)) (.int b.upper.numerator))

theorem eval_boxFormula (box : Option ClosedBox) (z : Fin m) (η : Fin m → ℝ) :
    (boxFormula box z).eval η ↔
      match box with | none => True | some b => b.Contains (η z) := by
  cases box <;>
    simp [boxFormula, Formula.eval, eval_lessEqual, Term.eval, ClosedBox.Contains]

def directionFormula (forward : Bool) (j : Fin m) : Formula m :=
  .lt (.int 0) (if forward then .var j else .neg (.var j))

theorem eval_directionFormula (forward : Bool) (j : Fin m) (η : Fin m → ℝ) :
    (directionFormula forward j).eval η ↔ direction forward (η j) := by
  cases forward <;> simp [directionFormula, Formula.eval, Term.eval, direction]

def productionTerm (Q : Network n r c) (a : Fin c) (s : Fin n)
    (j : Fin r → Fin m) : Term m :=
  sumFin (fun i => if i ∈ (Q.motifs a).reactions then
    .mul (.int (stoich (Q.reactions i) s)) (.var (j i)) else .int 0)

theorem eval_productionTerm (Q : Network n r c) (a : Fin c) (s : Fin n)
    (j : Fin r → Fin m) (η : Fin m → ℝ) :
    (productionTerm Q a s j).eval η = Q.production a s (fun i => η (j i)) := by
  simp [productionTerm, eval_sumFin, Network.production, Term.eval, apply_ite]

def constraintsFormula (Q : Network n r c) (z : Fin n → Fin m)
    (j : Fin r → Fin m) : Formula m :=
  .conj (allFin (fun s => .lt (.int 0) (.var (z s))))
    (.conj (allFin (fun s => boxFormula (Q.boxes s) (z s)))
      (allFin (fun a => .conj
        (allFin (fun i => if i ∈ (Q.motifs a).reactions then
          directionFormula (Q.forward i) (j i) else .truth))
        (allFin (fun s => if s ∈ (Q.motifs a).species then
          .lt (.int 0) (productionTerm Q a s j) else .truth)))))

theorem eval_constraintsFormula (Q : Network n r c) (z : Fin n → Fin m)
    (j : Fin r → Fin m) (η : Fin m → ℝ) :
    (constraintsFormula Q z j).eval η ↔
      Q.Constraints (fun s => η (z s)) (fun i => η (j i)) := by
  simp [constraintsFormula, Formula.eval, eval_allFin, eval_boxFormula,
    eval_directionFormula, eval_productionTerm, Network.Constraints, Term.eval, apply_ite]
  intro _ _
  rfl

end JointThermoComplexity.Complexity.NetworkFormula

#print axioms JointThermoComplexity.Complexity.NetworkFormula.eval_constraintsFormula
