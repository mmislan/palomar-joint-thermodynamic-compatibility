module
public import proofs.JointThermoComplexity.Complexity.RealSyntax
public import Mathlib.Data.Fin.Basic

set_option autoImplicit false
@[expose] public section

/-!
# Arithmetic gates and existential auxiliary variables

A gate can read only original inputs and earlier gates. A circuit's finite
structure enforces this order. Its integer data are independent of real
witnesses. The generated equations use a single shared assignment; satisfying
them forces every auxiliary variable to its actual circuit value. This is the
semantic bridge needed before proving encoded size and construction runtime.
-/

namespace JointThermoComplexity.Complexity.RealCircuit
open RealSyntax

inductive Step (n k : ℕ) where
  | constant : ℤ → Step n k
  | input : Fin n → Step n k
  | add : Fin k → Fin k → Step n k
  | mul : Fin k → Fin k → Step n k
  | neg : Fin k → Step n k
  deriving DecidableEq

inductive Circuit (n : ℕ) : ℕ → Type where
  | nil : Circuit n 0
  | snoc {k : ℕ} : Circuit n k → Step n k → Circuit n (k + 1)

variable {n k m : ℕ}

def Step.eval (s : Step n k) (ρ : Fin n → ℝ) (v : Fin k → ℝ) : ℝ :=
  match s with
  | .constant z => z
  | .input i => ρ i
  | .add i j => v i + v j
  | .mul i j => v i * v j
  | .neg i => -v i

def Circuit.eval : {k : ℕ} → Circuit n k → (Fin n → ℝ) → Fin k → ℝ
  | _, .nil, _ => Fin.elim0
  | _, .snoc c s, ρ => Fin.lastCases (s.eval ρ (c.eval ρ)) (c.eval ρ)

@[simp] theorem Circuit.eval_snoc_last (c : Circuit n k) (s : Step n k)
    (ρ : Fin n → ℝ) :
    (c.snoc s).eval ρ (Fin.last k) = s.eval ρ (c.eval ρ) := by
  simp [Circuit.eval]

@[simp] theorem Circuit.eval_snoc_castSucc (c : Circuit n k) (s : Step n k)
    (ρ : Fin n → ℝ) (i : Fin k) :
    (c.snoc s).eval ρ i.castSucc = c.eval ρ i := by
  simp [Circuit.eval]

def Circuit.Satisfies : {k : ℕ} → Circuit n k → (Fin n → ℝ) → (Fin k → ℝ) → Prop
  | _, .nil, _, _ => True
  | _, .snoc c s, ρ, v =>
      c.Satisfies ρ (fun i => v i.castSucc) ∧
      v (Fin.last _) = s.eval ρ (fun i => v i.castSucc)

/-- Every auxiliary value is forced by the ordered gate equations. -/
theorem Circuit.satisfies_iff_eval (c : Circuit n k) (ρ : Fin n → ℝ) (v : Fin k → ℝ) :
    c.Satisfies ρ v ↔ v = c.eval ρ := by
  induction c with
  | nil =>
    constructor
    · intro _
      funext i
      exact Fin.elim0 i
    · intro _
      trivial
  | @snoc k c s ih =>
    constructor
    · rintro ⟨hp, hs⟩
      have hv := (ih (fun i => v i.castSucc)).mp hp
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [hv] using hs
      · simpa only [Circuit.eval_snoc_castSucc] using congrFun hv j
    · intro hv
      subst v
      refine ⟨?_, ?_⟩
      · apply (ih _).mpr
        funext i
        simp
      · simp

theorem Circuit.satisfies_eval (c : Circuit n k) (ρ : Fin n → ℝ) :
    c.Satisfies ρ (c.eval ρ) := (c.satisfies_iff_eval ρ _).mpr rfl

def Step.term (s : Step n k) (inputs : Fin n → Fin m) (previous : Fin k → Fin m) : Term m :=
  match s with
  | .constant z => .int z
  | .input i => .var (inputs i)
  | .add i j => .add (.var (previous i)) (.var (previous j))
  | .mul i j => .mul (.var (previous i)) (.var (previous j))
  | .neg i => .neg (.var (previous i))

theorem Step.term_eval (s : Step n k) (inputs : Fin n → Fin m)
    (previous : Fin k → Fin m) (η : Fin m → ℝ) :
    (s.term inputs previous).eval η =
      s.eval (fun i => η (inputs i)) (fun i => η (previous i)) := by
  cases s <;> rfl

def Circuit.formula : {k : ℕ} → Circuit n k →
    (Fin n → Fin m) → (Fin k → Fin m) → Formula m
  | _, .nil, _, _ => .truth
  | _, .snoc c s, inputs, outputs =>
      .conj (c.formula inputs (fun i => outputs i.castSucc))
        (.eq (.var (outputs (Fin.last _))) (s.term inputs (fun i => outputs i.castSucc)))

/-- The generated formula expresses precisely the same ordered gate equations. -/
theorem Circuit.formula_eval_iff (c : Circuit n k) (inputs : Fin n → Fin m)
    (outputs : Fin k → Fin m) (η : Fin m → ℝ) :
    (c.formula inputs outputs).eval η ↔
      c.Satisfies (fun i => η (inputs i)) (fun i => η (outputs i)) := by
  induction c with
  | nil => rfl
  | snoc c s ih =>
    simp only [Circuit.formula, Formula.eval, Term.eval, Step.term_eval,
      Circuit.Satisfies, ih]

theorem Circuit.formula_forces_values (c : Circuit n k) (inputs : Fin n → Fin m)
    (outputs : Fin k → Fin m) (η : Fin m → ℝ)
    (h : (c.formula inputs outputs).eval η) :
    (fun i => η (outputs i)) = c.eval (fun i => η (inputs i)) :=
  (c.satisfies_iff_eval _ _).mp ((c.formula_eval_iff inputs outputs η).mp h)

/-- Every original assignment extends to the fresh, disjoint auxiliary block. -/
theorem Circuit.exists_extension (c : Circuit n k) (ρ : Fin n → ℝ) :
    ∃ η : Fin (n + k) → ℝ,
      (∀ i, η (Fin.castAdd k i) = ρ i) ∧
      (c.formula (Fin.castAdd k) (Fin.natAdd n)).eval η := by
  let η : Fin (n + k) → ℝ := Fin.addCases ρ (c.eval ρ)
  refine ⟨η, ?_, ?_⟩
  · intro i
    simp [η]
  · apply (c.formula_eval_iff _ _ η).mpr
    simpa [η] using c.satisfies_eval ρ

end JointThermoComplexity.Complexity.RealCircuit

#print axioms JointThermoComplexity.Complexity.RealCircuit.Circuit.satisfies_iff_eval
#print axioms JointThermoComplexity.Complexity.RealCircuit.Circuit.formula_forces_values
#print axioms JointThermoComplexity.Complexity.RealCircuit.Circuit.exists_extension
