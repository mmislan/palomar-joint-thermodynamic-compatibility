module
public import proofs.JointThermoComplexity.Complexity.BinaryPower
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
@[expose] public section

/-!
# Literal monomials with binary exponents

The construction appends input, repeated-squaring and product gates. Its data
depend only on the supplied finite term list. Correctness holds for every real
assignment, with an explicit bound in exponent bit lengths. The empty product
is one; zero exponents require no exceptional semantic hypothesis.
-/

namespace JointThermoComplexity.Complexity.MonomialCircuit
open RealCircuit
open scoped BigOperators

variable {n k m : ℕ}

def evalTerms (ρ : Fin n → ℝ) : List (Fin n × ℕ) → ℝ
  | [] => 1
  | item :: items => ρ item.1 ^ item.2 * evalTerms ρ items

def gateCost : List (Fin n × ℕ) → ℕ
  | [] => 0
  | item :: items => 3 + 2 * item.2.bits.length + gateCost items

structure State (n : ℕ) where
  size : ℕ
  circuit : Circuit n size
  accumulator : Fin size

def State.value (s : State n) (ρ : Fin n → ℝ) : ℝ :=
  s.circuit.eval ρ s.accumulator

def State.advance (s : State n) (item : Fin n × ℕ) : State n :=
  let first := s.circuit.snoc (.input item.1)
  let power := BinaryPower.build first (Fin.last s.size) item.2
  let previous := Fin.castLE (BinaryPower.build_size_ge first (Fin.last s.size) item.2)
    s.accumulator.castSucc
  ⟨power.size + 1, power.circuit.snoc (.mul previous power.accumulator), Fin.last power.size⟩

theorem State.advance_value (s : State n) (item : Fin n × ℕ) (ρ : Fin n → ℝ) :
    (s.advance item).value ρ = s.value ρ * ρ item.1 ^ item.2 := by
  have hp := BinaryPower.build_value (s.circuit.snoc (.input item.1))
    (Fin.last s.size) item.2 ρ
  have hk := BinaryPower.build_preserves (s.circuit.snoc (.input item.1))
    (Fin.last s.size) item.2 s.accumulator.castSucc ρ
  simp only [BinaryPower.State.accValue] at hp
  simp only [State.advance, State.value, Circuit.eval_snoc_last, Step.eval]
  rw [hk, hp]
  simp only [Circuit.eval_snoc_castSucc, Circuit.eval_snoc_last, Step.eval]

theorem State.advance_size_ge (s : State n) (item : Fin n × ℕ) :
    s.size ≤ (s.advance item).size := by
  have h := BinaryPower.build_size_ge (s.circuit.snoc (.input item.1))
    (Fin.last s.size) item.2
  simp only [State.advance]
  omega

theorem State.advance_size_le (s : State n) (item : Fin n × ℕ) :
    (s.advance item).size ≤ s.size + 3 + 2 * item.2.bits.length := by
  have h := BinaryPower.build_size_le (s.circuit.snoc (.input item.1))
    (Fin.last s.size) item.2
  simp only [State.advance]
  omega

theorem State.advance_preserves (s : State n) (item : Fin n × ℕ) (i : Fin s.size)
    (ρ : Fin n → ℝ) :
    (s.advance item).circuit.eval ρ (Fin.castLE (s.advance_size_ge item) i) =
      s.circuit.eval ρ i := by
  have hk := BinaryPower.build_preserves (s.circuit.snoc (.input item.1))
    (Fin.last s.size) item.2 i.castSucc ρ
  have hi : Fin.castLE (s.advance_size_ge item) i =
      (Fin.castLE (BinaryPower.build_size_ge (s.circuit.snoc (.input item.1))
        (Fin.last s.size) item.2) i.castSucc).castSucc := by
    apply Fin.ext
    rfl
  rw [hi]
  simpa only [State.advance, Circuit.eval_snoc_castSucc] using hk

def State.runTerms (s : State n) : List (Fin n × ℕ) → State n
  | [] => s
  | item :: items => (s.advance item).runTerms items

theorem State.runTerms_value (s : State n) (items : List (Fin n × ℕ)) (ρ : Fin n → ℝ) :
    (s.runTerms items).value ρ = s.value ρ * evalTerms ρ items := by
  induction items generalizing s with
  | nil => simp [State.runTerms, evalTerms]
  | cons item items ih =>
    rw [State.runTerms, ih, State.advance_value]
    simp only [evalTerms, mul_assoc]

theorem State.runTerms_size_ge (s : State n) (items : List (Fin n × ℕ)) :
    s.size ≤ (s.runTerms items).size := by
  induction items generalizing s with
  | nil => exact Nat.le_refl _
  | cons item items ih => exact (s.advance_size_ge item).trans (ih (s.advance item))

theorem State.runTerms_size_le (s : State n) (items : List (Fin n × ℕ)) :
    (s.runTerms items).size ≤ s.size + gateCost items := by
  induction items generalizing s with
  | nil => simp [State.runTerms, gateCost]
  | cons item items ih =>
    have h := ih (s.advance item)
    have ha := s.advance_size_le item
    simp only [State.runTerms, gateCost]
    omega

theorem State.runTerms_preserves (s : State n) (items : List (Fin n × ℕ))
    (i : Fin s.size) (ρ : Fin n → ℝ) :
    (s.runTerms items).circuit.eval ρ (Fin.castLE (s.runTerms_size_ge items) i) =
      s.circuit.eval ρ i := by
  induction items generalizing s with
  | nil => rfl
  | cons item items ih =>
    change ((s.advance item).runTerms items).circuit.eval ρ
      (Fin.castLE ((s.advance item).runTerms_size_ge items)
        (Fin.castLE (s.advance_size_ge item) i)) = s.circuit.eval ρ i
    rw [ih (s.advance item)]
    exact s.advance_preserves item i ρ

def start (c : Circuit n k) : State n :=
  ⟨k + 1, c.snoc (.constant 1), Fin.last k⟩

def build (c : Circuit n k) (items : List (Fin n × ℕ)) : State n :=
  (start c).runTerms items

theorem build_value (c : Circuit n k) (items : List (Fin n × ℕ)) (ρ : Fin n → ℝ) :
    (build c items).value ρ = evalTerms ρ items := by
  unfold build
  rw [State.runTerms_value]
  simp [start, State.value, Step.eval]

theorem build_size_le (c : Circuit n k) (items : List (Fin n × ℕ)) :
    (build c items).size ≤ k + 1 + gateCost items :=
  State.runTerms_size_le (start c) items

theorem build_size_ge (c : Circuit n k) (items : List (Fin n × ℕ)) :
    k ≤ (build c items).size :=
  (Nat.le_succ k).trans (State.runTerms_size_ge (start c) items)

theorem build_preserves (c : Circuit n k) (items : List (Fin n × ℕ))
    (i : Fin k) (ρ : Fin n → ℝ) :
    (build c items).circuit.eval ρ (Fin.castLE (build_size_ge c items) i) = c.eval ρ i := by
  have h := State.runTerms_preserves (start c) items i.castSucc ρ
  have hi : Fin.castLE ((start c).runTerms_size_ge items) i.castSucc =
      Fin.castLE (build_size_ge c items) i := by
    apply Fin.ext
    rfl
  rw [hi] at h
  simpa [build, start] using h

def denseTerms (γ : Fin n → ℕ) : List (Fin n × ℕ) := List.ofFn (fun i => (i, γ i))

theorem evalTerms_eq_prod (ρ : Fin n → ℝ) (items : List (Fin n × ℕ)) :
    evalTerms ρ items = (items.map (fun item => ρ item.1 ^ item.2)).prod := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [evalTerms, ih]

theorem eval_denseTerms (ρ : Fin n → ℝ) (γ : Fin n → ℕ) :
    evalTerms ρ (denseTerms γ) = ∏ i, ρ i ^ γ i := by
  rw [evalTerms_eq_prod]
  simp only [denseTerms, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

/-- The generated equations force the literal finite-species monomial. -/
theorem formula_forces_monomial (c : Circuit n k) (γ : Fin n → ℕ)
    (inputs : Fin n → Fin m) (outputs : Fin (build c (denseTerms γ)).size → Fin m)
    (η : Fin m → ℝ)
    (h : ((build c (denseTerms γ)).circuit.formula inputs outputs).eval η) :
    η (outputs (build c (denseTerms γ)).accumulator) = ∏ i, η (inputs i) ^ γ i := by
  have hv := (build c (denseTerms γ)).circuit.formula_forces_values inputs outputs η h
  have ha := congrFun hv (build c (denseTerms γ)).accumulator
  exact ha.trans ((build_value c (denseTerms γ) (fun i => η (inputs i))).trans
    (eval_denseTerms (fun i => η (inputs i)) γ))

end JointThermoComplexity.Complexity.MonomialCircuit

#print axioms JointThermoComplexity.Complexity.MonomialCircuit.build_value
#print axioms JointThermoComplexity.Complexity.MonomialCircuit.build_size_le
#print axioms JointThermoComplexity.Complexity.MonomialCircuit.build_preserves
#print axioms JointThermoComplexity.Complexity.MonomialCircuit.formula_forces_monomial
