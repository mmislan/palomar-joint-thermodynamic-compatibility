module
public import proofs.JointThermoComplexity.Complexity.CounterProgramFrame
public import Mathlib.Tactic.FinCases

set_option autoImplicit false
@[expose] public section

/-! A fixed counter program for branch, species and reaction dimensions. -/

namespace JointThermoComplexity.Complexity.DenseDimensionProgram
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction

def external (boxed : Bool) (n : ℕ) : ℕ := if boxed then n else 2 * n + 1
def initial (n t : ℕ) : Fin 6 → ℕ := ![n, t, 0, 0, 0, 0]
def result (boxed : Bool) (n t : ℕ) : Fin 6 → ℕ :=
  ![n, t, t + 2, external boxed n, external boxed n + 2 * t + 2, 2 * t + 4]

def program (boxed : Bool) : CounterProgram 6 :=
  [.copy 1 2 (by decide), .increment 2, .increment 2, .copy 0 3 (by decide)] ++
  (if boxed then [] else [.add 0 3 (by decide), .increment 3]) ++
  [.copy 1 4 (by decide), .add 1 4 (by decide), .add 3 4 (by decide), .increment 4, .increment 4,
    .copy 2 5 (by decide), .add 2 5 (by decide)]

theorem eval (boxed : Bool) (n t : ℕ) : counterProgramEval (program boxed) (initial n t) = result boxed n t := by
  funext j
  cases boxed <;> fin_cases j <;>
    norm_num [program, initial, result, external, counterProgramEval, CounterInstruction.eval, Function.update_apply] <;> omega

def timeBound (boxed : Bool) (L : ℕ) : ℕ := counterIterTime (program boxed).length (16 * L)
noncomputable def timePolynomial (boxed : Bool) : Polynomial ℕ :=
  (counterTimePolynomial (program boxed).length).comp (16 * Polynomial.X)

theorem timePolynomial_eval (boxed : Bool) (L : ℕ) : (timePolynomial boxed).eval L = timeBound boxed L := by
  simp [timePolynomial, timeBound, Polynomial.eval_comp, counterTimePolynomial_eval]

theorem initial_bound (L n t : ℕ) (hn : n ≤ L) (ht : t ≤ 16 * L) : ∀ j, initial n t j ≤ 16 * L := by
  intro j
  fin_cases j
  · change n ≤ 16 * L
    omega
  · exact ht
  all_goals exact Nat.zero_le _

end JointThermoComplexity.Complexity.DenseDimensionProgram

#print axioms JointThermoComplexity.Complexity.DenseDimensionProgram.eval
#print axioms JointThermoComplexity.Complexity.DenseDimensionProgram.timePolynomial_eval
