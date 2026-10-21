module

public import proofs.DInstabilityComplexity.CounterProgramSemantics
public import proofs.Complexitylib.Asymptotics

@[expose] public section

/-! # Unconditional polynomial bounds for every fixed arithmetic counter program

Each instruction grows bounded registers by at most 2(B+1)^2 and takes at most
100(B+1)^4 actual machine steps. Iterating these explicit polynomials for a fixed
program gives a polynomial bound without accepting any complexity certificate.
-/

namespace DInstabilityComplexity.MachineConstruction

open Complexity Complexity.TM Polynomial

def counterNextBound (B : ℕ) : ℕ := 2 * (B + 1) ^ 2

theorem counter_update_bounded (v : Fin n → ℕ) (B : ℕ) (hv : ∀ j, v j ≤ B)
    (r : Fin n) (a : ℕ) (ha : a ≤ counterNextBound B) :
    ∀ j, Function.update v r a j ≤ counterNextBound B := by
  intro j
  by_cases hj : j = r
  · subst j
    simpa only [Function.update_self] using ha
  · rw [Function.update_of_ne hj]
    have h := hv j
    unfold counterNextBound
    nlinarith

theorem CounterInstruction.eval_bound (i : CounterInstruction n) (v : Fin n → ℕ) (B : ℕ)
    (hv : ∀ j, v j ≤ B) : ∀ j, i.eval v j ≤ counterNextBound B := by
  cases i with
  | increment r =>
    apply counter_update_bounded v B hv r
    have h := hv r
    unfold counterNextBound
    nlinarith
  | clear r => exact counter_update_bounded v B hv r 0 (Nat.zero_le _)
  | copy src dst _ =>
    apply counter_update_bounded v B hv dst
    have h := hv src
    unfold counterNextBound
    nlinarith
  | add src dst _ =>
    apply counter_update_bounded v B hv dst
    have hs := hv src
    have hd := hv dst
    unfold counterNextBound
    nlinarith
  | mulAdd a b dst _ _ _ =>
    apply counter_update_bounded v B hv dst
    have hm := Nat.mul_le_mul (hv a) (hv b)
    have hd := hv dst
    unfold counterNextBound
    nlinarith

theorem CounterInstruction.time_monotone (i : CounterInstruction n) {v w : Fin n → ℕ}
    (hv : ∀ j, v j ≤ w j) : i.time v ≤ i.time w := by
  cases i <;> simp only [CounterInstruction.time, mulAddBound] <;> gcongr <;> exact hv _

theorem CounterInstruction.time_bound (i : CounterInstruction n) (v : Fin n → ℕ) (B : ℕ)
    (hv : ∀ j, v j ≤ B) : i.time v ≤ 100 * (B + 1) ^ 4 := by
  have hm := i.time_monotone hv
  have hb : i.time (fun _ => B) ≤ 100 * (B + 1) ^ 4 := by
    cases i <;> simp only [CounterInstruction.time, mulAddBound] <;> ring_nf <;> omega
  exact hm.trans hb

def counterIterBound : ℕ → ℕ → ℕ
  | 0, B => B
  | k + 1, B => counterIterBound k (counterNextBound B)

def counterIterTime : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, B => 100 * (B + 1) ^ 4 + 1 + counterIterTime k (counterNextBound B)

theorem counterProgramEval_bound (p : CounterProgram n) (v : Fin n → ℕ) (B : ℕ)
    (hv : ∀ j, v j ≤ B) : ∀ j, counterProgramEval p v j ≤ counterIterBound p.length B := by
  induction p generalizing v B with
  | nil => exact hv
  | cons i is ih => exact ih (i.eval v) (counterNextBound B) (i.eval_bound v B hv)

theorem counterProgramTime_bound (p : CounterProgram n) (v : Fin n → ℕ) (B : ℕ)
    (hv : ∀ j, v j ≤ B) : counterProgramTime p v ≤ counterIterTime p.length B := by
  induction p generalizing v B with
  | nil => exact Nat.le_refl 1
  | cons i is ih =>
    have hi := i.time_bound v B hv
    have ht := ih (i.eval v) (counterNextBound B) (i.eval_bound v B hv)
    change i.time v + 1 + counterProgramTime is (i.eval v) ≤
      100 * (B + 1) ^ 4 + 1 + counterIterTime is.length (counterNextBound B)
    omega

noncomputable def counterBoundPolynomial : ℕ → Polynomial ℕ
  | 0 => X
  | k + 1 => (counterBoundPolynomial k).comp (2 * (X + 1) ^ 2)

noncomputable def counterTimePolynomial : ℕ → Polynomial ℕ
  | 0 => 1
  | k + 1 => 100 * (X + 1) ^ 4 + 1 + (counterTimePolynomial k).comp (2 * (X + 1) ^ 2)

theorem counterBoundPolynomial_eval (k B : ℕ) : (counterBoundPolynomial k).eval B = counterIterBound k B := by
  induction k generalizing B with
  | zero => simp [counterBoundPolynomial, counterIterBound]
  | succ k ih => simp [counterBoundPolynomial, counterIterBound, counterNextBound, ih]

theorem counterTimePolynomial_eval (k B : ℕ) : (counterTimePolynomial k).eval B = counterIterTime k B := by
  induction k generalizing B with
  | zero => simp [counterTimePolynomial, counterIterTime]
  | succ k ih => simp [counterTimePolynomial, counterIterTime, counterNextBound, ih]

#print axioms CounterInstruction.eval_bound
#print axioms CounterInstruction.time_bound
#print axioms counterProgramTime_bound
#print axioms counterBoundPolynomial_eval
#print axioms counterTimePolynomial_eval

end DInstabilityComplexity.MachineConstruction
