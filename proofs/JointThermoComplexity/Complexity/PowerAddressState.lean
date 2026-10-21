module
public import proofs.JointThermoComplexity.Complexity.ExactGateCount

set_option autoImplicit false
@[expose] public section

/-! Natural address evolution, including the final next address which may equal the arity. -/

namespace JointThermoComplexity.Complexity.PowerAddressState

structure State where
  nextAddress : ℕ
  accumulatorAddress : ℕ
  powerAddress : ℕ

def State.advance (s : State) : Bool → State
  | false => ⟨s.nextAddress + 1, s.accumulatorAddress, s.nextAddress⟩
  | true => ⟨s.nextAddress + 2, s.nextAddress, s.nextAddress + 1⟩

def State.run (s : State) : List Bool → State
  | [] => s
  | bit :: rest => (s.advance bit).run rest

def Fits (arity : ℕ) (bits : List Bool) (s : State) : Prop :=
  s.accumulatorAddress < arity ∧ s.powerAddress < arity ∧ s.nextAddress + ExactGateCount.bitsCost bits ≤ arity

theorem step_fresh (arity : ℕ) (bit : Bool) (rest : List Bool) (s : State) (h : Fits arity (bit :: rest) s) :
    s.nextAddress < arity ∧ (bit = true → s.nextAddress + 1 < arity) ∧ Fits arity rest (s.advance bit) := by
  rcases h with ⟨ha, hp, hn⟩
  cases bit with
  | false =>
    change s.nextAddress + (1 + ExactGateCount.bitsCost rest) ≤ arity at hn
    refine ⟨by omega, (fun h => by cases h), ?_⟩
    change s.accumulatorAddress < arity ∧ s.nextAddress < arity ∧
      (s.nextAddress + 1) + ExactGateCount.bitsCost rest ≤ arity
    omega
  | true =>
    change s.nextAddress + (2 + ExactGateCount.bitsCost rest) ≤ arity at hn
    refine ⟨by omega, (fun _ => by omega), ?_⟩
    change s.nextAddress < arity ∧ s.nextAddress + 1 < arity ∧
      (s.nextAddress + 2) + ExactGateCount.bitsCost rest ≤ arity
    omega

theorem run_next (s : State) (bits : List Bool) :
    (s.run bits).nextAddress = s.nextAddress + ExactGateCount.bitsCost bits := by
  induction bits generalizing s with
  | nil => simp only [State.run, ExactGateCount.bitsCost, Nat.add_zero]
  | cons bit rest ih =>
    rw [State.run, ih]
    cases bit <;> simp only [State.advance, ExactGateCount.bitsCost, Bool.false_eq_true, ↓reduceIte] <;> omega

end JointThermoComplexity.Complexity.PowerAddressState

#print axioms JointThermoComplexity.Complexity.PowerAddressState.step_fresh
