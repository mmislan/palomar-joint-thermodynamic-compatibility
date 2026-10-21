module

public import proofs.Complexitylib.Models.TuringMachine.Registers.Arith

@[expose] public section

/-! # Executable arithmetic counter programs and actual finite-state compilation

Distinct-register conditions are part of the instruction data required by the
existing arithmetic machines. Programs and their compiled finite control are
fixed independently of the input word. No time or correctness certificate is
stored in the data.
-/

namespace DInstabilityComplexity.MachineConstruction

open Complexity Complexity.TM

inductive CounterInstruction (n : ℕ) where
  | increment (r : Fin n)
  | clear (r : Fin n)
  | copy (src dst : Fin n) (hne : src ≠ dst)
  | add (src dst : Fin n) (hne : src ≠ dst)
  | mulAdd (a b dst : Fin n) (hab : a ≠ b) (had : a ≠ dst) (hbd : b ≠ dst)

namespace CounterInstruction

def eval : CounterInstruction n → (Fin n → ℕ) → (Fin n → ℕ)
  | .increment r, v => Function.update v r (v r + 1)
  | .clear r, v => Function.update v r 0
  | .copy src dst _, v => Function.update v dst (v src)
  | .add src dst _, v => Function.update v dst (v dst + v src)
  | .mulAdd a b dst _ _ _, v => Function.update v dst (v dst + v a * v b)

def machine : CounterInstruction n → TM n
  | .increment r => incRegTM r
  | .clear r => clearRegTM r
  | .copy src dst _ => copyIntoTM src dst
  | .add src dst _ => addIntoTM src dst
  | .mulAdd a b dst _ _ _ => mulAddIntoTM a b dst

def time : CounterInstruction n → (Fin n → ℕ) → ℕ
  | .increment r, v => 2 * v r + 4
  | .clear r, v => 2 * v r + 4
  | .copy src dst _, v =>
      (2 * v dst + 4) + 1 + (v src * ((2 * (0 + v src) + 4) + 2) + (v src + 2))
  | .add src dst _, v =>
      v src * ((2 * (v dst + v src) + 4) + 2) + (v src + 2)
  | .mulAdd a b dst _ _ _, v =>
      v a * (mulAddBound (v a) (v b) (v dst) + 2) + (v a + 2)

end CounterInstruction

abbrev CounterProgram (n : ℕ) := List (CounterInstruction n)

def counterValues (v : Fin n → ℕ) : Fin n → Tape := fun j => regTape (v j)

theorem counterValues_parked (v : Fin n → ℕ) (j : Fin n) : Parked (counterValues v j) :=
  parked_regTape _

theorem counterValues_update (v : Fin n → ℕ) (r : Fin n) (a : ℕ) :
    counterValues (Function.update v r a) = Function.update (counterValues v) r (regTape a) := by
  funext j
  by_cases hj : j = r
  · subst j
    simp only [counterValues, Function.update_self]
  · simp only [counterValues, Function.update_of_ne hj]

def counterProgramEval : CounterProgram n → (Fin n → ℕ) → (Fin n → ℕ)
  | [], v => v
  | i :: is, v => counterProgramEval is (i.eval v)

def counterProgramMachine : CounterProgram n → TM n
  | [] => skipTM
  | i :: is => seqTM i.machine (counterProgramMachine is)

def counterProgramTime : CounterProgram n → (Fin n → ℕ) → ℕ
  | [], _ => 1
  | i :: is, v => i.time v + 1 + counterProgramTime is (i.eval v)

#print axioms counterValues_update

end DInstabilityComplexity.MachineConstruction
