module

public import proofs.DInstabilityComplexity.CounterProgramSyntax

@[expose] public section

/-! # Actual execution contracts for every compiled arithmetic counter program -/

namespace DInstabilityComplexity.MachineConstruction

open Complexity Complexity.TM

theorem CounterInstruction.machine_hoareTime (i : CounterInstruction n) (v : Fin n → ℕ)
    (inp : Tape) (ys : List Bool) (hinp : Parked inp) :
    i.machine.HoareTime (EmitPred inp (counterValues v) ys)
      (EmitPred inp (counterValues (i.eval v)) ys) (i.time v) := by
  cases i with
  | increment r =>
    simpa only [CounterInstruction.machine, CounterInstruction.eval, CounterInstruction.time,
      counterValues_update] using incRegTM_hoareTime r (v r) inp (counterValues v) ys hinp
        (fun j _ => counterValues_parked v j) rfl
  | clear r =>
    simpa only [CounterInstruction.machine, CounterInstruction.eval, CounterInstruction.time,
      counterValues_update] using clearRegTM_hoareTime r (v r) inp (counterValues v) ys hinp
        (fun j _ => counterValues_parked v j) rfl
  | copy src dst hne =>
    simpa only [CounterInstruction.machine, CounterInstruction.eval, CounterInstruction.time,
      counterValues_update] using copyIntoTM_hoareTime src dst hne (v src) (v dst) inp
        (counterValues v) ys hinp (fun j _ => counterValues_parked v j) rfl rfl
  | add src dst hne =>
    simpa only [CounterInstruction.machine, CounterInstruction.eval, CounterInstruction.time,
      counterValues_update] using addIntoTM_hoareTime src dst hne (v src) (v dst) inp
        (counterValues v) ys hinp (fun j _ => counterValues_parked v j) rfl rfl
  | mulAdd a b dst hab had hbd =>
    simpa only [CounterInstruction.machine, CounterInstruction.eval, CounterInstruction.time,
      counterValues_update] using mulAddIntoTM_hoareTime a b dst hab had hbd (v a) (v b) (v dst)
        inp (counterValues v) ys hinp (fun j _ => counterValues_parked v j) rfl rfl rfl

theorem counterProgramMachine_hoareTime (p : CounterProgram n) (v : Fin n → ℕ)
    (inp : Tape) (ys : List Bool) (hinp : Parked inp) :
    (counterProgramMachine p).HoareTime (EmitPred inp (counterValues v) ys)
      (EmitPred inp (counterValues (counterProgramEval p v)) ys) (counterProgramTime p v) := by
  induction p generalizing v with
  | nil =>
    simpa only [counterProgramMachine, counterProgramEval, counterProgramTime] using
      (skipTM_hoareTime inp (counterValues v) ys hinp (counterValues_parked v)).mono_bound (by omega)
  | cons i is ih =>
    have hi := i.machine_hoareTime v inp ys hinp
    have ht := ih (i.eval v)
    have hall := seqTM_hoareTime i.machine (counterProgramMachine is) hi
      (emitPred_transition hinp (counterValues_parked (i.eval v)) ys) ht
    simpa only [counterProgramMachine, counterProgramEval, counterProgramTime] using hall

#print axioms CounterInstruction.machine_hoareTime
#print axioms counterProgramMachine_hoareTime

end DInstabilityComplexity.MachineConstruction
