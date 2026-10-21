module
public import proofs.DInstabilityComplexity.CounterProgramSyntax

set_option autoImplicit false
@[expose] public section

/-! Injective placement of actual unary instructions amongst arbitrary parked work tapes. -/

namespace JointThermoComplexity.Complexity.CounterPlacement
open _root_.Complexity
open _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction

variable {n w : ℕ}

def destination : CounterInstruction n → Fin n
  | .increment r | .clear r => r
  | .copy _ r _ | .add _ r _ | .mulAdd _ _ r _ _ _ => r

def result : CounterInstruction n → (Fin n → ℕ) → ℕ
  | .increment r, v => v r + 1
  | .clear _, _ => 0
  | .copy src _ _, v => v src
  | .add src dst _, v => v dst + v src
  | .mulAdd a b dst _ _ _, v => v dst + v a * v b

theorem eval_eq (i : CounterInstruction n) (v : Fin n → ℕ) :
    i.eval v = Function.update v (destination i) (result i v) := by
  cases i <;> rfl

def instruction (ports : Fin n → Fin w) (hinj : Function.Injective ports) :
    CounterInstruction n → CounterInstruction w
  | .increment r => .increment (ports r)
  | .clear r => .clear (ports r)
  | .copy src dst h => .copy (ports src) (ports dst) (fun he => h (hinj he))
  | .add src dst h => .add (ports src) (ports dst) (fun he => h (hinj he))
  | .mulAdd a b dst hab had hbd => .mulAdd (ports a) (ports b) (ports dst)
      (fun he => hab (hinj he)) (fun he => had (hinj he)) (fun he => hbd (hinj he))

def updated (ports : Fin n → Fin w) (i : CounterInstruction n) (v : Fin n → ℕ)
    (work : Fin w → Tape) : Fin w → Tape :=
  Function.update work (ports (destination i)) (regTape (result i v))

theorem registers_updated (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (i : CounterInstruction n) (v : Fin n → ℕ) (work : Fin w → Tape)
    (hreg : ∀ j, IsReg (v j) (work (ports j))) :
    ∀ j, IsReg (i.eval v j) (updated ports i v work (ports j)) := by
  intro j
  rw [eval_eq]
  by_cases hj : j = destination i
  · subst j
    simp only [updated, Function.update_self]
    exact reg_regT _
  · have hp : ports j ≠ ports (destination i) := fun he => hj (hinj he)
    simpa only [updated, Function.update_of_ne hj, Function.update_of_ne hp] using hreg j

theorem parked_updated (ports : Fin n → Fin w) (i : CounterInstruction n)
    (v : Fin n → ℕ) (work : Fin w → Tape) (hsafe : ∀ j, Parked (work j)) :
    ∀ j, Parked (updated ports i v work j) := by
  intro j
  by_cases hj : j = ports (destination i)
  · subst j
    simp only [updated, Function.update_self]
    exact parked_regTape _
  · simpa only [updated, Function.update_of_ne hj] using hsafe j

theorem other_updated (ports : Fin n → Fin w) (i : CounterInstruction n)
    (v : Fin n → ℕ) (work : Fin w → Tape) (j : Fin w)
    (hj : ∀ k, j ≠ ports k) : updated ports i v work j = work j :=
  Function.update_of_ne (hj (destination i)) _ _

theorem hoareTime (ports : Fin n → Fin w) (hinj : Function.Injective ports)
    (i : CounterInstruction n) (v : Fin n → ℕ) (inp : Tape)
    (work : Fin w → Tape) (emitted : List Bool) (hinp : Parked inp)
    (hsafe : ∀ j, Parked (work j)) (hreg : ∀ j, IsReg (v j) (work (ports j))) :
    (instruction ports hinj i).machine.HoareTime (EmitPred inp work emitted)
      (EmitPred inp (updated ports i v work) emitted) (i.time v) := by
  have heq : ∀ j, work (ports j) = regTape (v j) := fun j => (hreg j).eq_regT
  cases i with
  | increment r =>
    exact incRegTM_hoareTime (ports r) (v r) inp work emitted hinp
      (fun j _ => hsafe j) (heq r)
  | clear r =>
    exact clearRegTM_hoareTime (ports r) (v r) inp work emitted hinp
      (fun j _ => hsafe j) (heq r)
  | copy src dst h =>
    exact copyIntoTM_hoareTime (ports src) (ports dst) (fun he => h (hinj he))
      (v src) (v dst) inp work emitted hinp (fun j _ => hsafe j) (heq src) (heq dst)
  | add src dst h =>
    exact addIntoTM_hoareTime (ports src) (ports dst) (fun he => h (hinj he))
      (v src) (v dst) inp work emitted hinp (fun j _ => hsafe j) (heq src) (heq dst)
  | mulAdd a b dst hab had hbd =>
    exact mulAddIntoTM_hoareTime (ports a) (ports b) (ports dst)
      (fun he => hab (hinj he)) (fun he => had (hinj he)) (fun he => hbd (hinj he))
      (v a) (v b) (v dst) inp work emitted hinp (fun j _ => hsafe j) (heq a) (heq b) (heq dst)

end JointThermoComplexity.Complexity.CounterPlacement

#print axioms JointThermoComplexity.Complexity.CounterPlacement.registers_updated
#print axioms JointThermoComplexity.Complexity.CounterPlacement.hoareTime
