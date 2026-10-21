module
public import proofs.JointThermoComplexity.Complexity.CounterRenaming
public import proofs.JointThermoComplexity.Complexity.PolynomialCounterFrame
public import proofs.JointThermoComplexity.Complexity.SourcePolynomialSchedules

set_option autoImplicit false
@[expose] public section

/-! One fixed actual counter program computes every count needed before strict
serialization. Only raw input length and the bounded unary arity are inputs. -/

namespace JointThermoComplexity.Complexity.StrictScheduleProgram
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction SourcePolynomialSchedules

def scaleCoefficients : List ℕ := [58, 265, 60]
def thresholdCoefficients : List ℕ := [65106, 552897, 1291320, 518880, 57600]
def scalePorts : Fin 3 → Fin 16 := ![0, 2, 4]
def thresholdPorts : Fin 3 → Fin 16 := ![0, 3, 4]
theorem scale_injective : Function.Injective scalePorts := by decide
theorem threshold_injective : Function.Injective thresholdPorts := by decide

def scaleProgram : CounterProgram 16 :=
  CounterRenaming.program scalePorts scale_injective (PolynomialCounters.program scaleCoefficients)
def thresholdProgram : CounterProgram 16 :=
  CounterRenaming.program thresholdPorts threshold_injective (PolynomialCounters.program thresholdCoefficients)

theorem scale_value (L : ℕ) : PolynomialCounters.value scaleCoefficients L = scaleLength L := by
  simp only [scaleCoefficients, PolynomialCounters.value, scaleLength]
  ring
theorem threshold_value (L : ℕ) : PolynomialCounters.value thresholdCoefficients L = thresholdLength L := by
  simp only [thresholdCoefficients, PolynomialCounters.value, thresholdLength]
  ring

theorem horner_values (ports : Fin 3 → Fin 16) (hinj : Function.Injective ports)
    (cs : List ℕ) (v : Fin 16 → ℕ) :
    counterProgramEval (CounterRenaming.program ports hinj (PolynomialCounters.program cs)) v (ports 0) = v (ports 0) ∧
    counterProgramEval (CounterRenaming.program ports hinj (PolynomialCounters.program cs)) v (ports 1) =
      PolynomialCounters.value cs (v (ports 0)) := by
  have he := CounterRenaming.eval ports hinj (PolynomialCounters.program cs) v
  have hv := PolynomialCounters.program_eval cs (v ∘ ports)
  exact ⟨(congrFun he 0).trans hv.1, (congrFun he 1).trans hv.2⟩

def core : CounterProgram 16 := scaleProgram ++ thresholdProgram

theorem core_values (v : Fin 16 → ℕ) :
    counterProgramEval core v 0 = v 0 ∧ counterProgramEval core v 1 = v 1 ∧
    counterProgramEval core v 2 = scaleLength (v 0) ∧
    counterProgramEval core v 3 = thresholdLength (v 0) ∧
    counterProgramEval core v 13 = v 13 := by
  let vm := counterProgramEval scaleProgram v
  have hm := horner_values scalePorts scale_injective scaleCoefficients v
  have hk := horner_values thresholdPorts threshold_injective thresholdCoefficients vm
  have hmOutside (j : Fin 16) (hj : ∀ k, j ≠ scalePorts k) : vm j = v j :=
    CounterRenaming.outside scalePorts scale_injective (PolynomialCounters.program scaleCoefficients) v j hj
  have hkOutside (j : Fin 16) (hj : ∀ k, j ≠ thresholdPorts k) :
      counterProgramEval thresholdProgram vm j = vm j :=
    CounterRenaming.outside thresholdPorts threshold_injective (PolynomialCounters.program thresholdCoefficients) vm j hj
  rw [core, PolynomialCounters.eval_append]
  change counterProgramEval thresholdProgram vm 0 = _ ∧ counterProgramEval thresholdProgram vm 1 = _ ∧
    counterProgramEval thresholdProgram vm 2 = _ ∧ counterProgramEval thresholdProgram vm 3 = _ ∧
    counterProgramEval thresholdProgram vm 13 = _
  refine ⟨hk.1.trans hm.1, ?_, ?_, ?_, ?_⟩
  · exact (hkOutside 1 (by intro k; fin_cases k <;> decide)).trans
      (hmOutside 1 (by intro k; fin_cases k <;> decide))
  · exact (hkOutside 2 (by intro k; fin_cases k <;> decide)).trans (hm.2.trans (scale_value _))
  · exact hk.2.trans (by rw [threshold_value]; exact congrArg thresholdLength hm.1)
  · exact (hkOutside 13 (by intro k; fin_cases k <;> decide)).trans
      (hmOutside 13 (by intro k; fin_cases k <;> decide))

def counts : CounterProgram 16 :=
  [.copy 0 5 (by decide), .increment 5, .increment 5,
   .copy 1 6 (by decide), .add 2 6 (by decide),
   .copy 6 7 (by decide), .increment 7,
   .copy 7 8 (by decide), .add 7 8 (by decide),
   .copy 8 9 (by decide), .add 3 9 (by decide),
   .copy 9 10 (by decide), .increment 10,
   .copy 1 11 (by decide), .increment 11,
   .copy 8 12 (by decide), .increment 12,
   .copy 5 14 (by decide), .copy 5 15 (by decide)]

def assembled (v : Fin 16 → ℕ) : Fin 16 → ℕ :=
  ![v 0, v 1, v 2, v 3, v 4, v 0 + 2, v 1 + v 2, v 1 + v 2 + 1,
    (v 1 + v 2 + 1) * 2, (v 1 + v 2 + 1) * 2 + v 3,
    (v 1 + v 2 + 1) * 2 + v 3 + 1, v 1 + 1, (v 1 + v 2 + 1) * 2 + 1,
    v 13, v 0 + 2, v 0 + 2]

theorem counts_eval (v : Fin 16 → ℕ) : counterProgramEval counts v = assembled v := by
  funext j
  fin_cases j <;> norm_num [counts, counterProgramEval, CounterInstruction.eval,
    Function.update_apply, assembled] <;> omega

def initialValues (L n : ℕ) : Fin 16 → ℕ := fun j => if j = 0 then L else if j = 1 then n else 0

def values (L n scratch : ℕ) : Fin 16 → ℕ :=
  let m := scaleLength L
  let k := thresholdLength L
  ![L, n, m, k, scratch, L + 2, n + m, n + m + 1,
    (n + m + 1) * 2, (n + m + 1) * 2 + k, (n + m + 1) * 2 + k + 1,
    n + 1, (n + m + 1) * 2 + 1, 0, L + 2, L + 2]

def program : CounterProgram 16 := core ++ counts

theorem program_eval (L n : ℕ) :
    counterProgramEval program (initialValues L n) =
      values L n (counterProgramEval core (initialValues L n) 4) := by
  rw [program, PolynomialCounters.eval_append, counts_eval]
  have he := core_values (initialValues L n)
  rcases he with ⟨h0, h1, h2, h3, h13⟩
  simp only [initialValues, ↓reduceIte, Fin.isValue, Fin.reduceEq] at h0 h1 h2 h3 h13
  simp only [assembled, values, h0, h1, h2, h3, h13]

variable {w : ℕ}
def machine (ports : CounterProgramFrame.Ports 16 w) : TM w := CounterProgramFrame.machine ports program

theorem hoareTime (ports : CounterProgramFrame.Ports 16 w) (L n : ℕ) (hn : n ≤ L)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : CounterProgramFrame.Stable ports R) :
    (machine ports).HoareTime
      (CounterProgramFrame.Logical ports (initialValues L n) before input emitted R)
      (CounterProgramFrame.Logical ports (values L n (counterProgramEval core (initialValues L n) 4))
        before input emitted R) (counterIterTime program.length L) := by
  have hv : ∀ j, initialValues L n j ≤ L := by
    intro j
    unfold initialValues
    split
    · exact le_rfl
    · split
      · exact hn
      · exact Nat.zero_le _
  simpa only [machine, program_eval] using
    CounterProgramFrame.bounded_hoareTime ports program (initialValues L n) L hv before input emitted R hR

end JointThermoComplexity.Complexity.StrictScheduleProgram

#print axioms JointThermoComplexity.Complexity.StrictScheduleProgram.core_values
#print axioms JointThermoComplexity.Complexity.StrictScheduleProgram.program_eval
#print axioms JointThermoComplexity.Complexity.StrictScheduleProgram.hoareTime
