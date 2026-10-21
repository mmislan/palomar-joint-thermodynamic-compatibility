module
public import proofs.JointThermoComplexity.Complexity.CounterInputEntry
public import proofs.DInstabilityComplexity.CounterProgramBounds
public import proofs.DInstabilityComplexity.UnaryCodeEmitter
public import proofs.Complexitylib.Classes.P.Defs

set_option autoImplicit false
@[expose] public section

/-! All fixed arithmetic counter programs run in FP from initial binary tapes.
The selected register is emitted in unary. This supports polynomially bounded
addresses and loop counts; it is not yet a source-formula construction theorem. -/

namespace JointThermoComplexity.Complexity.BoundedCounters
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction
open Polynomial
variable {n : ℕ}

def output (p : CounterProgram n) (qin qout : Fin n) (input : List Bool) : List Bool :=
  List.replicate (counterProgramEval p (initialValues qin input.length) qout) true ++ [false]

def machine (p : CounterProgram n) (qin qout : Fin n) : TM n :=
  seqTM (entry qin) (seqTM (counterProgramMachine p) (emitUnaryCodeTM qout))

def timeBound (k L : ℕ) : ℕ := (2 * L + 6) + 1 + counterIterTime k L + 1 + (4 * counterIterBound k L + 4)

noncomputable def timePolynomial (k : ℕ) : Polynomial ℕ :=
  (2 * X + 6) + 1 + counterTimePolynomial k + 1 + (4 * counterBoundPolynomial k + 4)

theorem timePolynomial_eval (k L : ℕ) : (timePolynomial k).eval L = timeBound k L := by
  simp [timePolynomial, timeBound, counterTimePolynomial_eval, counterBoundPolynomial_eval]

theorem machine_computesInTime (p : CounterProgram n) (qin qout : Fin n) :
    (machine p qin qout).ComputesInTime (output p qin qout) (timeBound p.length) := by
  intro input
  let inp : Tape := ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩
  let v0 := initialValues qin input.length
  let v1 := counterProgramEval p v0
  have hinp := parked_init_input input
  have hs := counterProgramMachine_hoareTime p v0 inp [] hinp
  have he := emitUnaryCodeTM_hoareTime qout (v1 qout) inp (counterValues v1) [] hinp (counterValues_parked v1) rfl
  have hse := seqTM_hoareTime (counterProgramMachine p) (emitUnaryCodeTM qout) hs
    (emitPred_transition hinp (counterValues_parked v1) []) he
  have hi := entry_hoareTime qin input
  have hall := seqTM_hoareTime (entry qin) (seqTM (counterProgramMachine p) (emitUnaryCodeTM qout)) hi
    (emitPred_transition hinp (counterValues_parked v0) []) hse
  obtain ⟨c, t, ht, hr, hh, hpost⟩ := hall (Tape.init (input.map Γ.ofBool))
    (fun _ => Tape.init []) (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  have htime := counterProgramTime_bound p v0 input.length (initialValues_le qin input.length)
  have hvalue := counterProgramEval_bound p v0 input.length (initialValues_le qin input.length) qout
  change v1 qout ≤ counterIterBound p.length input.length at hvalue
  refine ⟨c, t, ?_, hr, hh, ?_⟩
  · unfold timeBound
    omega
  · simpa only [output, List.nil_append, v0, v1] using hpost.2.2.hasOutput

theorem output_mem_FP (p : CounterProgram n) (qin qout : Fin n) : output p qin qout ∈ FP := by
  let P := timePolynomial p.length
  refine ⟨P.natDegree, n, machine p qin qout, timeBound p.length, machine_computesInTime p qin qout, ?_⟩
  exact BigO.of_polynomial_bound P (fun L => by rw [timePolynomial_eval])

end JointThermoComplexity.Complexity.BoundedCounters

#print axioms JointThermoComplexity.Complexity.BoundedCounters.machine_computesInTime
#print axioms JointThermoComplexity.Complexity.BoundedCounters.output_mem_FP
