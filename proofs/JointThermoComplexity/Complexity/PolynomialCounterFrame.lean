module
public import proofs.JointThermoComplexity.Complexity.CounterProgramFrame
public import proofs.JointThermoComplexity.Complexity.PolynomialCounterPrograms

set_option autoImplicit false
@[expose] public section

/-! Fixed polynomial schedules computed in selected unary registers, with an
actual polynomial step bound and an arbitrary surrounding binary/flag frame. -/

namespace JointThermoComplexity.Complexity.PolynomialCounterFrame
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction
open HeaderAt (Cursor)
open CounterProgramFrame (Ports Logical Stable)
variable {w : ℕ}

def machine (ports : Ports 3 w) (cs : List ℕ) : TM w :=
  CounterProgramFrame.machine ports (PolynomialCounters.program cs)

def timeBound (cs : List ℕ) (B : ℕ) : ℕ :=
  counterIterTime (PolynomialCounters.program cs).length B

noncomputable def timePolynomial (cs : List ℕ) : Polynomial ℕ :=
  counterTimePolynomial (PolynomialCounters.program cs).length

theorem timePolynomial_eval (cs : List ℕ) (B : ℕ) :
    (timePolynomial cs).eval B = timeBound cs B :=
  counterTimePolynomial_eval _ _

def Result (ports : Ports 3 w) (L value : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    IsReg L (work (ports.index 0)) ∧ IsReg value (work (ports.index 1)) ∧
    (∃ scratch, IsReg scratch (work (ports.index 2))) ∧ R work

theorem exact_hoareTime (ports : Ports 3 w) (cs : List ℕ) (v : Fin 3 → ℕ)
    (B : ℕ) (hv : ∀ j, v j ≤ B) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable ports R) :
    (machine ports cs).HoareTime (Logical ports v before input emitted R)
      (Logical ports (counterProgramEval (PolynomialCounters.program cs) v) before input emitted R)
      (timeBound cs B) :=
  CounterProgramFrame.bounded_hoareTime ports (PolynomialCounters.program cs)
    v B hv before input emitted R hR

theorem hoareTime (ports : Ports 3 w) (cs : List ℕ) (v : Fin 3 → ℕ)
    (B : ℕ) (hv : ∀ j, v j ≤ B) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable ports R) :
    (machine ports cs).HoareTime (Logical ports v before input emitted R)
      (Result ports (v 0) (PolynomialCounters.value cs (v 0)) before input emitted R)
      (timeBound cs B) := by
  apply (exact_hoareTime ports cs v B hv before input emitted R hR).strengthen_post
  rintro inp work out ⟨hc, hs, hr, hx⟩
  have he := PolynomialCounters.program_eval cs v
  exact ⟨hc, hs, by simpa only [he.1] using hr 0, by simpa only [he.2] using hr 1,
    ⟨_, hr 2⟩, hx⟩

theorem polynomial_bound (ports : Ports 3 w) (cs : List ℕ) (v : Fin 3 → ℕ)
    (B : ℕ) (hv : ∀ j, v j ≤ B) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable ports R) :
    (machine ports cs).HoareTime (Logical ports v before input emitted R)
      (Result ports (v 0) (PolynomialCounters.value cs (v 0)) before input emitted R)
      ((timePolynomial cs).eval B) := by
  rw [timePolynomial_eval]
  exact hoareTime ports cs v B hv before input emitted R hR

end JointThermoComplexity.Complexity.PolynomialCounterFrame

#print axioms JointThermoComplexity.Complexity.PolynomialCounterFrame.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.PolynomialCounterFrame.hoareTime
#print axioms JointThermoComplexity.Complexity.PolynomialCounterFrame.polynomial_bound
