module
public import proofs.JointThermoComplexity.Complexity.StrictRowInitialization

set_option autoImplicit false
@[expose] public section

/-! Actual blank-input preparation of the complete row invariant, with a total
polynomial time bound and the saved counter frame needed by later sections. -/

namespace JointThermoComplexity.Complexity.StrictInitialComposition
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction StrictRowInitialization

def arity (input : List Bool) : ℕ := HeaderControl.count input
def scratch (input : List Bool) : ℕ := counterProgramEval StrictScheduleProgram.core
  (StrictScheduleProgram.initialValues input.length (arity input)) 4
def initialState (input : List Bool) : RowEnergyControl.State :=
  state (HeaderControl.copied input) (HeaderControl.suffix input) []
def sharedScale (input : List Bool) : ℕ := arity input + SourcePolynomialSchedules.scaleLength input.length

def machine : TM 64 := seqTM StrictScheduleEntry.machine StrictRowInitialization.machine
def timeBound (L : ℕ) : ℕ := StrictScheduleEntry.timeBound L + 1 + StrictRowInitialization.timeBound L L

noncomputable def scalePolynomial : Polynomial ℕ := 60 * Polynomial.X ^ 2 + 265 * Polynomial.X + 58
noncomputable def sharedPolynomial : Polynomial ℕ := Polynomial.X + scalePolynomial
noncomputable def timePolynomial : Polynomial ℕ := StrictScheduleEntry.timePolynomial + 1 +
  sharedPolynomial * (2 * sharedPolynomial + 6) + sharedPolynomial + 31

theorem scalePolynomial_eval (L : ℕ) : scalePolynomial.eval L = SourcePolynomialSchedules.scaleLength L := by
  simp [scalePolynomial, SourcePolynomialSchedules.scaleLength]

theorem timePolynomial_eval (L : ℕ) : timePolynomial.eval L = timeBound L := by
  simp [timePolynomial, sharedPolynomial, scalePolynomial_eval, timeBound,
    StrictScheduleEntry.timePolynomial_eval, StrictRowInitialization.timeBound]
  omega

theorem row_time_mono (L n : ℕ) (hn : n ≤ L) :
    StrictRowInitialization.timeBound L n ≤ StrictRowInitialization.timeBound L L := by
  dsimp only [StrictRowInitialization.timeBound]
  gcongr

theorem counter_outside : ∀ i : Fin 16, i ≠ 14 → i ≠ 15 →
    StrictScheduleEntry.ports.index i ≠ rowPorts.active ∧
      ∀ a, StrictScheduleEntry.ports.index i ≠ rowPorts.square.index a := by decide

theorem high_outside (j : Fin 64) (hj : 30 ≤ j.val) :
    j ≠ rowPorts.active ∧ ∀ a, j ≠ rowPorts.square.index a := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    change j.val = 28 at hv
    omega
  · intro a he
    have hv := congrArg Fin.val he
    change j.val = a.val at hv
    omega

theorem extra_stable (L n scratch : ℕ) (original : List Bool) :
    RowEnergyStep.Stable rowPorts (Extra L n scratch original) := by
  rintro work next he ⟨hc, h42, h43, hh, hv, hb⟩
  have kept (j : Fin 64) (hj : 30 ≤ j.val) : next j = work j :=
    he j (high_outside j hj).1 (high_outside j hj).2
  exact ⟨fun i hi hf => by
      simpa only [he _ (counter_outside i hi hf).1 (counter_outside i hi hf).2] using hc i hi hf,
    by simpa only [kept 42 (by decide)] using h42,
    by simpa only [kept 43 (by decide)] using h43,
    by simpa only [kept 62 (by decide)] using hh,
    by simpa only [kept 62 (by decide)] using hv,
    by simpa only [kept 63 (by decide)] using hb⟩

theorem extra_fuel_stable (L n scratch : ℕ) (original : List Bool) :
    RowEnergyLoop.FuelStable (29 : Fin 64) (Extra L n scratch original) := by
  rintro work next he ⟨hc, h42, h43, hh, hv, hb⟩
  have hcounter : ∀ i : Fin 16, i ≠ 15 → StrictScheduleEntry.ports.index i ≠ 29 := fun i hi =>
    StrictScheduleEntry.ports.injective.ne hi
  exact ⟨fun i hi hf => by simpa only [he _ (hcounter i hf)] using hc i hi hf,
    by simpa only [he 42 (by decide)] using h42,
    by simpa only [he 43 (by decide)] using h43,
    by simpa only [he 62 (by decide)] using hh,
    by simpa only [he 62 (by decide)] using hv,
    by simpa only [he 63 (by decide)] using hb⟩

theorem hoareTime (input : List Bool) :
    machine.HoareTime (StrictScheduleEntry.Initial input)
      (fun inp work out => RowEnergyStep.Logical rowPorts (initialState input) (sharedScale input).bits
        (input.length + 2) (width input.length (arity input))
        (Extra input.length (arity input) (scratch input) input) inp work out ∧
        IsReg (input.length + 2) (work 29)) (timeBound input.length) := by
  have hs := StrictScheduleEntry.hoareTime input
  have hr := StrictRowInitialization.hoareTime input.length (arity input) (scratch input) input
    (HeaderControl.copied input) (HeaderControl.suffix input) []
  have hseq := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨hc, hs, hv, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hv, hx⟩) hr
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hready⟩
    have hrow := row_ready input.length (arity input) (scratch input) input
      (HeaderControl.copied input) (HeaderControl.suffix input) [] work hready
    exact ⟨⟨hc, hrow.1⟩, hrow.2⟩
  · have ht := row_time_mono input.length (arity input) (HeaderControl.count_le_length input)
    unfold timeBound
    omega

end JointThermoComplexity.Complexity.StrictInitialComposition

#print axioms JointThermoComplexity.Complexity.StrictInitialComposition.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.StrictInitialComposition.extra_stable
#print axioms JointThermoComplexity.Complexity.StrictInitialComposition.extra_fuel_stable
#print axioms JointThermoComplexity.Complexity.StrictInitialComposition.hoareTime
