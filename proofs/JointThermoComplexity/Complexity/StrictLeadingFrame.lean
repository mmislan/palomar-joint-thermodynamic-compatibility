module
public import proofs.JointThermoComplexity.Complexity.StrictLeadingInitialization

set_option autoImplicit false
@[expose] public section

/-! Total blank-input prefix execution and its saved frame for the original-row traversal. -/

namespace JointThermoComplexity.Complexity.StrictLeadingFrame
open _root_.Complexity _root_.Complexity.TM
open StrictInitialComposition (arity scratch)
open StrictLeadingInitialization
open StrictRowInitialization (rowPorts state)

theorem extra_stable (L n s : ℕ) (original : List Bool) :
    RowEnergyStep.Stable rowPorts (StrictLeadingInitialization.Extra L n s original) := by
  rintro work next he ⟨hc, h42, h43, hh, hv, hb⟩
  have kept (j : Fin 64) (hj : 30 ≤ j.val) : next j = work j :=
    he j (StrictInitialComposition.high_outside j hj).1 (StrictInitialComposition.high_outside j hj).2
  exact ⟨fun i hi hf => by
      simpa only [he _ (StrictInitialComposition.counter_outside i hi hf).1
        (StrictInitialComposition.counter_outside i hi hf).2] using hc i hi hf,
    by simpa only [kept 42 (by decide)] using h42,
    by simpa only [kept 43 (by decide)] using h43,
    by simpa only [kept 62 (by decide)] using hh,
    by simpa only [kept 62 (by decide)] using hv,
    by simpa only [kept 63 (by decide)] using hb⟩

theorem extra_fuel_stable (L n s : ℕ) (original : List Bool) :
    RowEnergyLoop.FuelStable (29 : Fin 64) (StrictLeadingInitialization.Extra L n s original) := by
  rintro work next he ⟨hc, h42, h43, hh, hv, hb⟩
  have hcounter : ∀ i : Fin 16, i ≠ 15 → StrictScheduleEntry.ports.index i ≠ 29 := fun i hi =>
    StrictScheduleEntry.ports.injective.ne hi
  exact ⟨fun i hi hf => by simpa only [he _ (hcounter i hf)] using hc i hi hf,
    by simpa only [he 42 (by decide)] using h42,
    by simpa only [he 43 (by decide)] using h43,
    by simpa only [he 62 (by decide)] using hh,
    by simpa only [he 62 (by decide)] using hv,
    by simpa only [he 63 (by decide)] using hb⟩

noncomputable def thresholdPolynomial : Polynomial ℕ :=
  57600 * Polynomial.X ^ 4 + 518880 * Polynomial.X ^ 3 + 1291320 * Polynomial.X ^ 2 +
    552897 * Polynomial.X + 65106
noncomputable def leadPolynomial : Polynomial ℕ :=
  (Polynomial.X + StrictInitialComposition.scalePolynomial + 1) * 2 + thresholdPolynomial

theorem leadPolynomial_eval (L : ℕ) : leadPolynomial.eval L = leadAddress L L := by
  simp [leadPolynomial, thresholdPolynomial, StrictInitialComposition.scalePolynomial_eval,
    leadAddress, SourcePolynomialSchedules.thresholdLength]

theorem lead_mono (L n : ℕ) (hn : n ≤ L) : leadAddress L n ≤ leadAddress L L := by
  dsimp only [leadAddress]
  omega

theorem leading_time_mono (L n W : ℕ) (hn : n ≤ L) (boxed : Bool) :
    StrictLeadingInitialization.timeBound L n W boxed ≤ StrictLeadingInitialization.timeBound L L W boxed := by
  have hJ := lead_mono L n hn
  dsimp only [StrictLeadingInitialization.timeBound, binder]
  gcongr

def word (boxed : Bool) (input : List Bool) : List Bool :=
  SparseListCodec.unaryCode (binder input.length (arity input)) ++
    RowSquareCanonical.entries (StrictGeneratedTemplates.data (rawValues input.length (arity input)) (kind boxed))

def rowState (boxed : Bool) (input : List Bool) : RowEnergyControl.State :=
  state (HeaderControl.copied input) (HeaderControl.suffix input) (word boxed input)

def machine (boxed : Bool) : TM 64 := seqTM StrictInitialComposition.machine (StrictLeadingInitialization.machine boxed)

def timeBound (L : ℕ) (boxed : Bool) : ℕ := StrictInitialComposition.timeBound L + 1 +
  StrictLeadingInitialization.timeBound L L (leadAddress L L + 1) boxed

noncomputable def timePolynomial (boxed : Bool) : Polynomial ℕ :=
  StrictInitialComposition.timePolynomial + 1 +
    ((4 * (leadPolynomial + 1) + 4) + 1 +
      (leadPolynomial * (2 * leadPolynomial + 6) + (leadPolynomial + 2) + 1 +
        (StrictGeneratedBytes.timePolynomial (kind boxed)).comp (leadPolynomial + 1)))

theorem timePolynomial_eval (L : ℕ) (boxed : Bool) : (timePolynomial boxed).eval L = timeBound L boxed := by
  simp [timePolynomial, timeBound, StrictInitialComposition.timePolynomial_eval,
    leadPolynomial_eval, StrictGeneratedBytes.timePolynomial_eval,
    StrictLeadingInitialization.timeBound, binder]

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (StrictScheduleEntry.Initial input)
      (Framed input.length (arity input) (HeaderControl.copied input) (HeaderControl.suffix input)
        (word boxed input) (StrictLeadingInitialization.Extra input.length (arity input) (scratch input) input))
      (timeBound input.length boxed) := by
  have hJ : (leadAddress input.length (arity input)).bits.length ≤ leadAddress input.length input.length + 1 :=
    (BinaryIncrementControl.bits_length_le _).trans
      (Nat.le_trans (lead_mono _ _ (HeaderControl.count_le_length input)) (Nat.le_succ _))
  have hi := StrictInitialComposition.hoareTime input
  have hl := StrictLeadingInitialization.hoareTime input.length (arity input) (scratch input)
    (leadAddress input.length input.length + 1) hJ boxed input
    (HeaderControl.copied input) (HeaderControl.suffix input) []
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨⟨hc, hr⟩, hf⟩) hl
  apply hseq.consequence (fun _ _ _ h => h)
  · intro inp work out h
    simpa only [word, List.nil_append] using h
  · have ht := leading_time_mono input.length (arity input)
      (leadAddress input.length input.length + 1) (HeaderControl.count_le_length input) boxed
    unfold timeBound
    omega

end JointThermoComplexity.Complexity.StrictLeadingFrame

#print axioms JointThermoComplexity.Complexity.StrictLeadingFrame.extra_stable
#print axioms JointThermoComplexity.Complexity.StrictLeadingFrame.extra_fuel_stable
#print axioms JointThermoComplexity.Complexity.StrictLeadingFrame.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.StrictLeadingFrame.hoareTime
