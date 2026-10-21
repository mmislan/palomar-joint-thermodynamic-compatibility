module
public import proofs.JointThermoComplexity.Complexity.StrictGeneratedTail
public import proofs.JointThermoComplexity.Complexity.StrictLeadingFrame
public import proofs.Complexitylib.Asymptotics

set_option autoImplicit false
@[expose] public section

/-! An actual polynomial bound for all address loads and generated-tail loops. -/

namespace JointThermoComplexity.Complexity.GeneratedTailTime
open _root_.Complexity _root_.Complexity.TM
open GeneratedTailFrame GeneratedTailSetup StrictGeneratedTemplates

theorem basic_bounds (L n : ℕ) : n + 1 ≤ W L n ∧ m L ≤ W L n ∧ C L n ≤ W L n ∧
    k L ≤ W L n ∧ D L n + 1 ≤ W L n := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [W, J, D, C] <;> omega

theorem pair_le (a b bound : ℕ) (ha : a ≤ bound) (hb : b ≤ bound) : ∀ j : Fin 2, ![a, b] j ≤ bound := by
  intro j
  fin_cases j
  · exact ha
  · exact hb

theorem initial_bound (L n : ℕ) : ∀ j, initialValues L n j ≤ W L n :=
  pair_le _ _ _ (by dsimp only [W]; omega) (Nat.zero_le _)

theorem after_scale_bound (L n : ℕ) : ∀ j, afterScale L n j ≤ W L n := by
  have hc := (basic_bounds L n).2.2.1
  exact pair_le _ _ _ (by dsimp only [C] at hc; omega) hc

theorem after_circle_bound (L n : ℕ) : ∀ j, afterCircle L n j ≤ W L n :=
  pair_le _ _ _ (basic_bounds L n).2.2.1 (basic_bounds L n).2.2.1

theorem pair_time_bound (L n s bound : ℕ) (values : Fin 2 → ℕ) (a b : Fin 16)
    (hv : ∀ j, values j ≤ bound) (ha : countValue L n s a ≤ bound) (hb : countValue L n s b ≤ bound) :
    pairTime L n s values a b ≤ 2 * BinaryAddressLoad.boundedTime bound + 1 := by
  have h0 := BinaryAddressLoad.timeBound_le (values 0) (countValue L n s a) bound
    ((BinaryIncrementControl.bits_length_le _).trans (hv 0)) ha
  have h1 := BinaryAddressLoad.timeBound_le (values 1) (countValue L n s b) bound
    ((BinaryIncrementControl.bits_length_le _).trans (hv 1)) hb
  dsimp only [pairTime]
  omega

theorem loop_count_mono (bound a b : ℕ) (h : a ≤ b) (kind : Kind) :
    GeneratedEnergyLoop.timeBound bound a kind ≤ GeneratedEnergyLoop.timeBound bound b kind := by
  dsimp only [GeneratedEnergyLoop.timeBound]
  gcongr

theorem section_count_mono (bound a b : ℕ) (h : a ≤ b) (initial edge : Kind) :
    GeneratedLoopFramed.sectionTime bound a initial edge ≤ GeneratedLoopFramed.sectionTime bound b initial edge := by
  have ht := loop_count_mono bound a b h edge
  dsimp only [GeneratedLoopFramed.sectionTime]
  omega

def budget (bound : ℕ) : ℕ :=
  (2 * BinaryAddressLoad.boundedTime bound + 2 + GeneratedLoopFramed.sectionTime bound bound .scaleInitial .scaleEdge) + 1 +
  ((2 * BinaryAddressLoad.boundedTime bound + 2 + GeneratedEnergyLoop.timeBound bound bound .circle) + 1 +
  ((2 * BinaryAddressLoad.boundedTime bound + 2 + GeneratedLoopFramed.sectionTime bound bound .errorInitial .errorEdge) + 1 + 1))

theorem tail_bound (L n s : ℕ) : StrictGeneratedTail.timeBound L n s ≤ budget (W L n) := by
  have hb := basic_bounds L n
  have hpScale := pair_time_bound L n s (W L n) (initialValues L n) 1 11 (initial_bound L n)
    (by change n ≤ W L n; omega) hb.1
  have hpCircle := pair_time_bound L n s (W L n) (afterScale L n) 13 13 (after_scale_bound L n)
    (Nat.zero_le _) (Nat.zero_le _)
  have hpError := pair_time_bound L n s (W L n) (afterCircle L n) 8 12 (after_circle_bound L n)
    (by change D L n ≤ W L n; omega) hb.2.2.2.2
  have hs := section_count_mono (W L n) (m L) (W L n) hb.2.1 .scaleInitial .scaleEdge
  have hc := loop_count_mono (W L n) (C L n) (W L n) hb.2.2.1 .circle
  have he := section_count_mono (W L n) (k L) (W L n) hb.2.2.2.1 .errorInitial .errorEdge
  dsimp only [StrictGeneratedTail.timeBound, scaleTime, circleTime, errorTime, budget]
  omega

noncomputable def loadPolynomial : Polynomial ℕ :=
  (3 * Polynomial.X + 9) + 1 + (Polynomial.X * (2 * Polynomial.X + 6) + (Polynomial.X + 2))
noncomputable def loopPolynomial (kind : Kind) : Polynomial ℕ :=
  Polynomial.X * (StrictGeneratedBytes.timePolynomial kind + 4 * Polynomial.X + 12) + (Polynomial.X + 2)
noncomputable def sectionPolynomial (initial edge : Kind) : Polynomial ℕ :=
  StrictGeneratedBytes.timePolynomial initial + 1 + loopPolynomial edge
noncomputable def budgetPolynomial : Polynomial ℕ :=
  (2 * loadPolynomial + 2 + sectionPolynomial .scaleInitial .scaleEdge) + 1 +
  ((2 * loadPolynomial + 2 + loopPolynomial .circle) + 1 +
  ((2 * loadPolynomial + 2 + sectionPolynomial .errorInitial .errorEdge) + 1 + 1))

theorem loadPolynomial_eval (bound : ℕ) : loadPolynomial.eval bound = BinaryAddressLoad.boundedTime bound := by
  simp [loadPolynomial, BinaryAddressLoad.boundedTime]

theorem loopPolynomial_eval (bound : ℕ) (kind : Kind) :
    (loopPolynomial kind).eval bound = GeneratedEnergyLoop.timeBound bound bound kind := by
  simp [loopPolynomial, StrictGeneratedBytes.timePolynomial_eval, GeneratedEnergyLoop.timeBound,
    GeneratedEnergyStep.timeBound]

theorem sectionPolynomial_eval (bound : ℕ) (initial edge : Kind) :
    (sectionPolynomial initial edge).eval bound = GeneratedLoopFramed.sectionTime bound bound initial edge := by
  simp [sectionPolynomial, StrictGeneratedBytes.timePolynomial_eval, loopPolynomial_eval, GeneratedLoopFramed.sectionTime]

theorem budgetPolynomial_eval (bound : ℕ) : budgetPolynomial.eval bound = budget bound := by
  simp [budgetPolynomial, budget, loadPolynomial_eval, loopPolynomial_eval, sectionPolynomial_eval]

noncomputable def timePolynomial : Polynomial ℕ := budgetPolynomial.comp (StrictLeadingFrame.leadPolynomial + 2)

theorem timePolynomial_eval (L : ℕ) : timePolynomial.eval L = budget (W L L) := by
  simp only [timePolynomial, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_ofNat,
    StrictLeadingFrame.leadPolynomial_eval, budgetPolynomial_eval]
  rfl

theorem runtime_bound (L n s : ℕ) (hn : n ≤ L) :
    StrictGeneratedTail.timeBound L n s ≤ timePolynomial.eval L := by
  have hw : W L n ≤ W L L := by
    dsimp only [W, J, D, C]
    omega
  calc
    StrictGeneratedTail.timeBound L n s ≤ budget (W L n) := tail_bound L n s
    _ ≤ budget (W L L) := by
      rw [← budgetPolynomial_eval, ← budgetPolynomial_eval]
      exact polynomial_eval_mono_nat budgetPolynomial hw
    _ = timePolynomial.eval L := (timePolynomial_eval L).symm

end JointThermoComplexity.Complexity.GeneratedTailTime

#print axioms JointThermoComplexity.Complexity.GeneratedTailTime.tail_bound
#print axioms JointThermoComplexity.Complexity.GeneratedTailTime.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.GeneratedTailTime.runtime_bound
