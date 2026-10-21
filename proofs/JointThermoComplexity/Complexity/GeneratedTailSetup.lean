module
public import proofs.JointThermoComplexity.Complexity.GeneratedTailFrame

set_option autoImplicit false
@[expose] public section

/-! Concrete scale, circle and error sections, each with its actual address loads. -/

namespace JointThermoComplexity.Complexity.GeneratedTailSetup
open _root_.Complexity _root_.Complexity.TM
open GeneratedTailFrame StrictGeneratedTemplates

def m (L : ℕ) : ℕ := SourcePolynomialSchedules.scaleLength L
def k (L : ℕ) : ℕ := SourcePolynomialSchedules.thresholdLength L
def C (L n : ℕ) : ℕ := n + m L + 1
def D (L n : ℕ) : ℕ := C L n * 2
def J (L n : ℕ) : ℕ := D L n + k L
def W (L n : ℕ) : ℕ := J L n + 2
def initialValues (L n : ℕ) : Fin 2 → ℕ := ![J L n, 0]
def scaleValues (n : ℕ) : Fin 2 → ℕ := ![n, n + 1]
def afterScale (L n : ℕ) : Fin 2 → ℕ := ![n + m L, n + m L + 1]
def circleValues : Fin 2 → ℕ := ![0, 0]
def afterCircle (L n : ℕ) : Fin 2 → ℕ := ![C L n, C L n]
def errorValues (L n : ℕ) : Fin 2 → ℕ := ![D L n, D L n + 1]
def finalValues (L n : ℕ) : Fin 2 → ℕ := ![J L n, J L n + 1]

theorem pair_bound (a count bound : ℕ) (h : a + 1 + count ≤ bound) :
    ∀ j : Fin 2, ![a, a + 1] j + count ≤ bound := by
  intro j
  fin_cases j
  · change a + count ≤ bound
    omega
  · exact h

theorem scale_bound (L n : ℕ) : ∀ j, scaleValues n j + m L ≤ W L n := by
  apply pair_bound
  dsimp only [W, J, D, C]
  omega

theorem circle_bound (L n : ℕ) : ∀ j, circleValues j + C L n ≤ W L n := by
  intro j
  fin_cases j <;> change 0 + C L n ≤ W L n <;> dsimp only [W, J, D] <;> omega

theorem error_bound (L n : ℕ) : ∀ j, errorValues L n j + k L ≤ W L n := by
  apply pair_bound
  dsimp only [W, J]
  omega

theorem pair_valuesAt (a b count : ℕ) : GeneratedEnergyLoop.valuesAt ![a, b] count = ![a + count, b + count] := by
  funext j
  fin_cases j <;> rfl

theorem chain_valuesAt (a count : ℕ) :
    GeneratedEnergyLoop.valuesAt ![a, a + 1] count = ![a + count, a + count + 1] := by
  rw [pair_valuesAt]
  have h : a + 1 + count = a + count + 1 := by omega
  rw [h]

theorem scale_after (L n : ℕ) : GeneratedEnergyLoop.valuesAt (scaleValues n) (m L) = afterScale L n :=
  chain_valuesAt n (m L)
theorem circle_after (L n : ℕ) : GeneratedEnergyLoop.valuesAt circleValues (C L n) = afterCircle L n := by
  simpa only [circleValues, afterCircle, Nat.zero_add] using pair_valuesAt 0 0 (C L n)
theorem error_after (L n : ℕ) : GeneratedEnergyLoop.valuesAt (errorValues L n) (k L) = finalValues L n :=
  chain_valuesAt (D L n) (k L)

theorem section_hoareTime (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ)
    (source : Fin 16) (h14 : source ≠ 14) (h15 : source ≠ 15) (bound : ℕ)
    (hW : ∀ j, values j + countValue L n s source ≤ bound) (initial edge : Kind)
    (before input emitted : List Bool) :
    (GeneratedLoopFramed.sectionMachine ports (StrictScheduleEntry.ports.index source) initial edge).HoareTime
      (Logical L n s original values before input emitted)
      (Logical L n s original (GeneratedEnergyLoop.valuesAt values (countValue L n s source)) before input
        ((emitted ++ RowSquareCanonical.entries (data values initial)) ++
          GeneratedEnergyLoop.entries values edge (countValue L n s source)))
      (GeneratedLoopFramed.sectionTime bound (countValue L n s source) initial edge) := by
  have h := GeneratedLoopFramed.section_hoareTime ports (StrictScheduleEntry.ports.index source)
    (counter_separate source) values bound (countValue L n s source) hW initial edge before input emitted
    (Keep L n s original) (keep_stable L n s original)
  exact h.consequence (by
    rintro inp work out ⟨hc, hr⟩
    exact ⟨⟨hc, hr⟩, hr.extra.1 source h14 h15⟩) (fun _ _ _ h => h.1) le_rfl

theorem loop_hoareTime (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ)
    (source : Fin 16) (h14 : source ≠ 14) (h15 : source ≠ 15) (bound : ℕ)
    (hW : ∀ j, values j + countValue L n s source ≤ bound) (kind : Kind)
    (before input emitted : List Bool) :
    (GeneratedEnergyLoop.machine ports (StrictScheduleEntry.ports.index source) kind).HoareTime
      (Logical L n s original values before input emitted)
      (Logical L n s original (GeneratedEnergyLoop.valuesAt values (countValue L n s source)) before input
        (emitted ++ GeneratedEnergyLoop.entries values kind (countValue L n s source)))
      (GeneratedEnergyLoop.timeBound bound (countValue L n s source) kind) := by
  have h := GeneratedLoopFramed.hoareTime ports (StrictScheduleEntry.ports.index source)
    (counter_separate source) values bound (countValue L n s source) hW kind before input emitted
    (Keep L n s original) (keep_stable L n s original)
  exact h.consequence (by
    rintro inp work out ⟨hc, hr⟩
    exact ⟨⟨hc, hr⟩, hr.extra.1 source h14 h15⟩) (fun _ _ _ h => h.1) le_rfl

def scaleWord (L n : ℕ) : List Bool := RowSquareCanonical.entries (data (scaleValues n) .scaleInitial) ++
  GeneratedEnergyLoop.entries (scaleValues n) .scaleEdge (m L)
def circleWord (L n : ℕ) : List Bool := GeneratedEnergyLoop.entries circleValues .circle (C L n)
def errorWord (L n : ℕ) : List Bool := RowSquareCanonical.entries (data (errorValues L n) .errorInitial) ++
  GeneratedEnergyLoop.entries (errorValues L n) .errorEdge (k L)

def scaleMachine : TM 64 := seqTM (pairMachine 1 11) (GeneratedLoopFramed.sectionMachine ports 31 .scaleInitial .scaleEdge)
def circleMachine : TM 64 := seqTM (pairMachine 13 13) (GeneratedEnergyLoop.machine ports 35 .circle)
def errorMachine : TM 64 := seqTM (pairMachine 8 12) (GeneratedLoopFramed.sectionMachine ports 32 .errorInitial .errorEdge)

def scaleTime (L n s : ℕ) (values : Fin 2 → ℕ) : ℕ := pairTime L n s values 1 11 + 1 +
  GeneratedLoopFramed.sectionTime (W L n) (m L) .scaleInitial .scaleEdge
def circleTime (L n s : ℕ) (values : Fin 2 → ℕ) : ℕ := pairTime L n s values 13 13 + 1 +
  GeneratedEnergyLoop.timeBound (W L n) (C L n) .circle
def errorTime (L n s : ℕ) (values : Fin 2 → ℕ) : ℕ := pairTime L n s values 8 12 + 1 +
  GeneratedLoopFramed.sectionTime (W L n) (k L) .errorInitial .errorEdge

theorem scale_hoareTime (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ) (before input emitted : List Bool) :
    scaleMachine.HoareTime (Logical L n s original values before input emitted)
      (Logical L n s original (afterScale L n) before input (emitted ++ scaleWord L n)) (scaleTime L n s values) := by
  have hi := pair_hoareTime L n s original values 1 11 (by decide) (by decide) (by decide) (by decide) before input emitted
  have he := section_hoareTime L n s original (scaleValues n) 2 (by decide) (by decide) (W L n)
    (scale_bound L n) .scaleInitial .scaleEdge before input emitted
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hr⟩) he
  have hm : countValue L n s 2 = m L := rfl
  have hp : StrictScheduleEntry.ports.index 2 = (31 : Fin 64) := rfl
  simpa only [scaleMachine, scaleTime, scaleWord, hm, hp, scale_after, List.append_assoc] using hseq

theorem circle_hoareTime (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ) (before input emitted : List Bool) :
    circleMachine.HoareTime (Logical L n s original values before input emitted)
      (Logical L n s original (afterCircle L n) before input (emitted ++ circleWord L n)) (circleTime L n s values) := by
  have hi := pair_hoareTime L n s original values 13 13 (by decide) (by decide) (by decide) (by decide) before input emitted
  have he := loop_hoareTime L n s original circleValues 7 (by decide) (by decide) (W L n)
    (circle_bound L n) .circle before input emitted
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hr⟩) he
  have hc : countValue L n s 7 = C L n := rfl
  have hp : StrictScheduleEntry.ports.index 7 = (35 : Fin 64) := rfl
  simpa only [circleMachine, circleTime, circleWord, hc, hp, circle_after] using hseq

theorem error_hoareTime (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ) (before input emitted : List Bool) :
    errorMachine.HoareTime (Logical L n s original values before input emitted)
      (Logical L n s original (finalValues L n) before input (emitted ++ errorWord L n)) (errorTime L n s values) := by
  have hi := pair_hoareTime L n s original values 8 12 (by decide) (by decide) (by decide) (by decide) before input emitted
  have he := section_hoareTime L n s original (errorValues L n) 3 (by decide) (by decide) (W L n)
    (error_bound L n) .errorInitial .errorEdge before input emitted
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hr⟩) he
  have hk : countValue L n s 3 = k L := rfl
  have hp : StrictScheduleEntry.ports.index 3 = (32 : Fin 64) := rfl
  simpa only [errorMachine, errorTime, errorWord, hk, hp, error_after, List.append_assoc] using hseq

end JointThermoComplexity.Complexity.GeneratedTailSetup

#print axioms JointThermoComplexity.Complexity.GeneratedTailSetup.scale_hoareTime
#print axioms JointThermoComplexity.Complexity.GeneratedTailSetup.circle_hoareTime
#print axioms JointThermoComplexity.Complexity.GeneratedTailSetup.error_hoareTime
