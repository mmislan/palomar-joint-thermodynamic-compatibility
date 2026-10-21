module
public import proofs.JointThermoComplexity.Complexity.GeneratedTailSetup
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! The complete actual generated tail, in scale/circle/error order, followed by one terminator. -/

namespace JointThermoComplexity.Complexity.StrictGeneratedTail
open _root_.Complexity _root_.Complexity.TM
open GeneratedTailFrame GeneratedTailSetup

def word (L n : ℕ) : List Bool := scaleWord L n ++ circleWord L n ++ errorWord L n ++ [false]

def machine : TM 64 := seqTM scaleMachine (seqTM circleMachine (seqTM errorMachine (emitBitsTM [false])))

def timeBound (L n s : ℕ) : ℕ := scaleTime L n s (initialValues L n) + 1 +
  (circleTime L n s (afterScale L n) + 1 + (errorTime L n s (afterCircle L n) + 1 + 1))

theorem hoareTime (L n s : ℕ) (original before input emitted : List Bool) :
    machine.HoareTime (Logical L n s original (initialValues L n) before input emitted)
      (Logical L n s original (finalValues L n) before input (emitted ++ word L n)) (timeBound L n s) := by
  have hs := scale_hoareTime L n s original (initialValues L n) before input emitted
  have hc := circle_hoareTime L n s original (afterScale L n) before input (emitted ++ scaleWord L n)
  have he := error_hoareTime L n s original (afterCircle L n) before input
    ((emitted ++ scaleWord L n) ++ circleWord L n)
  have hf := FixedOutput.hoareTime [false] before input
    (((emitted ++ scaleWord L n) ++ circleWord L n) ++ errorWord L n)
    (GeneratedEnergyStep.Ready ports (finalValues L n) (Keep L n s original))
  have hf' : (emitBitsTM (n := 64) [false]).HoareTime
      (Logical L n s original (finalValues L n) before input
        (((emitted ++ scaleWord L n) ++ circleWord L n) ++ errorWord L n))
      (Logical L n s original (finalValues L n) before input
        ((((emitted ++ scaleWord L n) ++ circleWord L n) ++ errorWord L n) ++ [false])) 1 :=
    hf.consequence (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.safe, hr⟩)
      (fun _ _ _ ⟨hc, _, hr⟩ => ⟨hc, hr⟩) le_rfl
  have hef := seqTM_hoareTime _ _ he (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hf'
  have hcef := seqTM_hoareTime _ _ hc (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hef
  have hall := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hcef
  simpa only [machine, timeBound, word, List.append_assoc] using hall

end JointThermoComplexity.Complexity.StrictGeneratedTail

#print axioms JointThermoComplexity.Complexity.StrictGeneratedTail.hoareTime
