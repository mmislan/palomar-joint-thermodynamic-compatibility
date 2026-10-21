module
public import proofs.JointThermoComplexity.Complexity.MotifCoreBuild

set_option autoImplicit false
@[expose] public section

/-! From any original-input cursor, rewind once and emit the complete exact supplied-core formula in polynomial time. -/

namespace JointThermoComplexity.Complexity.MotifCoreBlock
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifCoreState MotifCoreFuelFrame

def machine (m : ℕ) : TM (m + 22) := seqTM rewindInputTM (MotifCoreBuild.machine m)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 6 + 52 * L ^ 5 + 184 * L ^ 4 + 252 * L ^ 3 + 192 * L ^ 2 + 118 * L + 10

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) (hsplit : before ++ remaining = input) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q 0 R work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧ IsReg Q.coreCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (MotifCoreDenseCode.formula Q).code) inp work out ∧
        State m input Q Q.coreCount R work ∧ IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧
        IsReg Q.coreCount (work (fuel m))) (timeBound input.length) := by
  let P : (Fin (m + 22) → Tape) → Prop := fun work => State m input Q 0 R work ∧
    IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧ IsReg Q.coreCount (work (fuel m))
  have hr := InputRewind.hoareTime before remaining emitted P
  have hb := MotifCoreBuild.hoareTime m input Q hd emitted R hR
  have hs := seqTM_hoareTime rewindInputTM (MotifCoreBuild.machine m) hr (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [hsplit] using hc, hp⟩) hb
  have hlength := congrArg List.length hsplit
  simp only [List.length_append] at hlength
  exact hs.mono_bound (by unfold timeBound MotifCoreBuild.timeBound; omega)

end JointThermoComplexity.Complexity.MotifCoreBlock

#print axioms JointThermoComplexity.Complexity.MotifCoreBlock.hoareTime
