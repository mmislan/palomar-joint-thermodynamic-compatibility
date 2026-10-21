module
public import proofs.JointThermoComplexity.Complexity.MotifCoreLoopEntry

set_option autoImplicit false
@[expose] public section

/-! Final truth closes the complete exact supplied-core allFin block, including zero cores. -/

namespace JointThermoComplexity.Complexity.MotifCoreBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifCoreState MotifCoreFuelFrame CurrentTraversal

def machine (m : ℕ) : TM (m + 22) := seqTM (MotifCoreLoop.machine m) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := 4 * L ^ 6 + 52 * L ^ 5 + 184 * L ^ 4 + 252 * L ^ 3 + 192 * L ^ 2 + 117 * L + 6

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q 0 R work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧ IsReg Q.coreCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (MotifCoreDenseCode.formula Q).code) inp work out ∧
        State m input Q Q.coreCount R work ∧ IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧
        IsReg Q.coreCount (work (fuel m))) (timeBound input.length) := by
  have hl := MotifCoreLoopEntry.hoareTime m input Q hd emitted R hR
  have hz := FixedOutput.hoareTime [false, false, false] [] input
    (emitted ++ output (MotifCoreDenseCode.clauses Q))
    (fun work => State m input Q Q.coreCount R work ∧ IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧
      IsReg Q.coreCount (work (fuel m)))
  have hs := seqTM_hoareTime (MotifCoreLoop.machine m) (emitBitsTM [false, false, false]) hl (by
    rintro inp work out ⟨hc, hp, hspecies, hcore⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp.1.1, hp, hspecies, hcore⟩) hz
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, _, hp, hspecies, hcore⟩
    exact ⟨by simpa only [List.append_assoc, MotifCoreDenseCode.output_eq] using hc, hp, hspecies, hcore⟩) (by
      unfold timeBound MotifCoreLoopEntry.timeBound
      simp only [List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.MotifCoreBuild

#print axioms JointThermoComplexity.Complexity.MotifCoreBuild.hoareTime
