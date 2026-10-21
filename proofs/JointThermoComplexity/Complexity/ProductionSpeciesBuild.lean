module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesLoopEntry

set_option autoImplicit false
@[expose] public section

/-! Final truth closes the exact production allFin stream, including the empty species domain. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState ProductionSpeciesFuelFrame CurrentTraversal

def machine (m : ℕ) : TM (m + 22) := seqTM (ProductionSpeciesLoop.machine m) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := 4 * L ^ 5 + 52 * L ^ 4 + 150 * L ^ 3 + 184 * L ^ 2 + 65 * L + 6

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a 0 R work ∧ IsReg Q.speciesCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (ProductionSpeciesDenseCode.formula Q a).code) inp work out ∧
        State m input Q a Q.speciesCount R work ∧ IsReg Q.speciesCount (work (fuel m))) (timeBound input.length) := by
  have hl := ProductionSpeciesLoopEntry.hoareTime m input Q hd a emitted R hR
  have hz := FixedOutput.hoareTime [false, false, false] [] input
    (emitted ++ output (ProductionSpeciesDenseCode.clauses Q a))
    (fun work => State m input Q a Q.speciesCount R work ∧ IsReg Q.speciesCount (work (fuel m)))
  have hs := seqTM_hoareTime (ProductionSpeciesLoop.machine m) (emitBitsTM [false, false, false]) hl (by
    rintro inp work out ⟨hc, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, safe m input Q a Q.speciesCount R work hp, hp, hr⟩) hz
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, _, hp, hr⟩
    exact ⟨by simpa only [List.append_assoc, ProductionSpeciesDenseCode.output_eq] using hc, hp, hr⟩) (by
      unfold timeBound ProductionSpeciesLoopEntry.timeBound
      simp only [List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.ProductionSpeciesBuild

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesBuild.hoareTime
