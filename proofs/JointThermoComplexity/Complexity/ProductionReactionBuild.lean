module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionLoopEntry

set_option autoImplicit false
@[expose] public section

/-! Append final integer zero to the complete actual add/term stream, obtaining exact production-sum bytes. -/

namespace JointThermoComplexity.Complexity.ProductionReactionBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionReactionState ProductionFuelFrame CurrentTraversal

def machine (m : ℕ) : TM (m + 20) := seqTM (ProductionReactionLoop.machine m) (emitBitsTM ProductionSelectedTerm.zeroCode)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 4 + 52 * L ^ 3 + 150 * L ^ 2 + 165 * L + 8

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) (emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧
        State m input.length Q.speciesCount 0 s.val Q.speciesCount (List.ofFn mask) 0 R work ∧ IsReg Q.reactionCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (ProductionDenseCode.term Q s mask).code) inp work out ∧
        State m input.length Q.speciesCount Q.reactionCount s.val (Q.speciesCount + Q.reactionCount)
          (List.ofFn mask) Q.reactionCount R work ∧ IsReg Q.reactionCount (work (fuel m))) (timeBound input.length) := by
  have hl := ProductionReactionLoopEntry.hoareTime m input Q hd s mask emitted R hR
  have hz := FixedOutput.hoareTime ProductionSelectedTerm.zeroCode [] input
    (emitted ++ output (ProductionDenseCode.clauses Q s mask))
    (fun work => State m input.length Q.speciesCount Q.reactionCount s.val (Q.speciesCount + Q.reactionCount)
      (List.ofFn mask) Q.reactionCount R work ∧ IsReg Q.reactionCount (work (fuel m)))
  have hs := seqTM_hoareTime (ProductionReactionLoop.machine m) (emitBitsTM ProductionSelectedTerm.zeroCode) hl (by
    rintro inp work out ⟨hc, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp.1.safe, hp, hr⟩) hz
  have hzero : ProductionSelectedTerm.zeroCode.length = 5 := rfl
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, _, hp, hr⟩
    exact ⟨by simpa only [List.append_assoc, ProductionDenseCode.output_eq] using hc, hp, hr⟩) (by
      unfold timeBound ProductionReactionLoopEntry.timeBound
      rw [hzero])

end JointThermoComplexity.Complexity.ProductionReactionBuild

#print axioms JointThermoComplexity.Complexity.ProductionReactionBuild.hoareTime
