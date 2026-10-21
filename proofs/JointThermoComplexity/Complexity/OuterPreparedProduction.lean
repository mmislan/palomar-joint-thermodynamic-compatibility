module
public import proofs.JointThermoComplexity.Complexity.OuterProductionResources
public import proofs.JointThermoComplexity.Complexity.MotifMaskDirectionsFrame

set_option autoImplicit false
@[expose] public section

/-! Prepared exact motif directions retain reusable arithmetic/core data and arbitrary stable outer resources. -/

namespace JointThermoComplexity.Complexity.OuterPreparedProduction
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt OuterProductionResources

theorem hoareTime (m ri si : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifPassFrame.Unchanged (m + 7) work work' → R work → R work') :
    (MotifMaskDirections.machine (m + 7)).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail)
        emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        Held m input.length Q.speciesCount ri si a.val work ∧ R work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail
        (emitted ++ (MotifDecodedDirections.formula Q a).code) inp work out ∧
        MotifDecodedDirections.Ready (m + 7) input Q a (Q.speciesCount + Q.reactionCount) work ∧
        Held m input.length Q.speciesCount ri si a.val work ∧ R work) (MotifMaskDirections.timeBound input.length) := by
  let S : (Fin (m + 22) → Tape) → Prop := fun work => Held m input.length Q.speciesCount ri si a.val work ∧ R work
  have hS : ∀ work work', MotifPassFrame.Unchanged (m + 7) work work' → S work → S work' := by
    rintro work work' hw ⟨hp, hr⟩
    exact ⟨motif_frame m input.length Q.speciesCount ri si a.val work work' hw hp, hR work work' hw hr⟩
  exact MotifMaskDirectionsFrame.hoareTime (m + 7) input Q hd a before tail emitted S hS

theorem initialized_hoareTime (m ri si : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) :
    (MotifMaskDirections.machine (m + 7)).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail)
        emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        WithFuel m input.length Q.speciesCount ri si a.val Q.coreCount work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail
        (emitted ++ (MotifDecodedDirections.formula Q a).code) inp work out ∧
        MotifDecodedDirections.Ready (m + 7) input Q a (Q.speciesCount + Q.reactionCount) work ∧
        WithFuel m input.length Q.speciesCount ri si a.val Q.coreCount work) (MotifMaskDirections.timeBound input.length) :=
  hoareTime m ri si input Q hd a before tail emitted (OuterFuelRegisters.State m Q.speciesCount Q.coreCount)
    (OuterFuelRegisters.motif_frame m Q.speciesCount Q.coreCount)

theorem production_state (m ri si : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (work : Fin (m + 22) → Tape) (hdir : MotifDecodedDirections.Ready (m + 7) input Q a (Q.speciesCount + Q.reactionCount) work)
    (hp : Held m input.length Q.speciesCount ri si a.val work) :
    ProductionOperandLoad.State (m + 2) input.length Q.speciesCount ri si work :=
  to_state m input.length Q.speciesCount ri si a.val work hdir.1.1 hp

end JointThermoComplexity.Complexity.OuterPreparedProduction

#print axioms JointThermoComplexity.Complexity.OuterPreparedProduction.hoareTime
#print axioms JointThermoComplexity.Complexity.OuterPreparedProduction.initialized_hoareTime
#print axioms JointThermoComplexity.Complexity.OuterPreparedProduction.production_state
