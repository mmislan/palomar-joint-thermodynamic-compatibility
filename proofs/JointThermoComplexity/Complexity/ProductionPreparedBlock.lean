module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesBlock

set_option autoImplicit false
@[expose] public section

/-! Prepared actual motif directions and retained reusable data supply the complete species production block. -/

namespace JointThermoComplexity.Complexity.ProductionPreparedBlock
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState ProductionSpeciesFuelFrame

theorem entry_of_directions (m ri : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape)
    (hdir : MotifDecodedDirections.Ready (m + 7) input Q a (Q.speciesCount + Q.reactionCount) work)
    (hp : OuterProductionResources.Held m input.length Q.speciesCount ri 0 a.val work) (hr : R work) :
    ProductionSpeciesMaskInit.StoredState m input Q a R work := by
  have hdata := OuterPreparedProduction.production_state m ri 0 input Q a work hdir hp
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  obtain ⟨⟨_, hz, hi, _, hmeta, hspecies⟩, hreact, hforward⟩ := hdir
  exact ⟨ri, hp.reactionBound, Q.speciesCount + Q.reactionCount, by omega,
    hdata, hi, hz, hspecies, hreact, hmeta.1, hmeta.2.1, hforward, hp.corePosition, hr⟩

abbrev machine (m : ℕ) : TM (m + 22) := ProductionSpeciesBlock.machine m

theorem hoareTime (m ri : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        MotifDecodedDirections.Ready (m + 7) input Q a (Q.speciesCount + Q.reactionCount) work ∧
        OuterProductionResources.Held m input.length Q.speciesCount ri 0 a.val work ∧ R work ∧
        IsReg Q.speciesCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (ProductionSpeciesDenseCode.formula Q a).code) inp work out ∧
        State m input Q a Q.speciesCount R work ∧ IsReg Q.speciesCount (work (fuel m)) ∧
        BoxBufferState.Stored (MotifMaskData.species (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 0)))
      (ProductionSpeciesBlock.timeBound input.length) := by
  have hs := ProductionSpeciesBlock.hoareTime m input Q hd a before remaining emitted hsplit R hR
  exact hs.consequence (by
    rintro inp work out ⟨hc, hdir, hp, hr, hfuel⟩
    exact ⟨hc, entry_of_directions m ri input Q hd a R work hdir hp hr, hfuel⟩) (fun _ _ _ h => h) le_rfl

end JointThermoComplexity.Complexity.ProductionPreparedBlock

#print axioms JointThermoComplexity.Complexity.ProductionPreparedBlock.entry_of_directions
#print axioms JointThermoComplexity.Complexity.ProductionPreparedBlock.hoareTime
