module
public import proofs.JointThermoComplexity.Complexity.MotifCompleteFrame

set_option autoImplicit false
@[expose] public section

/-! Reusable core entry has an actual species-zero register and an arbitrary natural core position, including the final count. -/

namespace JointThermoComplexity.Complexity.MotifCoreState
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState

def State (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (ci : ℕ)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) : Prop :=
  MotifPreparedMasks.Ready (m + 7) input Q work ∧
    ∃ ri, OuterProductionResources.Held m input.length Q.speciesCount ri 0 ci work ∧ R work

theorem map_state (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (ci : ℕ)
    (R S : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape)
    (hr : R work → S work) (hp : State m input Q ci R work) : State m input Q ci S work := by
  obtain ⟨hready, ri, hdata, hR⟩ := hp
  exact ⟨hready, ri, hdata, hr hR⟩

theorem of_reset (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape)
    (hs : ∀ j, Parked (work j)) (hdata : ProductionOperandData.Data (m + 2) input.length Q.speciesCount 0 0 work)
    (hi : IsReg Q.speciesCount (work (ProductionPorts.current (m + 2))))
    (hz : BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 9))))
    (hm : Stored (MotifMaskData.species (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 0)))
    (hr : Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 1)))
    (hf : ProductionSpeciesState.Fixed m input Q a R work) : State m input Q a.val R work := by
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  obtain ⟨hk, hraw, hflags, hcore, hR⟩ := hf
  have hsm := hm.reusable (L := input.length) (by rw [MotifMaskData.species_length]; omega)
  have hrm := hr.reusable (L := input.length) (by rw [MotifMaskData.reactions_length]; omega)
  have hfm := hflags.reusable (L := input.length) (by rw [BoxTraversalData.forward_length]; omega)
  exact ⟨⟨hs, hz, hi, ⟨hsm, hrm, hfm, hdata.magnitudeReusable⟩,
    ⟨hk, hraw, 0, by omega, hdata.reactionPosition⟩, hflags⟩,
    0, ⟨hdata, by omega, hcore⟩, hR⟩

theorem of_fresh (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape)
    (hp : OuterFuelFreshEntry.Advanced m input work) (hr : R work) :
    State m input Q 0 R work ∧ OuterFuelRegisters.State m Q.speciesCount Q.coreCount work := by
  obtain ⟨hready, ri, hdata, hfuel⟩ := OuterProductionResources.of_fresh m input Q hd work hp
  exact ⟨⟨hready, ri, hdata, hr⟩, hfuel⟩

end JointThermoComplexity.Complexity.MotifCoreState

#print axioms JointThermoComplexity.Complexity.MotifCoreState.of_reset
#print axioms JointThermoComplexity.Complexity.MotifCoreState.of_fresh
