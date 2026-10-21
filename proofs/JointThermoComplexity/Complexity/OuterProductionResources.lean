module
public import proofs.JointThermoComplexity.Complexity.ProductionOperandData
public import proofs.JointThermoComplexity.Complexity.OuterFuelRegisters
public import proofs.JointThermoComplexity.Complexity.ProductionInitialState

set_option autoImplicit false
@[expose] public section

/-! Reusable arithmetic data, bounded reaction position and actual core index survive motif and outer-fuel frames. -/

namespace JointThermoComplexity.Complexity.OuterProductionResources
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

structure Held (m L n ri si ci : ℕ) (work : Fin (m + 22) → Tape) : Prop where
  data : ProductionOperandData.Data (m + 2) L n ri si work
  reactionBound : ri ≤ 4 * L
  corePosition : IsReg ci (work (ProductionPorts.core (m + 2)))

def WithFuel (m L n ri si ci c : ℕ) (work : Fin (m + 22) → Tape) : Prop :=
  Held m L n ri si ci work ∧ OuterFuelRegisters.State m n c work

theorem to_state (m L n ri si ci : ℕ) (work : Fin (m + 22) → Tape)
    (hs : ∀ j, Parked (work j)) (h : Held m L n ri si ci work) : ProductionOperandLoad.State (m + 2) L n ri si work :=
  ProductionOperandData.to_state (m + 2) L n ri si work hs h.data

theorem motif_frame (m L n ri si ci : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : MotifPassFrame.Unchanged (m + 7) work work') (h : Held m L n ri si ci work) : Held m L n ri si ci work' := by
  have hcore := MotifPassFrame.outside (m + 7) work work' hw (ProductionPorts.core (m + 2))
    (Or.inr (by change 8 ≤ (13 : ℕ); omega))
  exact ⟨ProductionOperandData.motif_frame (m + 2) L n ri si work work' hw h.data,
    h.reactionBound, by simpa only [hcore] using h.corePosition⟩

theorem with_fuel_frame (m L n ri si ci c : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : MotifPassFrame.Unchanged (m + 7) work work') : WithFuel m L n ri si ci c work → WithFuel m L n ri si ci c work' := by
  rintro ⟨hp, hf⟩
  exact ⟨motif_frame m L n ri si ci work work' hw hp, OuterFuelRegisters.motif_frame m n c work work' hw hf⟩

theorem outer_frame (m L n ri si ci : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : OuterFuelCopyFrame.Unchanged m work work') (h : Held m L n ri si ci work) : Held m L n ri si ci work' := by
  have hcore := OuterFuelCopyFrame.outside m work work' hw (ProductionPorts.core (m + 2))
    (Or.inl (by change (13 : ℕ) ≤ 13; omega))
  exact ⟨ProductionOperandData.outer_frame m L n ri si work work' hw h.data,
    h.reactionBound, by simpa only [hcore] using h.corePosition⟩

theorem of_fresh (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 22) → Tape) (h : OuterFuelFreshEntry.Advanced m input work) :
    MotifPreparedMasks.Ready (m + 7) input Q work ∧ ∃ ri, WithFuel m input.length Q.speciesCount ri 0 0 Q.coreCount work := by
  have h' : MotifPreparedMasks.Ready (m + 7) input Q work ∧ ProductionBank.State (m + 2) work ∧
      IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧ IsReg Q.coreCount (work (OuterFuelPorts.destination m 1)) := by
    simpa only [OuterFuelFreshEntry.Advanced, hd] using h
  obtain ⟨ri, hri, hp, hc⟩ := ProductionInitialState.of_prepared (m + 2) input Q hd work h'.1 h'.2.1
  exact ⟨h'.1, ri, ⟨ProductionOperandData.of_state (m + 2) input.length Q.speciesCount ri 0 work hp, hri, hc⟩, h'.2.2⟩

end JointThermoComplexity.Complexity.OuterProductionResources

#print axioms JointThermoComplexity.Complexity.OuterProductionResources.motif_frame
#print axioms JointThermoComplexity.Complexity.OuterProductionResources.outer_frame
#print axioms JointThermoComplexity.Complexity.OuterProductionResources.of_fresh
