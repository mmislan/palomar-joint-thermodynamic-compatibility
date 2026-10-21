module
public import proofs.JointThermoComplexity.Complexity.BoxRegisters
public import proofs.JointThermoComplexity.Complexity.CurrentResources
public import proofs.JointThermoComplexity.Complexity.CurrentReady

set_option autoImplicit false
@[expose] public section

/-! The post-positivity state seeds bounded binary buffers and retains raw/previous resources for motif emission. -/

namespace JointThermoComplexity.Complexity.BoxSeed
open _root_.Complexity
open _root_.Complexity.TM
open PowerPorts MonomialPorts ReactionPorts CurrentPorts BoxState BoxBufferState

theorem of_current (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 15) → Tape)
    (h : CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) Q.speciesCount Q.speciesCount
      (CurrentResources.State m input) work) :
    Ready m input.length Q.speciesCount (fun work => CurrentPins.Kept m input work ∧ BoxRegisters.State m input work) work := by
  rcases h with ⟨hs, hz, hraw, hi, hprev, _, hmeta, ⟨hn, ⟨a, p, ha, hp, har, hpr⟩, ⟨keep, hkeep, hk⟩⟩⟩
  have hbuf : Buffers m input.length work :=
    ⟨of_register (ArityValue.arity_bound input) hn, of_register ha har, of_register hp hpr, of_register hkeep hk⟩
  have hr : BoxRegisters.State m input work := by
    refine ⟨?_, hprev⟩
    rw [ArityValue.on_decode hd]
    exact hraw
  exact ⟨hs, hz, hi, hbuf, hmeta, hr⟩

end JointThermoComplexity.Complexity.BoxSeed

#print axioms JointThermoComplexity.Complexity.BoxSeed.of_current
