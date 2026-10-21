module
public import proofs.JointThermoComplexity.Complexity.CurrentPins
public import proofs.JointThermoComplexity.Complexity.NetworkEmitReady

set_option autoImplicit false
@[expose] public section

/-! Preserve the already bounded reusable circuit registers for later constraint emission. -/

namespace JointThermoComplexity.Complexity.CurrentResources
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady ReactionPorts CurrentPorts

def Held (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  IsReg (ArityValue.arity input) (work (next (m + 2))) ∧ Temps (m + 1) input.length work ∧
    (∃ keep, keep ≤ 4 * input.length ∧ IsReg keep (work (saved m)))

def State (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  CurrentPins.Kept m input work ∧ Held m input work

theorem held_frame (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) → work' j = work j) :
    Held m input work → Held m input work' := by
  have hx : ∀ j : Fin (m + 15), j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 8 → work' j = work j := by
    intro j hj
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = m + 14 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  rintro ⟨hn, ⟨a, p, ha, hp, har, hpr⟩, ⟨keep, hkeep, hk⟩⟩
  exact ⟨by simpa only [hx (next (m + 2)) (Or.inl rfl)] using hn,
    ⟨a, p, ha, hp, by simpa only [hx (accumulator (m + 2)) (Or.inr (Or.inl rfl))] using har,
      by simpa only [hx (power (m + 2)) (Or.inr (Or.inr (Or.inl rfl)))] using hpr⟩,
    ⟨keep, hkeep, by simpa only [hx (saved m) (Or.inr (Or.inr (Or.inr rfl)))] using hk⟩⟩

theorem frame (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) → work' j = work j) :
    State m input work → State m input work' := by
  rintro ⟨hp, hr⟩
  exact ⟨CurrentPins.frame m input work work' hw hp, held_frame m input work work' hw hr⟩

theorem of_network_ready (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 15) → Tape)
    (h : NetworkEmitReady.Ready m input.length (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network)
      Q.speciesCount (NetworkPins.Kept m input) work) : State m input work := by
  rcases h with ⟨_, _, hn, ht, _, hk, _, _, hp⟩
  refine ⟨CurrentPins.of_network m input work hp, ?_, ht, hk⟩
  rw [ArityValue.on_decode hd]
  exact hn

end JointThermoComplexity.Complexity.CurrentResources

#print axioms JointThermoComplexity.Complexity.CurrentResources.frame
