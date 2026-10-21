module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionState

set_option autoImplicit false
@[expose] public section

/-! Advance the actual reaction-mask head by one cell while preserving the production arithmetic and indices. -/

namespace JointThermoComplexity.Complexity.ProductionMaskAdvance
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts ProductionReactionState

def ports (m : ℕ) : List (Fin (m + 20)) := [MotifBufferPorts.buffer (m + 5) 1]

def machine (m : ℕ) : TM (m + 20) := WorkHeadsAdvance.machine (ports m)

theorem advance_state (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work')
    (work : Fin (m + 20) → Tape) (hp : State m L n ri si idx mask k R work) :
    State m L n ri si idx mask (k + 1) R (WorkHeadsAdvance.advance (ports m) work) := by
  let work' := WorkHeadsAdvance.advance (ports m) work
  have hw (j : Fin (m + 20)) (hj : j ≠ MotifBufferPorts.buffer (m + 5) 1) : work' j = work j := by
    simp only [work', WorkHeadsAdvance.advance, ports, List.mem_singleton, hj, ↓reduceIte]
  have hx (j : Fin (m + 20)) (hj : j.val ≠ 3) : work' j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hs := WorkHeadsAdvance.parked (ports m) work hp.1.safe
  have hstate : ProductionOperandLoad.State m L n ri si work' :=
    ⟨hs, by simpa only [hx (left m) (by change (9 : ℕ) ≠ 3; omega)] using hp.1.productReusable,
      by simpa only [hx (right m) (by change (10 : ℕ) ≠ 3; omega)] using hp.1.reactantReusable,
      by simpa only [hx (magnitude m) (by change (8 : ℕ) ≠ 3; omega)] using hp.1.magnitudeReusable,
      by simpa only [hx (sign m) (by change (11 : ℕ) ≠ 3; omega)] using hp.1.signHead,
      by simpa only [hx (species m) (by change (12 : ℕ) ≠ 3; omega)] using hp.1.speciesPosition,
      by simpa only [hx (count m) (by change m + 15 ≠ 3; omega)] using hp.1.speciesCount,
      by simpa only [hx (reaction m) (by change (6 : ℕ) ≠ 3; omega)] using hp.1.reactionPosition⟩
  have hmask : MotifDirectionState.At mask (k + 1) (work' (MotifBufferPorts.buffer (m + 5) 1)) := by
    simpa only [work', WorkHeadsAdvance.advance, ports, List.mem_singleton, ↓reduceIte] using hp.2.2.2.1.advance
  exact ⟨hstate, by
      change IsReg idx (work' (current m))
      rw [hx (current m) (by change (7 : ℕ) ≠ 3; omega)]
      exact hp.2.1,
    by
      change BinaryIncrementRun.Register 0 (work' (PowerPorts.scratch (m + 7)))
      rw [hx (PowerPorts.scratch (m + 7)) (by change (5 : ℕ) ≠ 3; omega)]
      exact hp.2.2.1,
    hmask, hR work work' (of_mask m work work' hw) hp.2.2.2.2⟩

theorem hoareTime (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (before remaining emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n ri si idx mask k R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m L n ri si idx mask (k + 1) R work) 1 := by
  have hs := WorkHeadsAdvance.hoareTime (ports m) before remaining emitted
    (fun work _ => State m L n ri si idx mask k R work) (fun work _ => State m L n ri si idx mask (k + 1) R work)
    (fun work _ hp => advance_state m L n ri si idx mask k R hR work hp)
  exact hs.consequence (fun _ _ _ ⟨hc, hp⟩ => ⟨hc, hp.1.safe, hp⟩) (fun _ _ _ ⟨hc, _, hp⟩ => ⟨hc, hp⟩) le_rfl

end JointThermoComplexity.Complexity.ProductionMaskAdvance

#print axioms JointThermoComplexity.Complexity.ProductionMaskAdvance.advance_state
#print axioms JointThermoComplexity.Complexity.ProductionMaskAdvance.hoareTime
