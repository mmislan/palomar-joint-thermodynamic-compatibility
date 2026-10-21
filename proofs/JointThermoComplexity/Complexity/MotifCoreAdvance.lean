module
public import proofs.JointThermoComplexity.Complexity.MotifCoreState

set_option autoImplicit false
@[expose] public section

/-! The actual core-index successor retains prepared reusable state, including at the final natural count. -/

namespace JointThermoComplexity.Complexity.MotifCoreAdvance
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifCoreState

abbrev machine (m : ℕ) : TM (m + 22) := UnarySuccessor.machine (ProductionPorts.core (m + 2))

theorem hoareTime (m ci : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (before remaining emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q ci R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q (ci + 1) R work)
      (2 * ci + 6) := by
  rintro inp work out ⟨hc, hready, ri, hdata, hr⟩
  let P : (Fin (m + 22) → Tape) → Prop := fun work' => ∀ j, j ≠ ProductionPorts.core (m + 2) → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ ProductionPorts.core (m + 2) → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hs, hpos, hw⟩ :=
    UnarySuccessor.hoareTime (ProductionPorts.core (m + 2)) ci before remaining emitted P hP
      inp work out ⟨hc, hready.1, hdata.corePosition, fun _ _ => rfl⟩
  have hx (j : Fin (m + 22)) (hj : j.val ≠ 13) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hu := MotifCompleteFrame.of_single m (ProductionPorts.core (m + 2))
    (by change 2 ≤ (13 : ℕ) ∧ (13 : ℕ) ≤ 13; omega) work d.work hw
  have hcopy : ProductionOperandData.Data (m + 2) input.length Q.speciesCount ri 0 d.work :=
    ⟨by simpa only [hx (ProductionPorts.left (m + 2)) (by change (9 : ℕ) ≠ 13; omega)] using hdata.data.productReusable,
      by simpa only [hx (ProductionPorts.right (m + 2)) (by change (10 : ℕ) ≠ 13; omega)] using hdata.data.reactantReusable,
      by simpa only [hx (ProductionPorts.magnitude (m + 2)) (by change (8 : ℕ) ≠ 13; omega)] using hdata.data.magnitudeReusable,
      by simpa only [hx (ProductionPorts.sign (m + 2)) (by change (11 : ℕ) ≠ 13; omega)] using hdata.data.signHead,
      by simpa only [hx (ProductionPorts.species (m + 2)) (by change (12 : ℕ) ≠ 13; omega)] using hdata.data.speciesPosition,
      by simpa only [hx (ProductionPorts.count (m + 2)) (by change m + 17 ≠ 13; omega)] using hdata.data.speciesCount,
      by simpa only [hx (ProductionPorts.reaction (m + 2)) (by change (6 : ℕ) ≠ 13; omega)] using hdata.data.reactionPosition⟩
  obtain ⟨_, hz, hi, ⟨h0, h1, h2, h8⟩, ⟨hk, hraw, old, hold, hprev⟩, hflags⟩ := hready
  have hready' : MotifPreparedMasks.Ready (m + 7) input Q d.work :=
    ⟨hs, by simpa only [hx (PowerPorts.scratch (m + 9)) (by change (5 : ℕ) ≠ 13; omega)] using hz,
      by simpa only [hx (MonomialPorts.species (m + 7 + 1)) (by change (7 : ℕ) ≠ 13; omega)] using hi,
      ⟨by simpa only [hx (PowerPorts.next (m + 7 + 2)) (by change (2 : ℕ) ≠ 13; omega)] using h0,
        by simpa only [hx (PowerPorts.accumulator (m + 7 + 2)) (by change (3 : ℕ) ≠ 13; omega)] using h1,
        by simpa only [hx (PowerPorts.power (m + 7 + 2)) (by change (4 : ℕ) ≠ 13; omega)] using h2,
        by simpa only [hx (ReactionPorts.saved (m + 7)) (by change (8 : ℕ) ≠ 13; omega)] using h8⟩,
      ⟨MotifCompleteFrame.kept m input work d.work hu hk,
        by simpa only [hx (CurrentPorts.raw (m + 7)) (by change m + 21 ≠ 13; omega)] using hraw,
        old, hold, by simpa only [hx (MonomialPorts.previous (m + 7 + 1)) (by change (6 : ℕ) ≠ 13; omega)] using hprev⟩,
      by simpa only [hx (MotifBufferPorts.buffer (m + 7) 2) (by change (4 : ℕ) ≠ 13; omega)] using hflags⟩
  exact ⟨d, t, ht, hreach, hhalt, hdc, hready', ri, ⟨hcopy, hdata.reactionBound, hpos⟩, hR work d.work hu hr⟩

end JointThermoComplexity.Complexity.MotifCoreAdvance

#print axioms JointThermoComplexity.Complexity.MotifCoreAdvance.hoareTime
