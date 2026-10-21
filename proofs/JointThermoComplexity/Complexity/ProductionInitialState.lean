module
public import proofs.JointThermoComplexity.Complexity.ProductionOperandLoad
public import proofs.JointThermoComplexity.Complexity.MotifMaskDirectionsBank
public import proofs.JointThermoComplexity.Complexity.MotifForwardEntryBank

set_option autoImplicit false
@[expose] public section

/-! Actual fresh spare tapes supply zero operands, sign head and loop indices for production. -/

namespace JointThermoComplexity.Complexity.ProductionInitialState
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts BoxBufferState

theorem bank_zero (m : ℕ) (work : Fin (m + 20) → Tape) (h : ProductionBank.State m work)
    (j : Fin (m + 20)) (hlo : 9 ≤ j.val) (hhi : j.val ≤ 13) : IsReg 0 (work j) := by
  rw [h j hlo hhi]
  exact DimensionEntry.blank_register

theorem of_box (m idx : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 20) → Tape)
    (h : BoxState.Ready (m + 5) input.length idx (MotifBufferMeta.State (m + 5) input) work)
    (hb : ProductionBank.State m work) :
    ∃ old, old ≤ 4 * input.length ∧ ProductionOperandLoad.State m input.length Q.speciesCount old 0 work ∧ IsReg 0 (work (core m)) := by
  rcases h with ⟨hs, _, _, hbuf, hm⟩
  obtain ⟨old, hold, hp⟩ := hm.2.2
  have hleft : IsReg 0 (work (left m)) := bank_zero m work hb _ (by change 9 ≤ (9 : ℕ); omega) (by change (9 : ℕ) ≤ 13; omega)
  have hright : IsReg 0 (work (right m)) := bank_zero m work hb _ (by change 9 ≤ (10 : ℕ); omega) (by change (10 : ℕ) ≤ 13; omega)
  have hsign : IsReg 0 (work (sign m)) := bank_zero m work hb _ (by change 9 ≤ (11 : ℕ); omega) (by change (11 : ℕ) ≤ 13; omega)
  have hspecies : IsReg 0 (work (species m)) := bank_zero m work hb _ (by change 9 ≤ (12 : ℕ); omega) (by change (12 : ℕ) ≤ 13; omega)
  have hcore : IsReg 0 (work (core m)) := bank_zero m work hb _ (by change 9 ≤ (13 : ℕ); omega) (by change (13 : ℕ) ≤ 13; omega)
  exact ⟨old, hold, ⟨hs, of_register (by omega) hleft, of_register (by omega) hright,
    hbuf.2.2.2, hsign.head_eq, hspecies, (CurrentPins.counts (m + 5) input Q hd work hm.1).1, hp⟩, hcore⟩

theorem of_prepared (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 20) → Tape) (h : MotifPreparedMasks.Ready (m + 5) input Q work) (hb : ProductionBank.State m work) :
    ∃ old, old ≤ 4 * input.length ∧ ProductionOperandLoad.State m input.length Q.speciesCount old 0 work ∧ IsReg 0 (work (core m)) :=
  of_box m Q.speciesCount input Q hd work ((MotifPreparedMasks.ready_iff (m + 5) input Q work).mp h).1 hb

theorem of_directions (m idx : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (work : Fin (m + 20) → Tape)
    (h : MotifDecodedDirections.Ready (m + 5) input Q a idx work) (hb : ProductionBank.State m work) :
    ∃ old, old ≤ 4 * input.length ∧ ProductionOperandLoad.State m input.length Q.speciesCount old 0 work ∧ IsReg 0 (work (core m)) := by
  obtain ⟨⟨hs, hz, hi, hbuf, hm, _⟩, _, _⟩ := h
  exact of_box m idx input Q hd work ⟨hs, hz, hi, hbuf, hm⟩ hb

end JointThermoComplexity.Complexity.ProductionInitialState

#print axioms JointThermoComplexity.Complexity.ProductionInitialState.of_box
#print axioms JointThermoComplexity.Complexity.ProductionInitialState.of_prepared
#print axioms JointThermoComplexity.Complexity.ProductionInitialState.of_directions
