module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesStep

set_option autoImplicit false
@[expose] public section

/-! Rewind the actual supplied species mask and original input before the complete production block. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesMaskInit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState

def StoredState (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) : Prop :=
  ∃ ri, ri ≤ 4 * input.length ∧ ∃ idx, idx ≤ input.length ∧
    ProductionOperandLoad.State (m + 2) input.length Q.speciesCount ri 0 work ∧
    IsReg idx (work (ProductionPorts.current (m + 2))) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 9))) ∧
    BoxBufferState.Stored (MotifMaskData.species (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 0)) ∧
    BoxBufferState.Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 1)) ∧ Fixed m input Q a R work

theorem rewind_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (before remaining emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (rewindWorkTM (MotifBufferPorts.buffer (m + 7) 0)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ StoredState m input Q a R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q a 0 R work)
      (Q.speciesCount + 3) := by
  rintro inp work out ⟨hc, ri, hri, idx, hidx, hdata, hi, hz, hm, hr, hf⟩
  let P : (Fin (m + 22) → Tape) → Prop := fun work' => ∀ j, j ≠ MotifBufferPorts.buffer (m + 7) 0 → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ MotifBufferPorts.buffer (m + 7) 0 → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hs, hbits, hzero, hw⟩ :=
    BinaryPrefixRewind.hoareTime (MotifBufferPorts.buffer (m + 7) 0) (MotifMaskData.species (Q.network.motifs a))
      before remaining emitted P hP inp work out ⟨hc, hdata.safe, hm.1, hm.2, fun _ _ => rfl⟩
  have hx (j : Fin (m + 22)) (hj : j.val ≠ 2) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hcopy := ProductionOperandData.motif_frame (m + 2) input.length Q.speciesCount ri 0 work d.work
    (MotifPassFrame.of_mask (m + 7) 0 work d.work hw) (ProductionOperandData.of_state _ _ _ _ _ work hdata)
  refine ⟨d, t, ?_, hreach, hhalt, hdc, ri, hri, idx, hidx,
    ProductionOperandData.to_state _ _ _ _ _ d.work hs hcopy, ?_, ?_, ⟨hbits.2, hzero, hbits.1⟩, ?_, ?_⟩
  · simpa only [MotifMaskData.species_length] using ht
  · simpa only [hx (ProductionPorts.current (m + 2)) (by change (7 : ℕ) ≠ 2; omega)] using hi
  · simpa only [hx (PowerPorts.scratch (m + 9)) (by change (5 : ℕ) ≠ 2; omega)] using hz
  · simpa only [hx (MotifBufferPorts.buffer (m + 7) 1) (by change (3 : ℕ) ≠ 2; omega)] using hr
  · exact fixed_frame m input Q a R hR work d.work (ProductionSpeciesFrame.of_mask m work d.work hw) hf

def machine (m : ℕ) : TM (m + 22) := seqTM (rewindWorkTM (MotifBufferPorts.buffer (m + 7) 0)) rewindInputTM

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ StoredState m input Q a R work)
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a 0 R work) (2 * input.length + 7) := by
  have hm := rewind_hoareTime m input Q a before remaining emitted R hR
  have hr := InputRewind.hoareTime before remaining emitted (State m input Q a 0 R)
  have hs := seqTM_hoareTime (rewindWorkTM (MotifBufferPorts.buffer (m + 7) 0)) rewindInputTM hm (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp⟩) hr
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hlength := congrArg List.length hsplit
  simp only [List.length_append] at hlength
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ ⟨hc, hp⟩ => ⟨by simpa only [hsplit] using hc, hp⟩) (by omega)

end JointThermoComplexity.Complexity.ProductionSpeciesMaskInit

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesMaskInit.rewind_hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesMaskInit.hoareTime
