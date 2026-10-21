module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesState

set_option autoImplicit false
@[expose] public section

/-! Bounded actual reaction/current values restart at zero/species-count while species masks and metadata are retained. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesRestart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState

abbrev machine (m : ℕ) : TM (m + 22) := ProductionStart.machine (m + 2)

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (pos : ℕ) (before remaining emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q a pos R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ AtStart m input Q a pos R work)
      (ProductionStart.timeBound input.length) := by
  let P : (Fin (m + 22) → Tape) → Prop := fun work =>
    MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a)) pos (work (MotifBufferPorts.buffer (m + 7) 0)) ∧
    BoxBufferState.Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 1)) ∧
    Fixed m input Q a R work
  have hP : ∀ work work',
      (∀ j, j ≠ ProductionPorts.reaction (m + 2) → j ≠ ProductionPorts.current (m + 2) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hm, hr, hf⟩
    have hmask : work' (MotifBufferPorts.buffer (m + 7) 0) = work (MotifBufferPorts.buffer (m + 7) 0) := by
      apply hw
      · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 6 at hv; omega
      · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 7 at hv; omega
    have hreaction : work' (MotifBufferPorts.buffer (m + 7) 1) = work (MotifBufferPorts.buffer (m + 7) 1) := by
      apply hw
      · intro he; have hv := congrArg Fin.val he; change (3 : ℕ) = 6 at hv; omega
      · intro he; have hv := congrArg Fin.val he; change (3 : ℕ) = 7 at hv; omega
    exact ⟨by simpa only [hmask] using hm, by simpa only [hreaction] using hr,
      fixed_frame m input Q a R hR work work' (ProductionSpeciesFrame.of_start m work work' hw) hf⟩
  rintro inp work out ⟨hc, hp⟩
  obtain ⟨ri, hri, idx, hidx, hdata, hi, hz, hm, hr, hf⟩ := hp
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  exact ProductionStart.hoareTime (m + 2) input.length Q.speciesCount ri pos idx hri (by omega) hidx
    before remaining emitted P hP inp work out ⟨hc, hdata, hi, hz, hm, hr, hf⟩

end JointThermoComplexity.Complexity.ProductionSpeciesRestart

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesRestart.hoareTime
