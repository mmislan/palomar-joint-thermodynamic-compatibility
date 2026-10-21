module
public import proofs.JointThermoComplexity.Complexity.MotifCoreState

set_option autoImplicit false
@[expose] public section

/-! Reset the actual completed species index and reconstruct reusable next-core entry without assuming blank buffers. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesReset
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState

abbrev machine (m : ℕ) : TM (m + 22) := clearWorkTM (ProductionPorts.species (m + 2))

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before remaining emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ AtStart m input Q a Q.speciesCount R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifCoreState.State m input Q a.val R work)
      (2 * Q.speciesCount + 5) := by
  rintro inp work out ⟨hc, hdata, hi, hz, hm, hr, hf⟩
  let P : (Fin (m + 22) → Tape) → Prop := fun work' => ∀ j, j ≠ ProductionPorts.species (m + 2) → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ ProductionPorts.species (m + 2) → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hs, hpos, hw⟩ :=
    UnaryReset.hoareTime (ProductionPorts.species (m + 2)) Q.speciesCount before remaining emitted P hP
      inp work out ⟨hc, hdata.safe, hdata.speciesPosition, fun _ _ => rfl⟩
  have hx (j : Fin (m + 22)) (hj : j.val ≠ 12) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hdata' : ProductionOperandData.Data (m + 2) input.length Q.speciesCount 0 0 d.work :=
    ⟨by simpa only [hx (ProductionPorts.left (m + 2)) (by change (9 : ℕ) ≠ 12; omega)] using hdata.productReusable,
      by simpa only [hx (ProductionPorts.right (m + 2)) (by change (10 : ℕ) ≠ 12; omega)] using hdata.reactantReusable,
      by simpa only [hx (ProductionPorts.magnitude (m + 2)) (by change (8 : ℕ) ≠ 12; omega)] using hdata.magnitudeReusable,
      by simpa only [hx (ProductionPorts.sign (m + 2)) (by change (11 : ℕ) ≠ 12; omega)] using hdata.signHead,
      hpos, by simpa only [hx (ProductionPorts.count (m + 2)) (by change m + 17 ≠ 12; omega)] using hdata.speciesCount,
      by simpa only [hx (ProductionPorts.reaction (m + 2)) (by change (6 : ℕ) ≠ 12; omega)] using hdata.reactionPosition⟩
  have hmask : MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a))
      (MotifMaskData.species (Q.network.motifs a)).length (work (MotifBufferPorts.buffer (m + 7) 0)) := by
    simpa only [MotifMaskData.species_length] using hm
  have hRspecies : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work' :=
    fun work work' hu => hR work work' (MotifCompleteFrame.of_species m work work' hu)
  refine ⟨d, t, ht, hreach, hhalt, hdc, MotifCoreState.of_reset m input Q hd a R d.work hs hdata' ?_ ?_ ?_ ?_ ?_⟩
  · simpa only [hx (ProductionPorts.current (m + 2)) (by change (7 : ℕ) ≠ 12; omega)] using hi
  · simpa only [hx (PowerPorts.scratch (m + 9)) (by change (5 : ℕ) ≠ 12; omega)] using hz
  · simpa only [hx (MotifBufferPorts.buffer (m + 7) 0) (by change (2 : ℕ) ≠ 12; omega)] using hmask.stored
  · simpa only [hx (MotifBufferPorts.buffer (m + 7) 1) (by change (3 : ℕ) ≠ 12; omega)] using hr
  · exact fixed_frame m input Q a R hRspecies work d.work (ProductionSpeciesFrame.of_species m work d.work hw) hf

end JointThermoComplexity.Complexity.ProductionSpeciesReset

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesReset.hoareTime
