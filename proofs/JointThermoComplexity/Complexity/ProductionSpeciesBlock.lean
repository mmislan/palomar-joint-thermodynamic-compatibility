module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesMaskInit
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesBuild

set_option autoImplicit false
@[expose] public section

/-! Actual mask/input initialization and the copied-species loop emit the complete exact production formula. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesBlock
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState ProductionSpeciesFuelFrame ProductionSpeciesMaskInit

def machine (m : ℕ) : TM (m + 22) := seqTM (ProductionSpeciesMaskInit.machine m) (ProductionSpeciesBuild.machine m)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 5 + 52 * L ^ 4 + 150 * L ^ 3 + 184 * L ^ 2 + 67 * L + 14

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ StoredState m input Q a R work ∧
        IsReg Q.speciesCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (ProductionSpeciesDenseCode.formula Q a).code) inp work out ∧
        State m input Q a Q.speciesCount R work ∧ IsReg Q.speciesCount (work (fuel m)) ∧
        BoxBufferState.Stored (MotifMaskData.species (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 0)))
      (timeBound input.length) := by
  let R' : (Fin (m + 22) → Tape) → Prop := fun work => R work ∧ IsReg Q.speciesCount (work (fuel m))
  have hR' : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R' work → R' work' := by
    rintro work work' hw ⟨hr, hf⟩
    exact ⟨hR work work' hw hr, by simpa only [fuel_eq m work work' hw] using hf⟩
  have hm := ProductionSpeciesMaskInit.hoareTime m input Q hd a before remaining emitted hsplit R' hR'
  have hb := ProductionSpeciesBuild.hoareTime m input Q hd a emitted R hR
  have hs := seqTM_hoareTime (ProductionSpeciesMaskInit.machine m) (ProductionSpeciesBuild.machine m) hm (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    have hfuel : IsReg Q.speciesCount (work (fuel m)) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrest⟩ := hp
      exact hrest.2
    exact ⟨hc, map_state m input Q a 0 R' R work (fun h => h.1) hp, hfuel⟩) hb
  exact hs.consequence (by
    rintro inp work out ⟨hc, hp, hfuel⟩
    obtain ⟨ri, hri, idx, hidx, hdata, hi, hz, hm, hr, hk, hraw, hf, ha, hrest⟩ := hp
    exact ⟨hc, ri, hri, idx, hidx, hdata, hi, hz, hm, hr, hk, hraw, hf, ha, hrest, hfuel⟩) (by
      rintro inp work out ⟨hc, hp, hfuel⟩
      have hmask : MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a))
          (MotifMaskData.species (Q.network.motifs a)).length (work (MotifBufferPorts.buffer (m + 7) 0)) := by
        obtain ⟨_, _, _, _, _, _, _, hm, _⟩ := hp
        simpa only [MotifMaskData.species_length] using hm
      exact ⟨hc, hp, hfuel, hmask.stored⟩) (by
        unfold timeBound ProductionSpeciesBuild.timeBound
        omega)

end JointThermoComplexity.Complexity.ProductionSpeciesBlock

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesBlock.hoareTime
