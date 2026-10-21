module
public import proofs.JointThermoComplexity.Complexity.MotifMaskData
public import proofs.JointThermoComplexity.Complexity.BooleanWordSkip

set_option autoImplicit false
@[expose] public section

/-! Read one supplied motif's species and reaction masks using their actual retained count registers. -/

namespace JointThermoComplexity.Complexity.MotifRecordSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w n r : ℕ}

def machine (species reactions : Fin w) : TM w :=
  seqTM (BooleanWordSkip.machine species) (BooleanWordSkip.machine reactions)

def timeBound (n r : ℕ) : ℕ := 4 * n + 4 * r + 5

theorem hoareTime (species reactions : Fin w) (a : NetworkData.Motif n r) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Tape → Prop) :
    (machine species reactions).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif n r).code a ++ tail) emitted inp work out ∧
        IsReg n (work species) ∧ IsReg r (work reactions) ∧ R work out)
      (fun inp work out => Cursor (before ++ (DataCodec.motif n r).code a) tail emitted inp work out ∧
        IsReg n (work species) ∧ IsReg r (work reactions) ∧ R work out) (timeBound n r) := by
  have hs := BooleanWordSkip.hoareTime species (MotifMaskData.species a) before (MotifMaskData.reactions a ++ tail) emitted
    (fun work out => IsReg r (work reactions) ∧ R work out)
  have hr := BooleanWordSkip.hoareTime reactions (MotifMaskData.reactions a) (before ++ MotifMaskData.species a) tail emitted
    (fun work out => IsReg n (work species) ∧ R work out)
  have hfull := seqTM_hoareTime (BooleanWordSkip.machine species) (BooleanWordSkip.machine reactions) hs (by
    rintro inp work out ⟨hc, hn, hreact, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, by simpa only [MotifMaskData.reactions_length] using hreact,
      by simpa only [MotifMaskData.species_length] using hn, hR⟩) hr
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hn, hreact, hR⟩
    exact ⟨by simpa only [MotifMaskData.motif_code, List.append_assoc] using hc,
      by simpa only [MotifMaskData.species_length] using hn, hreact, hR⟩) (by
      rintro inp work out ⟨hc, hreact, hn, hR⟩
      exact ⟨by simpa only [MotifMaskData.motif_code, List.append_assoc] using hc,
        hn, by simpa only [MotifMaskData.reactions_length] using hreact, hR⟩) (by
        unfold timeBound
        rw [MotifMaskData.species_length, MotifMaskData.reactions_length]
        omega)

end JointThermoComplexity.Complexity.MotifRecordSkip

#print axioms JointThermoComplexity.Complexity.MotifRecordSkip.hoareTime
