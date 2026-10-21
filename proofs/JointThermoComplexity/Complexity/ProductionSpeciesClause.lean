module
public import proofs.JointThermoComplexity.Complexity.ProductionPositiveOutput

set_option autoImplicit false
@[expose] public section

/-! The actual supplied species-mask bit selects exact strict production positivity or truth. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesClause
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState

def formula (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (s : Fin Q.speciesCount) :
    RealSyntax.Formula (NetworkMembership.arity Q.network) :=
  if s ∈ (Q.network.motifs a).species then ProductionPositiveOutput.formula Q a s else .truth

def machine (m : ℕ) : TM (m + 22) := FlagBranch.machine (MotifBufferPorts.buffer (m + 7) 0)
  (ProductionPositiveOutput.machine m) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := ProductionPositiveOutput.timeBound L + 2

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (s : Fin Q.speciesCount) (emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a s.val R work)
      (fun inp work out => Cursor [] input (emitted ++ (formula Q a s).code) inp work out ∧ State m input Q a s.val R work)
      (timeBound input.length) := by
  let P := State m input Q a s.val R
  have hread (work : Fin (m + 22) → Tape) (hp : P work) :
      (work (MotifBufferPorts.buffer (m + 7) 0)).read = Γ.ofBool (decide (s ∈ (Q.network.motifs a).species)) := by
    obtain ⟨_, _, _, _, _, _, _, hm, _⟩ := hp
    have hlen : s.val < (MotifMaskData.species (Q.network.motifs a)).length := by
      rw [MotifMaskData.species_length]
      exact s.isLt
    simpa only [MotifMaskData.species_at (Q.network.motifs a) s] using hm.read hlen
  have hy := ProductionPositiveOutput.hoareTime m input Q hd a s [] input emitted rfl R hR
  have hn := FixedOutput.hoareTime [false, false, false] [] input emitted P
  have hn' : (emitBitsTM [false, false, false]).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ P work)
      (fun inp work out => Cursor [] input (emitted ++ [false, false, false]) inp work out ∧ P work) 3 :=
    hn.consequence (fun _ work _ ⟨hc, hp⟩ => ⟨hc, safe m input Q a s.val R work hp, hp⟩)
      (fun _ _ _ ⟨hc, _, hp⟩ => ⟨hc, hp⟩) le_rfl
  have hn'' := hn'.mono_bound (b' := ProductionPositiveOutput.timeBound input.length) (by
    unfold ProductionPositiveOutput.timeBound
    omega)
  by_cases hsel : s ∈ (Q.network.motifs a).species
  · have hb := FlagBranchRun.yes_hoareTime (MotifBufferPorts.buffer (m + 7) 0)
      (ProductionPositiveOutput.machine m) (emitBitsTM [false, false, false])
      [] input emitted [] input (emitted ++ (formula Q a s).code) P P
      (ProductionPositiveOutput.timeBound input.length) (by simpa only [formula, hsel, ↓reduceIte] using hy)
    have hb' := hb.mono_bound (b' := timeBound input.length) (by unfold timeBound; omega)
    rintro inp work out ⟨hc, hp⟩
    exact hb' inp work out ⟨⟨hc, hp⟩, by simpa [hsel, Γ.ofBool] using hread work hp⟩
  · have hb := FlagBranchRun.no_hoareTime (MotifBufferPorts.buffer (m + 7) 0)
      (ProductionPositiveOutput.machine m) (emitBitsTM [false, false, false])
      [] input emitted [] input (emitted ++ (formula Q a s).code) P P
      (ProductionPositiveOutput.timeBound input.length) (by
        simpa only [formula, hsel, ↓reduceIte, RealSyntax.Formula.code] using hn'')
    rintro inp work out ⟨hc, hp⟩
    exact hb inp work out ⟨⟨hc, hp⟩, by simpa [hsel, Γ.ofBool] using hread work hp⟩

end JointThermoComplexity.Complexity.ProductionSpeciesClause

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesClause.hoareTime
