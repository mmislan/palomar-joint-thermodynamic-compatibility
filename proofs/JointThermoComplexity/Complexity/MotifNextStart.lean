module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesReset
public import proofs.JointThermoComplexity.Complexity.MotifCoreAdvance

set_option autoImplicit false
@[expose] public section

/-! Restart actual production registers, clear the completed species index and advance to reusable next-core state. -/

namespace JointThermoComplexity.Complexity.MotifNextStart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (m : ℕ) : TM (m + 22) := seqTM (ProductionSpeciesRestart.machine m)
  (seqTM (ProductionSpeciesReset.machine m) (MotifCoreAdvance.machine m))

def timeBound (L : ℕ) : ℕ := 19 * L + 34

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before remaining emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionSpeciesState.State m input Q a Q.speciesCount R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifCoreState.State m input Q (a.val + 1) R work)
      (timeBound input.length) := by
  have hRspecies : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work' :=
    fun work work' hw => hR work work' (MotifCompleteFrame.of_species m work work' hw)
  have hr := ProductionSpeciesRestart.hoareTime m input Q hd a Q.speciesCount before remaining emitted R hRspecies
  have hs := ProductionSpeciesReset.hoareTime m input Q hd a before remaining emitted R hR
  have ha := MotifCoreAdvance.hoareTime m a.val input Q before remaining emitted R hR
  have hsa := seqTM_hoareTime (ProductionSpeciesReset.machine m) (MotifCoreAdvance.machine m) hs (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp⟩) ha
  have hfull := seqTM_hoareTime (ProductionSpeciesRestart.machine m)
    (seqTM (ProductionSpeciesReset.machine m) (MotifCoreAdvance.machine m)) hr (by
      rintro inp work out ⟨hc, hp⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hp⟩) hsa
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have ha := a.isLt
  exact hfull.mono_bound (by unfold timeBound ProductionStart.timeBound; omega)

end JointThermoComplexity.Complexity.MotifNextStart

#print axioms JointThermoComplexity.Complexity.MotifNextStart.hoareTime
