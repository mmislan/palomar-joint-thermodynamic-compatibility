module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesRestart

set_option autoImplicit false
@[expose] public section

/-! Actual bounded restart and complete production sum emit exactly one strict production-positivity formula. -/

namespace JointThermoComplexity.Complexity.ProductionPositiveOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState

def outputPrefix : List Bool := [false, true, true] ++ ProductionSelectedTerm.zeroCode

def formula (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (s : Fin Q.speciesCount) :
    RealSyntax.Formula (NetworkMembership.arity Q.network) :=
  .lt (.int 0) (NetworkFormula.productionTerm Q.network a s (NetworkMembership.currentIndex Q.network))

def machine (m : ℕ) : TM (m + 22) := seqTM (ProductionSpeciesRestart.machine m)
  (seqTM (emitBitsTM outputPrefix) (ProductionSum.machine (m + 2)))

def timeBound (L : ℕ) : ℕ := 4 * L ^ 4 + 52 * L ^ 3 + 150 * L ^ 2 + 182 * L + 47

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q a s.val R work)
      (fun inp work out => Cursor [] input (emitted ++ (formula Q a s).code) inp work out ∧ State m input Q a s.val R work)
      (timeBound input.length) := by
  let P : (Fin (m + 22) → Tape) → Prop := fun work =>
    MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a)) s.val (work (MotifBufferPorts.buffer (m + 7) 0)) ∧
    Fixed m input Q a R work
  have hP : ∀ work work', ProductionReactionState.Unchanged (m + 2) work work' → P work → P work' := by
    rintro work work' hw ⟨hm, hf⟩
    exact ⟨by simpa only [ProductionSpeciesFrame.inner_species_mask m work work' hw] using hm,
      fixed_frame m input Q a R hR work work' (ProductionSpeciesFrame.of_production m work work' hw) hf⟩
  have hr := ProductionSpeciesRestart.hoareTime m input Q hd a s.val before remaining emitted R hR
  have hf := FixedOutput.hoareTime outputPrefix before remaining emitted (AtStart m input Q a s.val R)
  have hb := ProductionSum.decoded_hoareTime (m + 2) input Q hd a s before remaining (emitted ++ outputPrefix) hsplit P hP
  have hfb := seqTM_hoareTime (emitBitsTM outputPrefix) (ProductionSum.machine (m + 2)) hf (by
    rintro inp work out ⟨hc, _, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    rcases hp with ⟨hdata, hi, hz, hm, hreaction, hfixed⟩
    have hcounts := CurrentPins.counts (m + 7) input Q hd work hfixed.1
    exact ⟨hc, hdata, hi, hz, hreaction, ⟨hm, hfixed⟩, hcounts.2⟩) hb
  have hfull := seqTM_hoareTime (ProductionSpeciesRestart.machine m)
    (seqTM (emitBitsTM outputPrefix) (ProductionSum.machine (m + 2))) hr (by
      rintro inp work out ⟨hc, hp⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hp.1.safe, hp⟩) hfb
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hprefix : outputPrefix.length = 8 := rfl
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hp, _, hstored⟩
    refine ⟨?_, Q.reactionCount, by omega, Q.speciesCount + Q.reactionCount, by omega,
      hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.1, hstored, hp.2.2.2.2.2⟩
    simpa only [formula, RealSyntax.Formula.code, RealSyntax.Term.code, outputPrefix,
      ProductionSelectedTerm.zeroCode, List.append_assoc] using hc) (by
      unfold timeBound ProductionStart.timeBound ProductionSum.timeBound
      rw [hprefix]
      omega)

end JointThermoComplexity.Complexity.ProductionPositiveOutput

#print axioms JointThermoComplexity.Complexity.ProductionPositiveOutput.hoareTime
