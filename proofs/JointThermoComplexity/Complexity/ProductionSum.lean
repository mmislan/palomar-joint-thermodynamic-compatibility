module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionBuild

set_option autoImplicit false
@[expose] public section

/-! Initialize stored reaction masks and emit the exact complete production sum from original binary input in quartic time. -/

namespace JointThermoComplexity.Complexity.ProductionSum
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts ProductionReactionState ProductionFuelFrame

def machine (m : ℕ) : TM (m + 20) := seqTM (ProductionMaskInit.machine m) (ProductionReactionBuild.machine m)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 4 + 52 * L ^ 3 + 150 * L ^ 2 + 167 * L + 16

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) (before remaining emitted : List Bool)
    (hsplit : before ++ remaining = input) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        ProductionOperandLoad.State m input.length Q.speciesCount 0 s.val work ∧
        IsReg Q.speciesCount (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧
        BoxBufferState.Stored (List.ofFn mask) (work (MotifBufferPorts.buffer (m + 5) 1)) ∧ R work ∧ IsReg Q.reactionCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (ProductionDenseCode.term Q s mask).code) inp work out ∧
        State m input.length Q.speciesCount Q.reactionCount s.val (Q.speciesCount + Q.reactionCount)
          (List.ofFn mask) Q.reactionCount R work ∧ IsReg Q.reactionCount (work (fuel m)) ∧
        BoxBufferState.Stored (List.ofFn mask) (work (MotifBufferPorts.buffer (m + 5) 1))) (timeBound input.length) := by
  let R' : (Fin (m + 20) → Tape) → Prop := fun work => R work ∧ IsReg Q.reactionCount (work (fuel m))
  have hR' : ∀ work work', Unchanged m work work' → R' work → R' work' := by
    rintro work work' hw ⟨hr, hf⟩
    exact ⟨hR work work' hw hr, by simpa only [fuel_eq m work work' hw] using hf⟩
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hm := ProductionMaskInit.hoareTime m Q.speciesCount 0 s.val Q.speciesCount input before remaining emitted hsplit
    (List.ofFn mask) (by simp only [List.length_ofFn]; omega) R' hR'
  have hb := ProductionReactionBuild.hoareTime m input Q hd s mask emitted R hR
  have hs := seqTM_hoareTime (ProductionMaskInit.machine m) (ProductionReactionBuild.machine m) hm (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, map_state m input.length Q.speciesCount 0 s.val Q.speciesCount (List.ofFn mask) 0 R' R work (fun h => h.1) hp,
      hp.2.2.2.2.2⟩) hb
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hp, hf⟩
    have hmask : MotifDirectionState.At (List.ofFn mask) (List.ofFn mask).length (work (MotifBufferPorts.buffer (m + 5) 1)) := by
      simpa only [List.length_ofFn] using hp.2.2.2.1
    exact ⟨hc, hp, hf, hmask.stored⟩) (by
      unfold timeBound ProductionReactionBuild.timeBound
      omega)

theorem decoded_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool)
    (hsplit : before ++ remaining = input) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        ProductionOperandLoad.State m input.length Q.speciesCount 0 s.val work ∧
        IsReg Q.speciesCount (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧
        BoxBufferState.Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 5) 1)) ∧
        R work ∧ IsReg Q.reactionCount (work (fuel m)))
      (fun inp work out => Cursor [] input
        (emitted ++ (NetworkFormula.productionTerm Q.network a s (NetworkMembership.currentIndex Q.network)).code) inp work out ∧
        State m input.length Q.speciesCount Q.reactionCount s.val (Q.speciesCount + Q.reactionCount)
          (MotifMaskData.reactions (Q.network.motifs a)) Q.reactionCount R work ∧ IsReg Q.reactionCount (work (fuel m)) ∧
        BoxBufferState.Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 5) 1)))
      (timeBound input.length) := by
  simpa only [MotifMaskData.reactions_eq, ProductionDenseCode.term_eq_production] using
    hoareTime m input Q hd s (fun i => decide (i ∈ (Q.network.motifs a).reactions)) before remaining emitted hsplit R hR

end JointThermoComplexity.Complexity.ProductionSum

#print axioms JointThermoComplexity.Complexity.ProductionSum.hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionSum.decoded_hoareTime
