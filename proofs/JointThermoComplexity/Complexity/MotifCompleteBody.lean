module
public import proofs.JointThermoComplexity.Complexity.ProductionPreparedBlock

set_option autoImplicit false
@[expose] public section

/-! One complete supplied-core body emits both direction and production allFin constraints at shared indices. -/

namespace JointThermoComplexity.Complexity.MotifCompleteBody
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState ProductionSpeciesFuelFrame

def formula (Q : NetworkCodec.Input) (a : Fin Q.coreCount) : RealSyntax.Formula (NetworkMembership.arity Q.network) :=
  .conj (MotifDecodedDirections.formula Q a) (ProductionSpeciesDenseCode.formula Q a)

theorem formula_eq (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    formula Q a = .conj
      (NetworkFormula.allFin (fun i => if i ∈ (Q.network.motifs a).reactions then
        NetworkFormula.directionFormula (Q.network.forward i) (NetworkMembership.currentIndex Q.network i) else .truth))
      (NetworkFormula.allFin (fun s => if s ∈ (Q.network.motifs a).species then
        .lt (.int 0) (NetworkFormula.productionTerm Q.network a s (NetworkMembership.currentIndex Q.network)) else .truth)) := rfl

def machine (m : ℕ) : TM (m + 22) := seqTM (emitBitsTM CircuitSerialization.conjunctionTag)
  (seqTM (MotifMaskDirections.machine (m + 7)) (ProductionPreparedBlock.machine m))

def timeBound (L : ℕ) : ℕ := 4 * L ^ 5 + 52 * L ^ 4 + 182 * L ^ 3 + 240 * L ^ 2 + 153 * L + 59

theorem hoareTime (m ri : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool)
    (hsplit : before ++ ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail) = input)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hRmask : ∀ work work', MotifPassFrame.Unchanged (m + 7) work work' → R work → R work')
    (hRspecies : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail)
        emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        OuterProductionResources.Held m input.length Q.speciesCount ri 0 a.val work ∧ R work ∧
        IsReg Q.speciesCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ (formula Q a).code) inp work out ∧
        State m input Q a Q.speciesCount R work ∧ IsReg Q.speciesCount (work (fuel m)) ∧
        BoxBufferState.Stored (MotifMaskData.species (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 0)))
      (timeBound input.length) := by
  let R' : (Fin (m + 22) → Tape) → Prop := fun work => R work ∧ IsReg Q.speciesCount (work (fuel m))
  have hR' : ∀ work work', MotifPassFrame.Unchanged (m + 7) work work' → R' work → R' work' := by
    rintro work work' hw ⟨hr, hf⟩
    have hfu := MotifPassFrame.outside (m + 7) work work' hw (fuel m) (Or.inr (by change 8 ≤ (14 : ℕ); omega))
    exact ⟨hRmask work work' hw hr, by simpa only [hfu] using hf⟩
  let P : (Fin (m + 22) → Tape) → Prop := fun work => MotifPreparedMasks.Ready (m + 7) input Q work ∧
    OuterProductionResources.Held m input.length Q.speciesCount ri 0 a.val work ∧ R' work
  have hf := FixedOutput.hoareTime CircuitSerialization.conjunctionTag before
    ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail) emitted P
  have hdir := OuterPreparedProduction.hoareTime m ri 0 input Q hd a before tail
    (emitted ++ CircuitSerialization.conjunctionTag) R' hR'
  have hb := ProductionPreparedBlock.hoareTime m ri input Q hd a
    (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail
    ((emitted ++ CircuitSerialization.conjunctionTag) ++ (MotifDecodedDirections.formula Q a).code)
    (by simpa only [List.append_assoc] using hsplit) R hRspecies
  have hdb := seqTM_hoareTime (MotifMaskDirections.machine (m + 7)) (ProductionPreparedBlock.machine m) hdir (by
    rintro inp work out ⟨hc, hp, hdata, hr, hfuel⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp, hdata, hr, hfuel⟩) hb
  have hfull := seqTM_hoareTime (emitBitsTM CircuitSerialization.conjunctionTag)
    (seqTM (MotifMaskDirections.machine (m + 7)) (ProductionPreparedBlock.machine m)) hf (by
      rintro inp work out ⟨hc, _, hp, hdata, hr, hfuel⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hp, hdata, hr, hfuel⟩) hdb
  exact hfull.consequence (fun _ _ _ ⟨hc, hp, hdata, hr, hfuel⟩ => ⟨hc, hp.1, hp, hdata, hr, hfuel⟩) (by
    rintro inp work out ⟨hc, hp, hfuel, hm⟩
    exact ⟨by simpa only [formula, RealSyntax.Formula.code, CircuitSerialization.conjunctionTag, List.append_assoc] using hc,
      hp, hfuel, hm⟩) (by
        unfold timeBound MotifMaskDirections.timeBound ProductionSpeciesBlock.timeBound CircuitSerialization.conjunctionTag
        simp only [List.length_cons, List.length_nil]
        omega)

end JointThermoComplexity.Complexity.MotifCompleteBody

#print axioms JointThermoComplexity.Complexity.MotifCompleteBody.formula_eq
#print axioms JointThermoComplexity.Complexity.MotifCompleteBody.hoareTime
