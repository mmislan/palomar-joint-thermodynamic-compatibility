module
public import proofs.JointThermoComplexity.Complexity.MotifDirections
public import proofs.JointThermoComplexity.Complexity.MotifPreparedMasks
public import proofs.JointThermoComplexity.Complexity.NetworkNumbering

set_option autoImplicit false
@[expose] public section

/-! Exact direction allFin output for a decoded supplied motif, retaining species-mask and validated state. -/

namespace JointThermoComplexity.Complexity.MotifDecodedDirections
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionFrame BoxBufferState PowerPorts MonomialPorts ReactionPorts

def Preserved (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (work : Fin (m + 15) → Tape) : Prop :=
  MotifBufferMeta.State m input work ∧ Stored (MotifMaskData.species (Q.network.motifs a)) (work (buffer m 0))

def Ready (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (idx : ℕ)
    (work : Fin (m + 15) → Tape) : Prop :=
  BoxState.Ready m input.length idx (Preserved m input Q a) work ∧
    Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (buffer m 1)) ∧
    Stored (BoxTraversalData.forward Q) (work (buffer m 2))

def formula (Q : NetworkCodec.Input) (a : Fin Q.coreCount) : RealSyntax.Formula (NetworkMembership.arity Q.network) :=
  NetworkFormula.allFin (fun i => if i ∈ (Q.network.motifs a).reactions then
    NetworkFormula.directionFormula (Q.network.forward i) (NetworkMembership.currentIndex Q.network i) else .truth)

theorem dense_formula (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    MotifDirectionDenseCode.formula (fun i => decide (i ∈ (Q.network.motifs a).reactions))
      Q.network.forward (NetworkMembership.currentIndex Q.network) = formula Q a := by
  simp [MotifDirectionDenseCode.formula, formula]

theorem separate (m : ℕ) : BoxState.Separate m (ReactionFuel.slot m) := by
  have hx (j : Fin (m + 15)) (hj : j.val ≤ 8) : ReactionFuel.slot m ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change m + 11 = j.val at hv
    omega
  exact ⟨hx (species (m + 1)) (by change (7 : ℕ) ≤ 8; omega),
    hx (scratch (m + 2)) (by change (5 : ℕ) ≤ 8; omega),
    hx (next (m + 2)) (by change (2 : ℕ) ≤ 8; omega),
    hx (accumulator (m + 2)) (by change (3 : ℕ) ≤ 8; omega),
    hx (power (m + 2)) (by change (4 : ℕ) ≤ 8; omega), hx (saved m) (by change (8 : ℕ) ≤ 8; omega)⟩

def machine (m : ℕ) : TM (m + 15) := MotifDirections.machine m (ReactionFuel.slot m)

theorem preserved_frame (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (work work' : Fin (m + 15) → Tape) (hw : Unchanged m work work') :
    Preserved m input Q a work → Preserved m input Q a work' := by
  rintro ⟨hm, hs⟩
  exact ⟨metadata m input work work' hw hm, species_mask m _ work work' hw hs⟩

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor before tail emitted inp work out ∧ Ready m input Q a Q.speciesCount work)
      (fun inp work out => Cursor before tail (emitted ++ (formula Q a).code) inp work out ∧
        Ready m input Q a (Q.speciesCount + Q.reactionCount) work) (MotifDirections.timeBound input.length) := by
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hs := MotifDirections.hoareTime m input.length Q.speciesCount (NetworkNumbering.decoded_arity_bound hd)
    (show Q.reactionCount ≤ input.length by omega) (ReactionFuel.slot m) (separate m)
    (NetworkMembership.currentIndex Q.network) (fun _ => rfl)
    (fun i => decide (i ∈ (Q.network.motifs a).reactions)) Q.network.forward before tail emitted
    (Preserved m input Q a) (preserved_frame m input Q a)
  exact hs.consequence (by
    rintro inp work out ⟨hc, hp, hm, hf⟩
    have hcount := (CurrentPins.counts m input Q hd work hp.2.2.2.2.1.1).2
    exact ⟨hc, hp, by simpa only [MotifMaskData.reactions_eq] using hm,
      by simpa only [MotifMaskData.forward_eq] using hf, hcount⟩) (by
      rintro inp work out ⟨hc, hp, hm, hf, _⟩
      exact ⟨by simpa only [dense_formula] using hc, hp,
        by simpa only [MotifMaskData.reactions_eq] using hm, by simpa only [MotifMaskData.forward_eq] using hf⟩) le_rfl

end JointThermoComplexity.Complexity.MotifDecodedDirections

#print axioms JointThermoComplexity.Complexity.MotifDecodedDirections.dense_formula
#print axioms JointThermoComplexity.Complexity.MotifDecodedDirections.preserved_frame
#print axioms JointThermoComplexity.Complexity.MotifDecodedDirections.hoareTime
