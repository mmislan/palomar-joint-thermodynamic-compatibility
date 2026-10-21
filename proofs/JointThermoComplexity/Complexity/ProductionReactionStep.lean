module
public import proofs.JointThermoComplexity.Complexity.ProductionIndexAdvance
public import proofs.JointThermoComplexity.Complexity.ProductionMaskAdvance

set_option autoImplicit false
@[expose] public section

/-! One actual ordered production-sum step emits add/selected-term and advances reaction, current and mask together. -/

namespace JointThermoComplexity.Complexity.ProductionReactionStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts ProductionReactionState

def addTag : List Bool := [false, true, false]

def word (Q : NetworkCodec.Input) (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (selected : Bool) : List Bool :=
  addTag ++ (ProductionSelectedTerm.term selected Q i s).code

def machine (m : ℕ) : TM (m + 20) := seqTM
  (seqTM (seqTM (emitBitsTM addTag) (ProductionSelectedTerm.machine m)) (ProductionIndexAdvance.machine m))
  (ProductionMaskAdvance.machine m)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 3 + 52 * L ^ 2 + 150 * L + 162

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (mask : List Bool) (him : i.val < mask.length)
    (emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧
        State m input.length Q.speciesCount i.val s.val (NetworkMembership.currentIndex Q.network i).val mask i.val R work)
      (fun inp work out => Cursor [] input (emitted ++ word Q i s mask[i.val]) inp work out ∧
        State m input.length Q.speciesCount (i.val + 1) s.val ((NetworkMembership.currentIndex Q.network i).val + 1)
          mask (i.val + 1) R work) (timeBound input.length) := by
  let S : (Fin (m + 20) → Tape) → Prop := fun work =>
    MotifDirectionState.At mask i.val (work (MotifBufferPorts.buffer (m + 5) 1)) ∧ R work
  have hS : ∀ work work', ProductionTermFrame.Unchanged m work work' → S work → S work' := by
    rintro work work' hw ⟨hm, hr⟩
    exact ⟨by simpa only [ProductionTermFrame.mask_eq m work work' hw 1] using hm,
      hR work work' (of_term m work work' hw) hr⟩
  have hf := FixedOutput.hoareTime addTag [] input emitted
    (State m input.length Q.speciesCount i.val s.val (NetworkMembership.currentIndex Q.network i).val mask i.val R)
  have ht := ProductionSelectedTerm.hoareTime m input Q hd i s mask[i.val] [] input (emitted ++ addTag) rfl S hS
  have hi := ProductionIndexAdvance.hoareTime m input.length Q.speciesCount i.val s.val
    (NetworkMembership.currentIndex Q.network i).val mask i.val [] input
    ((emitted ++ addTag) ++ (ProductionSelectedTerm.term mask[i.val] Q i s).code) R hR
  have hm := ProductionMaskAdvance.hoareTime m input.length Q.speciesCount (i.val + 1) s.val
    ((NetworkMembership.currentIndex Q.network i).val + 1) mask i.val [] input
    ((emitted ++ addTag) ++ (ProductionSelectedTerm.term mask[i.val] Q i s).code) R hR
  have hft := seqTM_hoareTime (emitBitsTM addTag) (ProductionSelectedTerm.machine m) hf (by
    rintro inp work out ⟨hc, _, hp⟩
    obtain ⟨hinp, hw, ho⟩ := hc.phase
    rw [hinp, hw, ho]
    exact ⟨hc, ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩, hp.2.2.2.1.read him⟩) ht
  have hfti := seqTM_hoareTime (seqTM (emitBitsTM addTag) (ProductionSelectedTerm.machine m)) (ProductionIndexAdvance.machine m) hft (by
    rintro inp work out ⟨hc, hp, hi, hz, hmask, hr⟩
    obtain ⟨hinp, hw, ho⟩ := hc.phase
    rw [hinp, hw, ho]
    exact ⟨hc, hp, hi, hz, hmask, hr⟩) hi
  have hfull := seqTM_hoareTime (seqTM (seqTM (emitBitsTM addTag) (ProductionSelectedTerm.machine m)) (ProductionIndexAdvance.machine m))
    (ProductionMaskAdvance.machine m) hfti (by
      rintro inp work out ⟨hc, hp⟩
      obtain ⟨hinp, hw, ho⟩ := hc.phase
      rw [hinp, hw, ho]
      exact ⟨hc, hp⟩) hm
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hri : i.val ≤ input.length := by have hir := i.isLt; omega
  have hidx := (NetworkNumbering.decoded_index_bound hd (NetworkMembership.currentIndex Q.network i)).le
  exact hfull.consequence (fun _ _ _ ⟨hc, hp⟩ => ⟨hc, hp.1.safe, hp⟩) (by
    rintro inp work out ⟨hc, hp⟩
    exact ⟨by simpa only [word, List.append_assoc] using hc, hp⟩) (by
      unfold timeBound ProductionSelectedTerm.timeBound ProductionTermOutput.timeBound addTag
      simp only [List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.ProductionReactionStep

#print axioms JointThermoComplexity.Complexity.ProductionReactionStep.hoareTime
