module
public import proofs.JointThermoComplexity.Complexity.ReactionPrefixFrame
public import proofs.JointThermoComplexity.Complexity.CurrentAddress
public import proofs.JointThermoComplexity.Complexity.CurrentEquationOutput

set_option autoImplicit false
@[expose] public section

/-! One actual record rescan emits its right-nested current equation, with exact denominator and output address. -/

namespace JointThermoComplexity.Complexity.CurrentRecord
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CircuitSerialization

variable {n arity : ℕ}

def values (m : ℕ) (current result : Fin arity) (j : Fin (m + 15)) : Fin arity :=
  if j = species (m + 1) then current else result

theorem values_current (m : ℕ) (current result : Fin arity) : values m current result (species (m + 1)) = current := by
  simp [values]

theorem values_result (m : ℕ) (current result : Fin arity) : values m current result (previous (m + 1)) = result :=
  ite_eq_right (previous_ne_species (m + 1))

def clause (m : ℕ) : TM (m + 15) := seqTM (emitBitsTM conjunctionTag)
  (CurrentEquationOutput.machine (scratch (m + 2)) (species (m + 1)) (previous (m + 1)))

def machine (m : ℕ) : TM (m + 15) := seqTM (ReactionPrefixCount.machine (speciesOld m))
  (seqTM (CurrentAddress.machine m) (clause m))

def word (q : ReactionCircuit.Reaction n) (current result : Fin arity) : List Bool :=
  conjunctionTag ++ (CurrentEquationOutput.equation q.denominator current result).code

def timeBound (L : ℕ) : ℕ := 66 * L ^ 2 + 156 * L + 113

theorem hoareTime (m L count old : ℕ) (q : ReactionCircuit.Reaction n) (current result : Fin arity)
    (ha : arity ≤ 4 * L) (hn : n ≤ L) (hold : old ≤ 4 * L)
    (hlen : ((DataCodec.reaction n).code q).length ≤ L)
    (hresult : result.val + 1 = count + ExactGateCount.reactionCost q)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
        IsReg count (work (raw m)) ∧ IsReg old (work (previous (m + 1))) ∧
        IsReg current.val (work (species (m + 1))) ∧ IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work)
      (fun inp work out => Cursor (before ++ (DataCodec.reaction n).code q) tail (emitted ++ word q current result) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
        IsReg (count + ExactGateCount.reactionCost q) (work (raw m)) ∧ IsReg result.val (work (previous (m + 1))) ∧
        IsReg current.val (work (species (m + 1))) ∧ IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work)
      (timeBound L) := by
  have hbudget : count + ExactGateCount.reactionCost q ≤ 4 * L := by have hi := result.isLt; omega
  have hden : (BitCodec.naturalCode q.denominator).length ≤ L :=
    (ReactionTallyData.component_lengths q).2.2.2.trans hlen
  let P : (Fin (m + 15) → Tape) → Prop := fun work =>
    BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ IsReg old (work (previous (m + 1))) ∧
    IsReg current.val (work (species (m + 1))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountAppend.destination → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, hp, hi, hr⟩
    exact ⟨by simpa only [hw _ (raw_ne_scratch m).symm] using hz,
      by simpa only [hw _ (raw_ne_previous m).symm] using hp,
      by simpa only [hw _ (raw_ne_current m).symm] using hi,
      hR work work' (fun j hj _ => hw j hj) hr⟩
  have ht := ReactionPrefixFrame.hoareTime (speciesOld m) q L count hn hlen hbudget before
    (BitCodec.naturalCode q.denominator ++ tail) emitted P hP
  let S : (Fin (m + 15) → Tape) → Prop := fun work =>
    IsReg current.val (work (species (m + 1))) ∧ IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ previous (m + 1) → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hi, hf, hr⟩
    exact ⟨by simpa only [hw _ (previous_ne_species (m + 1)).symm] using hi,
      by simpa only [hw _ (MonomialFuel.slot_separate (m + 1)).previous] using hf,
      hR work work' (fun j _ hj => hw j hj) hr⟩
  have haddr := CurrentAddress.hoareTime m L old result.val hold (by omega)
    (before ++ ReactionPrefixTally.word q) (BitCodec.naturalCode q.denominator ++ tail) emitted S hS
  let T : (Fin (m + 15) → Tape) → Prop := fun work =>
    IsReg (count + ExactGateCount.reactionCost q) (work (raw m)) ∧ IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work
  have htag := FixedOutput.hoareTime conjunctionTag (before ++ ReactionPrefixTally.word q)
    (BitCodec.naturalCode q.denominator ++ tail) emitted (fun work =>
      BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ IsReg current.val (work (species (m + 1))) ∧
      IsReg result.val (work (previous (m + 1))) ∧ T work)
  have heq := CurrentEquationOutput.hoareTime (scratch (m + 2)) (species (m + 1)) (previous (m + 1))
    (species_ne_scratch (m + 1)) (previous_ne_scratch (m + 1)) (values m current result) q.denominator
    (before ++ ReactionPrefixTally.word q) tail (emitted ++ conjunctionTag) T
  simp only [values_current, values_result] at heq
  have hclause := seqTM_hoareTime (emitBitsTM conjunctionTag)
    (CurrentEquationOutput.machine (scratch (m + 2)) (species (m + 1)) (previous (m + 1))) htag (by
      intro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) heq
  have hrest := seqTM_hoareTime (CurrentAddress.machine m) (clause m) haddr (by
    rintro inp work out ⟨hc, hs, hz, hn, hp, hi, hf, hr⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hs, hz, hi, hp, by simpa only [hresult, CurrentPorts.raw] using hn, hf, hr⟩) hclause
  have hfull := seqTM_hoareTime (ReactionPrefixCount.machine (speciesOld m))
    (seqTM (CurrentAddress.machine m) (clause m)) ht (by
      rintro inp work out ⟨hc, hs, hn, hf, hz, hp, hi, hr⟩
      obtain ⟨hip, hw, ho⟩ := hc.phase
      rw [hip, hw, ho]
      exact ⟨hc, hs, hz, by simpa only [hresult, CurrentPorts.raw] using hn, hp, hi, hf, hr⟩) hrest
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, hz, hn, hp, hi, hf, hr⟩
    exact ⟨by simpa only [ReactionPrefixTally.record_split, List.append_assoc] using hc, hs, hn, hf, hz, hp, hi, hr⟩) (by
      rintro inp work out ⟨hc, hs, hz, hi, hp, hn, hf, hr⟩
      exact ⟨by simpa only [ReactionPrefixTally.record_split, word, List.append_assoc] using hc, hs, hz, hn, hp, hi, hf, hr⟩) (by
        have he := CurrentEquationOutput.decoded_bound current.val result.val q.denominator L
          (current.isLt.le.trans ha) (result.isLt.le.trans ha) hden
        unfold timeBound ReactionPrefixCount.timeBound
        simp only [conjunctionTag, List.length_cons, List.length_nil]
        omega)

end JointThermoComplexity.Complexity.CurrentRecord

#print axioms JointThermoComplexity.Complexity.CurrentRecord.hoareTime
