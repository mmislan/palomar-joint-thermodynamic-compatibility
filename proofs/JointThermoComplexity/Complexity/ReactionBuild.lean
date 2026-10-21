module
public import proofs.JointThermoComplexity.Complexity.ReactionMonomials
public import proofs.JointThermoComplexity.Complexity.ReactionTail
public import proofs.JointThermoComplexity.Complexity.ReactionBuildCode

set_option autoImplicit false
@[expose] public section

/-! The complete actual literal reaction routine consumes one record and appends its exact circuit equations. -/

namespace JointThermoComplexity.Complexity.ReactionBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel ReactionPorts
open RealCircuit CircuitSerialization PowerAddressCircuit ReactionMonomials

def monomialView {n : ℕ} (s : ReactionCircuit.State n) : MonomialCircuit.State n := ⟨s.size, s.circuit, s.output⟩

def machine (m : ℕ) : TM (m + 15) := seqTM (ReactionMonomials.machine m) (ReactionTail.machine m)

def timeBound (L : ℕ) : ℕ := 384 * L ^ 4 + 1104 * L ^ 3 + 1512 * L ^ 2 + 1228 * L + 447

theorem hoareTime {n k : ℕ} (m L offset arity old idx oldSaved : ℕ) (ha : arity ≤ 4 * L)
    (hold : old ≤ 4 * L) (hidx : idx ≤ L) (hsaved : oldSaved ≤ 4 * L)
    (c : Circuit n k) (q : ReactionCircuit.Reaction n) (inputs : Fin n → Fin arity)
    (hinputs : ∀ i, (inputs i).val = i.val) (h : offset + (ReactionCircuit.build c q).size ≤ arity)
    (hcount : n ≤ L) (hreactant : ∀ i, (q.reactant i).bits.length ≤ L) (hproduct : ∀ i, (q.product i).bits.length ≤ L)
    (hnum : (BitCodec.naturalCode q.numerator).length ≤ L) (hden : (BitCodec.naturalCode q.denominator).length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail)
        (initial ++ equationStream c inputs (index offset k arity (by have hs := ReactionCircuit.build_size_ge c q; omega))) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
        IsReg (offset + k) (work (next (m + 2))) ∧ IsReg old (work (previous (m + 1))) ∧
        Temps (m + 1) L work ∧ IsReg idx (work (species (m + 1))) ∧ IsReg n (work (slot (m + 1))) ∧
        IsReg oldSaved (work (saved m)) ∧ R work)
      (fun inp work out => Cursor (before ++ (DataCodec.reaction n).code q) tail
        (initial ++ equationStream (ReactionCircuit.build c q).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready (m + 1) L offset (monomialView (ReactionCircuit.build c q)) n R work ∧
        IsReg n (work (slot (m + 1))) ∧ IsReg (offset + (right c q.reactant q.product).size + 2) (work (saved m)))
      (timeBound L) := by
  have hroom : offset + (right c q.reactant q.product).size + 3 < arity := by
    rw [ReactionBuildCode.size] at h
    omega
  have hp : offset + (right c q.reactant q.product).accumulator.val < arity := by
    have hi := (right c q.reactant q.product).accumulator.isLt
    omega
  have hl : offset + (left c q.reactant).accumulator.val < arity := by
    have hi := (left c q.reactant).accumulator.isLt
    have hs := MonomialCircuit.build_size_ge (left c q.reactant).circuit (MonomialCircuit.denseTerms q.product)
    change (left c q.reactant).size ≤ (right c q.reactant q.product).size at hs
    omega
  let target : Fin arity := ⟨offset + (right c q.reactant q.product).size, by omega⟩
  let prev : Fin arity := ⟨offset + (right c q.reactant q.product).accumulator.val, hp⟩
  let keep : Fin arity := ⟨offset + (left c q.reactant).accumulator.val, hl⟩
  have hright : offset + (right c q.reactant q.product).size ≤ arity := by omega
  have hpair := ReactionMonomials.hoareTime m L offset arity old idx oldSaved ha hold hidx hsaved c q.reactant q.product
    inputs hinputs hright hcount hreactant hproduct before
    ((BitCodec.naturalCode q.numerator ++ BitCodec.naturalCode q.denominator) ++ tail) initial R hR
  let S : (Fin (m + 15) → Tape) → Prop := fun work =>
    IsReg n (work (species (m + 1))) ∧ Temps (m + 1) L work ∧ IsReg n (work (slot (m + 1))) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → j ≠ saved m →
      work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hi, ⟨a, p, ha, hp, har, hpr⟩, hf, hr⟩
    refine ⟨?_, ⟨a, p, ha, hp, ?_, ?_⟩, ?_, hR work work' (fun j hn _ _ _ ho _ hs => hw j hn ho hs) hr⟩
    · simpa only [hw _ (species_ne_next (m + 1)) (previous_ne_species (m + 1)).symm (saved_ne_species m).symm] using hi
    · simpa only [hw _ (next_ne_accumulator (m + 2)).symm (previous_ne_accumulator (m + 1)).symm (saved_ne_accumulator m).symm] using har
    · simpa only [hw _ (next_ne_power (m + 2)).symm (previous_ne_power (m + 1)).symm (saved_ne_power m).symm] using hpr
    · simpa only [hw _ (slot_separate (m + 1)).next (slot_separate (m + 1)).previous (saved_ne_fuel m).symm] using hf
  have htail := ReactionTail.hoareTime m arity L ha target prev keep q.numerator q.denominator hroom hnum hden
    (before ++ (FiniteCodec.functionCode FiniteCodec.natural q.reactant ++ FiniteCodec.functionCode FiniteCodec.natural q.product))
    tail (initial ++ equationStream (right c q.reactant q.product).circuit inputs (index offset _ arity hright)) S hS
  have hseq := seqTM_hoareTime (ReactionMonomials.machine m) (ReactionTail.machine m) hpair (by
    rintro inp work out ⟨hc, ⟨hs, hi, hz, hn, hp, ht, hr⟩, hf, hk⟩
    obtain ⟨hip, hw, hout⟩ := hc.phase
    rw [hip, hw, hout]
    exact ⟨hc, hs, hz, hn, hp, hk, hi, ht, hf, hr⟩) htail
  exact hseq.consequence (by
    intro inp work out hp
    simpa only [ReactionBuildCode.record_code, List.append_assoc] using hp) (by
    rintro inp work out ⟨hc, hs, hz, hn, hp, hk, hi, ht, hf, hr⟩
    refine ⟨?_, ⟨hs, hi, hz, ?_, ?_, ht, hr⟩, hf, hk⟩
    · rw [ReactionBuildCode.stream offset arity c q inputs h]
      simpa only [ReactionBuildCode.record_code, target, prev, keep, List.append_assoc] using hc
    · simpa only [target, monomialView, ReactionBuildCode.size, Nat.add_assoc] using hn
    · simpa only [target, monomialView, ReactionBuildCode.output_value, Nat.add_assoc] using hp)
    (by unfold timeBound ReactionMonomials.timeBound; omega)

end JointThermoComplexity.Complexity.ReactionBuild

#print axioms JointThermoComplexity.Complexity.ReactionBuild.hoareTime
