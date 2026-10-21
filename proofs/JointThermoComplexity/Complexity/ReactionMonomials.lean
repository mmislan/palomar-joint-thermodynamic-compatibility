module
public import proofs.JointThermoComplexity.Complexity.ReactionSave
public import proofs.JointThermoComplexity.Complexity.MonomialDenseBuild

set_option autoImplicit false
@[expose] public section

/-! Compute both literal monomials in record order while preserving the first result address. -/

namespace JointThermoComplexity.Complexity.ReactionMonomials
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel ReactionPorts
open RealCircuit CircuitSerialization PowerAddressCircuit FiniteCodec

def left {n k : ℕ} (c : Circuit n k) (γ : Fin n → ℕ) : MonomialCircuit.State n :=
  MonomialCircuit.build c (MonomialCircuit.denseTerms γ)

def right {n k : ℕ} (c : Circuit n k) (γ δ : Fin n → ℕ) : MonomialCircuit.State n :=
  MonomialCircuit.build (left c γ).circuit (MonomialCircuit.denseTerms δ)

def first (m : ℕ) : TM (m + 15) :=
  seqTM (MonomialBuild.machine (m + 1) (slot (m + 1))) (ReactionSave.machine m)

def machine (m : ℕ) : TM (m + 15) := seqTM (first m) (MonomialBuild.machine (m + 1) (slot (m + 1)))

def timeBound (L : ℕ) : ℕ := 384 * L ^ 4 + 1104 * L ^ 3 + 1224 * L ^ 2 + 650 * L + 143

theorem hoareTime {n k : ℕ} (m L offset arity old idx oldSaved : ℕ) (ha : arity ≤ 4 * L)
    (hold : old ≤ 4 * L) (hidx : idx ≤ L) (hsaved : oldSaved ≤ 4 * L)
    (c : Circuit n k) (γ δ : Fin n → ℕ) (inputs : Fin n → Fin arity)
    (hinputs : ∀ i, (inputs i).val = i.val) (h : offset + (right c γ δ).size ≤ arity)
    (hcount : n ≤ L) (hγ : ∀ i, (γ i).bits.length ≤ L) (hδ : ∀ i, (δ i).bits.length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((functionCode natural γ ++ functionCode natural δ) ++ tail)
        (initial ++ equationStream c inputs (index offset k arity (by
          have hl := MonomialCircuit.build_size_ge c (MonomialCircuit.denseTerms γ)
          have hr := MonomialCircuit.build_size_ge (left c γ).circuit (MonomialCircuit.denseTerms δ)
          change k ≤ (left c γ).size at hl
          change (left c γ).size ≤ (right c γ δ).size at hr
          omega))) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
        IsReg (offset + k) (work (next (m + 2))) ∧ IsReg old (work (previous (m + 1))) ∧
        Temps (m + 1) L work ∧ IsReg idx (work (species (m + 1))) ∧ IsReg n (work (slot (m + 1))) ∧
        IsReg oldSaved (work (saved m)) ∧ R work)
      (fun inp work out => Cursor (before ++ (functionCode natural γ ++ functionCode natural δ)) tail
        (initial ++ equationStream (right c γ δ).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready (m + 1) L offset (right c γ δ) n R work ∧ IsReg n (work (slot (m + 1))) ∧
        IsReg (offset + (left c γ).accumulator.val) (work (saved m))) (timeBound L) := by
  have hlr : (left c γ).size ≤ (right c γ δ).size :=
    MonomialCircuit.build_size_ge (left c γ).circuit (MonomialCircuit.denseTerms δ)
  have hl : offset + (left c γ).size ≤ arity := by omega
  have hleft : offset + (left c γ).accumulator.val ≤ 4 * L := by
    have hi := (left c γ).accumulator.isLt
    omega
  let P : (Fin (m + 15) → Tape) → Prop := fun work => IsReg oldSaved (work (saved m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hs, hr⟩
    have he := hw (saved m) (saved_ne_next m) (saved_ne_accumulator m) (saved_ne_power m)
      (saved_ne_flag m) (saved_ne_previous m) (saved_ne_species m)
    exact ⟨by simpa only [he] using hs, hR work work' (fun j hn ha hp hf ho hi _ => hw j hn ha hp hf ho hi) hr⟩
  have hfirst := MonomialDenseBuild.hoareTime (m + 1) L offset arity old idx ha hold hidx c γ inputs hinputs hl
    hcount hγ before (functionCode natural δ ++ tail) initial P hP
  let S : (Fin (m + 15) → Tape) → Prop := fun work => IsReg n (work (slot (m + 1))) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ saved m → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw _ (saved_ne_fuel m).symm] using hf,
      hR work work' (fun j _ _ _ _ _ _ hj => hw j hj) hr⟩
  have hsave := ReactionSave.hoareTime m L offset n oldSaved (left c γ) hsaved hleft
    (before ++ functionCode natural γ) (functionCode natural δ ++ tail)
    (initial ++ equationStream (left c γ).circuit inputs (index offset _ arity hl)) S hS
  have hs1 := seqTM_hoareTime (MonomialBuild.machine (m + 1) (slot (m + 1))) (ReactionSave.machine m) hfirst (by
    rintro inp work out ⟨hc, ⟨hs, hi, hz, hn, hp, ht, ho, hr⟩, hf⟩
    obtain ⟨hip, hw, hout⟩ := hc.phase
    rw [hip, hw, hout]
    exact ⟨hc, ⟨hs, hi, hz, hn, hp, ht, hf, hr⟩, ho⟩) hsave
  let T : (Fin (m + 15) → Tape) → Prop := fun work => IsReg (offset + (left c γ).accumulator.val) (work (saved m)) ∧ R work
  have hT : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → work' j = work j) → T work → T work' := by
    rintro work work' hw ⟨hs, hr⟩
    have he := hw (saved m) (saved_ne_next m) (saved_ne_accumulator m) (saved_ne_power m)
      (saved_ne_flag m) (saved_ne_previous m) (saved_ne_species m)
    exact ⟨by simpa only [he] using hs, hR work work' (fun j hn ha hp hf ho hi _ => hw j hn ha hp hf ho hi) hr⟩
  have hsecond := MonomialDenseBuild.hoareTime (m + 1) L offset arity (offset + (left c γ).accumulator.val) n
    ha hleft hcount (left c γ).circuit δ inputs hinputs h hcount hδ (before ++ functionCode natural γ) tail initial T hT
  have hseq := seqTM_hoareTime (first m) (MonomialBuild.machine (m + 1) (slot (m + 1))) hs1 (by
    rintro inp work out ⟨hc, ⟨hs, hi, hz, hn, hp, ht, hf, hr⟩, ho⟩
    obtain ⟨hip, hw, hout⟩ := hc.phase
    rw [hip, hw, hout]
    exact ⟨hc, hs, hz, hn, hp, ht, hi, hf, ho, hr⟩) hsecond
  exact hseq.consequence (by
    intro inp work out hp
    rw [List.append_assoc] at hp
    exact hp) (by
    rintro inp work out ⟨hc, ⟨hs, hi, hz, hn, hp, ht, ho, hr⟩, hf⟩
    rw [List.append_assoc] at hc
    exact ⟨hc, ⟨hs, hi, hz, hn, hp, ht, hr⟩, hf, ho⟩)
    (by unfold timeBound MonomialBuild.timeBound; omega)

end JointThermoComplexity.Complexity.ReactionMonomials

#print axioms JointThermoComplexity.Complexity.ReactionMonomials.hoareTime
