module
public import proofs.JointThermoComplexity.Complexity.MonomialStart
public import proofs.JointThermoComplexity.Complexity.MonomialLoopEntry

set_option autoImplicit false
@[expose] public section

/-! A complete actual monomial routine initializes the empty product and traverses every encoded exponent. -/

namespace JointThermoComplexity.Complexity.MonomialBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel MonomialTraversal
open RealCircuit CircuitSerialization PowerAddressCircuit

def machine (m : ℕ) (r : Fin (m + 14)) : TM (m + 14) :=
  seqTM (MonomialStart.machine m) (MonomialLoop.machine m r)

def timeBound (L : ℕ) : ℕ := 192 * L ^ 4 + 552 * L ^ 3 + 612 * L ^ 2 + 311 * L + 63

theorem hoareTime {n k : ℕ} (m L offset arity old idx : ℕ) (ha : arity ≤ 4 * L)
    (hold : old ≤ 4 * L) (hidx : idx ≤ L) (r : Fin (m + 14)) (sep : Separate m r)
    (c : Circuit n k) (items : List (Fin n × ℕ)) (inputs : Fin n → Fin arity)
    (h : offset + (MonomialCircuit.build c items).size ≤ arity) (hcount : items.length ≤ L)
    (hbits : ∀ item ∈ items, item.2.bits.length ≤ L)
    (hsource : ∀ i (hi : i < items.length), (inputs items[i].1).val = i)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → R work → R work') :
    (machine m r).HoareTime
      (fun inp work out => Cursor before (code items ++ tail)
        (initial ++ equationStream c inputs (index offset k arity
          (by have hs := MonomialCircuit.build_size_ge c items; omega))) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 1))) ∧
        IsReg (offset + k) (work (next (m + 1))) ∧ IsReg old (work (previous m)) ∧
        Temps m L work ∧ IsReg idx (work (species m)) ∧ IsReg items.length (work r) ∧ R work)
      (fun inp work out => Cursor (before ++ code items) tail
        (initial ++ equationStream (MonomialCircuit.build c items).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (MonomialCircuit.build c items) items.length R work ∧ IsReg items.length (work r))
      (timeBound L) := by
  have hs : k + 1 ≤ (MonomialCircuit.build c items).size := (MonomialCircuit.start c).runTerms_size_ge items
  have hstart : offset + (k + 1) ≤ arity := by omega
  let P : (Fin (m + 14) → Tape) → Prop := fun work => IsReg items.length (work r) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw r sep.next sep.previous sep.species] using hf,
      hR work work' (fun j hn _ _ _ hp hi => hw j hn hp hi) hr⟩
  have hinit := MonomialStart.hoareTime m L offset arity old idx ha hold hidx c inputs hstart before
    (code items ++ tail) initial P hP
  have hloop := MonomialLoopEntry.hoareTime m L offset arity ha r sep (MonomialCircuit.start c)
    items inputs h hcount hbits hsource before tail initial R hR
  have hseq := seqTM_hoareTime (MonomialStart.machine m) (MonomialLoop.machine m r) hinit (by
    rintro inp work out ⟨hc, hs, hi, hz, hn, hp, ht, hf, hr⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, ⟨hs, hi, hz, hn, hp, ht, hr⟩, hf⟩) hloop
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp)
    (by unfold timeBound MonomialStart.timeBound; omega)

end JointThermoComplexity.Complexity.MonomialBuild

#print axioms JointThermoComplexity.Complexity.MonomialBuild.hoareTime
