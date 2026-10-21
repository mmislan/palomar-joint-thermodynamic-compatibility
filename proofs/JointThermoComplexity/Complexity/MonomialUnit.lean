module
public import proofs.JointThermoComplexity.Complexity.MonomialReady
public import proofs.JointThermoComplexity.Complexity.UnitGateStore
public import proofs.JointThermoComplexity.Complexity.UnitCircuitCode
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Actual unit initialization preserves bounded temporary power addresses and the species cursor. -/

namespace JointThermoComplexity.Complexity.MonomialUnit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady RealCircuit CircuitSerialization PowerAddressCircuit

def machine (m : ℕ) : TM (m + 14) :=
  UnitGateStore.machine (resultPermutation m) (nextOld (m + 1)) (scratchOld (m + 1))

theorem hoareTime {n k : ℕ} (m L offset arity old idx : ℕ) (ha : arity ≤ 4 * L) (hold : old ≤ 4 * L)
    (c : Circuit n k) (inputs : Fin n → Fin arity) (h : offset + (k + 1) ≤ arity)
    (before input initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ previous m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input
        (initial ++ equationStream c inputs (index offset k arity (by omega))) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 1))) ∧
        IsReg (offset + k) (work (next (m + 1))) ∧ IsReg old (work (previous m)) ∧
        Temps m L work ∧ IsReg idx (work (species m)) ∧ R work)
      (fun inp work out => Cursor before input
        (initial ++ equationStream (MonomialCircuit.start c).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (MonomialCircuit.start c) idx R work) (32 * L ^ 2 + 84 * L + 54) := by
  have hn : offset + k < arity := by omega
  have hne : GateStore.next (resultPermutation m) (nextOld (m + 1)) ≠
      GateStore.scratch (resultPermutation m) (scratchOld (m + 1)) := by
    simpa only [result_next, result_scratch] using next_ne_scratch (m + 1)
  let P : (Fin (m + 14) → Tape) → Prop := fun work => Temps m L work ∧ IsReg idx (work (species m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ GateStore.next (resultPermutation m) (nextOld (m + 1)) →
      j ≠ CountSumAt.destination (resultPermutation m) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨⟨a, p, ha, hp, har, hpr⟩, hi, hr⟩
    have hw' : ∀ j, j ≠ next (m + 1) → j ≠ previous m → work' j = work j := by
      simpa only [result_next, result_destination] using hw
    refine ⟨⟨a, p, ha, hp, ?_, ?_⟩, ?_, hR work work' hw' hr⟩
    · simpa only [hw' _ (next_ne_accumulator (m + 1)).symm (previous_ne_accumulator m).symm] using har
    · simpa only [hw' _ (next_ne_power (m + 1)).symm (previous_ne_power m).symm] using hpr
    · simpa only [hw' _ (species_ne_next m) (previous_ne_species m).symm] using hi
  have hu := UnitGateStore.hoareTime (resultPermutation m) (nextOld (m + 1)) (scratchOld (m + 1)) hne
    (⟨offset + k, hn⟩ : Fin arity) old before input
    (initial ++ equationStream c inputs (index offset k arity (by omega))) P hP
  simp only [result_next, result_scratch, result_destination, P] at hu
  have hb := TemplateRuntime.variable_bound (v := offset + k) (L := L) (by omega)
  exact hu.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hs, hz, hn, hp, ht, hi, hr⟩
    refine ⟨?_, hs, hi, hz, ?_, ?_, ht, hr⟩
    · change Cursor before input (initial ++ equationStream (c.snoc (.constant 1)) inputs (index offset (k + 1) arity h)) inp work out
      rw [UnitCircuitCode.snoc_stream offset arity c inputs h]
      simpa only [List.append_assoc] using hc
    · simpa only [MonomialCircuit.start, Nat.add_assoc] using hn
    · simpa only [MonomialCircuit.start, Fin.val_last] using hp)
    (by unfold UnitGateStore.timeBound; omega)

end JointThermoComplexity.Complexity.MonomialUnit

#print axioms JointThermoComplexity.Complexity.MonomialUnit.hoareTime
