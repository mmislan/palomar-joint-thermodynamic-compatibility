module
public import proofs.JointThermoComplexity.Complexity.DensePowerPorts

set_option autoImplicit false
@[expose] public section

/-! Only present encoded source occurrences supply canonical reference buffers. -/

namespace JointThermoComplexity.Complexity.DensePowerReady
open _root_.Complexity BinaryIncrementRun BoundedOccurrenceMachine
variable {w n : ℕ}

theorem encoded_get (slots : List (Port w)) (ending : Fin (w + 1)) (vs : List ℕ)
    (work : Fin (w + 1) → Tape) (hcap : vs.length ≤ slots.length)
    (he : BoundedOccurrenceRun.Encoded slots ending vs work) (i : ℕ) (hi : i < vs.length) :
    Register vs[i] (work (slots[i]'(by omega)).1) := by
  induction slots generalizing vs i with
  | nil => simp only [List.length_nil] at hcap; omega
  | cons p rest ih =>
    cases vs with
    | nil => simp only [List.length_nil] at hi; omega
    | cons v vs =>
      cases i with
      | zero => exact he.2.1
      | succ i =>
        exact ih vs (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hcap)
          he.2.2 i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

def values (vs : List (Fin n)) (j : Fin 64) : ℕ :=
  if h : j.val < 2 + vs.length ∧ 2 ≤ j.val then (vs[j.val - 2]'(by omega)).val else 0

theorem values_reference (vs : List (Fin n)) (hcap : vs.length ≤ 4) (i : Fin vs.length) :
    values vs (DensePowerPorts.reference vs.length hcap i) = vs[i.val].val := by
  have hi : 2 + i.val < 2 + vs.length := by omega
  simp [values, DensePowerPorts.reference, hi]

theorem source_get (vs : List (Fin n)) (hcap : vs.length ≤ 4) (work : Fin 64 → Tape)
    (he : BoundedOccurrenceRun.Encoded DenseParserPorts.layout.Physical
      DenseParserPorts.layout.ending.castSucc (vs.map Fin.val) work) (i : Fin vs.length) :
    Register vs[i.val].val (work (DensePowerPorts.reference vs.length hcap i)) := by
  have hm : (vs.map Fin.val).length ≤ DenseParserPorts.layout.Physical.length := by
    simpa only [List.length_map, SparseOffsetLayout.physical_length] using hcap
  have hi : i.val < (vs.map Fin.val).length := by simpa only [List.length_map] using i.isLt
  have hh := encoded_get DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc
    (vs.map Fin.val) work hm he i.val hi
  have hp : (DenseParserPorts.layout.Physical[i.val]'(by
      rw [SparseOffsetLayout.physical_length]; omega)).1 = DensePowerPorts.reference vs.length hcap i := by
    have hi4 : i.val < 4 := by omega
    obtain h | h | h | h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    all_goals
      apply Fin.ext
      change _ = 2 + i.val
      simp only [h]
      rfl
  rw [hp] at hh
  simpa only [List.getElem_map] using hh

theorem refs (vs : List (Fin n)) (hcap : vs.length ≤ 4) (work : Fin 64 → Tape)
    (he : BoundedOccurrenceRun.Encoded DenseParserPorts.layout.Physical
      DenseParserPorts.layout.ending.castSucc (vs.map Fin.val) work)
    (hf : ∀ j : Fin 64, 44 ≤ j.val → j.val < 48 → (work j).head = 1) :
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout vs.length hcap) (values vs) work := by
  apply DensePowerPorts.refs
  · intro i
    rw [values_reference]
    exact source_get vs hcap work he i
  · intro i
    apply hf
    · change 44 ≤ 44 + i.val; omega
    · change 44 + i.val < 48; omega

theorem bits (vs : List (Fin n)) (hcap : vs.length ≤ 4) (B : ℕ)
    (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B) :
    ∀ p ∈ (DensePowerPorts.cellLayout vs.length hcap).comparisons, ((values vs) p.constant).bits.length ≤ B := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  change (values vs (DensePowerPorts.reference vs.length hcap i)).bits.length ≤ B
  rw [values_reference]
  exact hbits i

end JointThermoComplexity.Complexity.DensePowerReady

#print axioms JointThermoComplexity.Complexity.DensePowerReady.encoded_get
#print axioms JointThermoComplexity.Complexity.DensePowerReady.refs
#print axioms JointThermoComplexity.Complexity.DensePowerReady.bits
