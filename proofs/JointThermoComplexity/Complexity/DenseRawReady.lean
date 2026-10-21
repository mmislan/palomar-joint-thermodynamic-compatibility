module
public import proofs.JointThermoComplexity.Complexity.DenseRawLoaded

set_option autoImplicit false
@[expose] public section

/-! Extract the raw packet references from the physical source loader. Only
present reference slots are asserted to contain canonical binary registers. -/

namespace JointThermoComplexity.Complexity.DenseRawReady
open _root_.Complexity BinaryIncrementRun BoundedOccurrenceMachine

def values (vs : List ℕ) (j : Fin 64) : ℕ :=
  if h : j.val < 2 + vs.length ∧ 2 ≤ j.val then vs[j.val - 2]'(by omega) else 0

theorem values_reference (vs : List ℕ) (hcap : vs.length ≤ 4) (i : Fin vs.length) :
    values vs (DensePowerPorts.reference vs.length hcap i) = vs[i.val] := by
  have hi : 2 + i.val < 2 + vs.length := by omega
  simp [values, DensePowerPorts.reference, hi]

theorem source_get (vs : List ℕ) (hcap : vs.length ≤ 4) (work : Fin 64 → Tape)
    (he : BoundedOccurrenceRun.Encoded DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc vs work)
    (i : Fin vs.length) : Register vs[i.val] (work (DensePowerPorts.reference vs.length hcap i)) := by
  have hm : vs.length ≤ DenseParserPorts.layout.Physical.length := by
    simpa only [SparseOffsetLayout.physical_length] using hcap
  have hh := DensePowerReady.encoded_get DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc vs work hm he i.val i.isLt
  have hp : (DenseParserPorts.layout.Physical[i.val]'(by rw [SparseOffsetLayout.physical_length]; omega)).1 =
      DensePowerPorts.reference vs.length hcap i := by
    have hi4 : i.val < 4 := by omega
    obtain h | h | h | h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    all_goals
      apply Fin.ext
      change _ = 2 + i.val
      simp only [h]
      rfl
  rw [hp] at hh
  exact hh

theorem refs (vs : List ℕ) (hcap : vs.length ≤ 4) (work : Fin 64 → Tape)
    (he : BoundedOccurrenceRun.Encoded DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc vs work)
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

theorem bits (vs : List ℕ) (hcap : vs.length ≤ 4) (B : ℕ) (hbits : ∀ v ∈ vs, v.bits.length ≤ B) :
    ∀ p ∈ (DensePowerPorts.cellLayout vs.length hcap).comparisons, ((values vs) p.constant).bits.length ≤ B := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  change (values vs (DensePowerPorts.reference vs.length hcap i)).bits.length ≤ B
  rw [values_reference]
  exact hbits _ (List.mem_iff_getElem.mpr ⟨i.val, i.isLt, rfl⟩)

def rawValues (input : List Bool) : List ℕ := (BoundedOccurrenceControl.scan 4 input).values
theorem raw_cap (input : List Bool) : (rawValues input).length ≤ 4 := BoundedOccurrenceControl.values_length 4 input

theorem raw_refs (input : List Bool) (m : ℕ) (hchoice : OccurrenceDispatchControl.choice 4 input = some m)
    (work : Fin 64 → Tape)
    (hl : Loaded DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc DenseParserPorts.layout.flag.castSucc input work)
    (hf : ∀ j : Fin 64, 44 ≤ j.val → j.val < 48 → (work j).head = 1) :
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout (rawValues input).length (raw_cap input)) (values (rawValues input)) work := by
  apply refs (rawValues input) (raw_cap input) work _ hf
  exact DenseRawLoaded.encoded_of_choice DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc
    DenseParserPorts.layout.flag.castSucc input work m (by simpa only [SparseOffsetLayout.physical_length] using hchoice) hl

theorem raw_bits (input : List Bool) (L : ℕ) (hlen : input.length ≤ L) :
    ∀ p ∈ (DensePowerPorts.cellLayout (rawValues input).length (raw_cap input)).comparisons,
      ((values (rawValues input)) p.constant).bits.length ≤ L :=
  bits (rawValues input) (raw_cap input) L (fun v hv => (BoundedOccurrenceControl.bits_length 4 input v hv).trans hlen)

end JointThermoComplexity.Complexity.DenseRawReady

#print axioms JointThermoComplexity.Complexity.DenseRawReady.raw_refs
#print axioms JointThermoComplexity.Complexity.DenseRawReady.raw_bits
