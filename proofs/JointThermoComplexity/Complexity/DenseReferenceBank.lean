module
public import proofs.JointThermoComplexity.Complexity.DenseReferenceClear

set_option autoImplicit false
@[expose] public section

/-! A fixed four-reference bank: present raw values remain unchanged and unused
reusable buffers are actually cleared to binary zero before each packet. -/

namespace JointThermoComplexity.Complexity.DenseReferenceBank
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun BoxBufferState

def slots : List (Fin 64) := [2, 3, 4, 5]
def port (i : Fin 4) : Fin 64 := ⟨2 + i.val, by omega⟩
def unused (m : ℕ) : List (Fin 64) := slots.drop m
def machine (m : ℕ) : TM 64 := DenseReferenceClear.machine (unused m)

theorem slot_mem : ∀ i : Fin 4, port i ∈ slots := by decide
theorem unused_mem (m : ℕ) (hm : m ≤ 4) : ∀ i : Fin 4, port i ∈ unused m ↔ m ≤ i.val := by
  interval_cases m <;> decide
theorem unused_nodup (m : ℕ) : (unused m).Nodup :=
  (by decide : slots.Nodup).sublist (List.drop_sublist m slots)

theorem present_away (vs : List ℕ) (hm : vs.length ≤ 4) (i : Fin 4) (hi : i.val < vs.length) : port i ∉ unused vs.length := by
  intro h
  have hh := (unused_mem vs.length hm i).mp h
  omega

def Present (vs : List ℕ) (hm : vs.length ≤ 4) (work : Fin 64 → Tape) : Prop :=
  ∀ i : Fin vs.length, Register vs[i.val] (work (port (i.castLE hm)))
def Kept (L : ℕ) (vs : List ℕ) (hm : vs.length ≤ 4) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Present vs hm work ∧ (∀ i : Fin 4, i.val < vs.length → Reusable L (work (port i))) ∧ R work
def Bank (L : ℕ) (vs : List ℕ) (work : Fin 64 → Tape) : Prop :=
  ∀ i : Fin 4, Register (DenseRawReady.values vs (port i)) (work (port i)) ∧ Reusable L (work (port i))

theorem values_port (vs : List ℕ) (i : Fin 4) :
    DenseRawReady.values vs (port i) = if h : i.val < vs.length then vs[i.val] else 0 := by
  simp [DenseRawReady.values, port]

theorem present_of_encoded (vs : List ℕ) (hm : vs.length ≤ 4) (work : Fin 64 → Tape)
    (he : BoundedOccurrenceRun.Encoded DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc vs work) : Present vs hm work := by
  intro i
  exact DenseRawReady.source_get vs hm work he i

theorem kept_stable (L : ℕ) (vs : List ℕ) (hm : vs.length ≤ 4) (R : (Fin 64 → Tape) → Prop)
    (hR : DenseReferenceClear.Stable (unused vs.length) R) : DenseReferenceClear.Stable (unused vs.length) (Kept L vs hm R) := by
  rintro work next he ⟨hp, hreuse, hr⟩
  refine ⟨?_, ?_, hR work next he hr⟩
  · intro i
    rw [he (port (i.castLE hm)) (present_away vs hm _ i.isLt)]
    exact hp i
  · intro i hi
    rw [he (port i) (present_away vs hm i hi)]
    exact hreuse i hi

theorem hoareTime (L : ℕ) (vs : List ℕ) (hm : vs.length ≤ 4) (before input emitted : List Bool)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseReferenceClear.Stable (unused vs.length) R) :
    (machine vs.length).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        DenseReferenceClear.Ready L slots work ∧ Present vs hm work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Bank L vs work ∧ R work)
      (4 * (12 * L + 10)) := by
  have hh := DenseReferenceClear.hoareTime (unused vs.length) (unused_nodup vs.length) L before input emitted
    (Kept L vs hm R) (kept_stable L vs hm R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hready, hp, hr⟩
    exact ⟨hc, hs, (fun j hj => hready j (List.mem_of_mem_drop hj)), hp,
      (fun i _ => hready (port i) (slot_mem i)), hr⟩
  · rintro inp work out ⟨hc, hs, hz, hp, hreuse, hr⟩
    refine ⟨hc, hs, ?_, hr⟩
    intro i
    by_cases hi : i.val < vs.length
    · let j : Fin vs.length := ⟨i.val, hi⟩
      have hji : j.castLE hm = i := Fin.ext rfl
      refine ⟨?_, hreuse i hi⟩
      rw [values_port, dite_eq_left hi]
      simpa only [hji] using hp j
    · have hmem := (unused_mem vs.length hm i).mpr (by omega)
      have hh := hz (port i) hmem
      rw [values_port, dite_eq_right hi]
      exact hh
  · have hlen : (unused vs.length).length ≤ 4 := by
      simp only [unused, List.length_drop, slots, List.length_cons, List.length_nil]
      omega
    exact Nat.mul_le_mul_right _ hlen

theorem refs (L : ℕ) (vs : List ℕ) (work : Fin 64 → Tape) (hb : Bank L vs work)
    (hf : ∀ j : Fin 64, 44 ≤ j.val → j.val < 48 → (work j).head = 1) :
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout 4 (by decide)) (DenseRawReady.values vs) work := by
  apply DensePowerPorts.refs
  · intro i
    exact (hb i).1
  · intro i
    apply hf
    · change 44 ≤ 44 + i.val; omega
    · change 44 + i.val < 48; omega

theorem bits (vs : List ℕ) (B : ℕ) (hbits : ∀ v ∈ vs, v.bits.length ≤ B) :
    ∀ p ∈ (DensePowerPorts.cellLayout 4 (by decide)).comparisons, ((DenseRawReady.values vs) p.constant).bits.length ≤ B := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  change (DenseRawReady.values vs (port i)).bits.length ≤ B
  rw [values_port]
  split
  · rename_i hi
    exact hbits _ (List.mem_iff_getElem.mpr ⟨i.val, hi, rfl⟩)
  · simp only [Nat.zero_bits, List.length_nil]
    omega

end JointThermoComplexity.Complexity.DenseReferenceBank

#print axioms JointThermoComplexity.Complexity.DenseReferenceBank.hoareTime
#print axioms JointThermoComplexity.Complexity.DenseReferenceBank.refs
