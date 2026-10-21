module
public import proofs.JointThermoComplexity.Complexity.EquationCoefficientControl
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceValue

set_option autoImplicit false
@[expose] public section

/-! Finite signed coefficient catalog and exact encoded-word comparison.
Only canonical coefficient words are claimed to be distinguished by this test.
-/

namespace JointThermoComplexity.Complexity.SmallCoefficientTable

def coefficient (i : Fin 11) : ℤ := (i.val : ℤ) - 5
def catalog : List ℤ := List.ofFn coefficient

def equalCode (bits : List Bool) (z : ℤ) : Bool :=
  (!(BinaryDifference.subtract bits (BitCodec.integerCode z) false).2) &&
    (!(BinaryDifference.subtract (BitCodec.integerCode z) bits false).2)

def select (bits : List Bool) (f : ℤ → List Bool) (fallback : List Bool) : List ℤ → List Bool
  | [] => fallback
  | z :: rest => if equalCode bits z then f z else select bits f fallback rest

theorem coefficient_bound (i : Fin 11) : (coefficient i).natAbs ≤ 5 := by
  have h : ∀ j : Fin 11, (coefficient j).natAbs ≤ 5 := by decide
  exact h i

theorem index_of_small (z : ℤ) (hz : z.natAbs ≤ 5) : ∃ i : Fin 11, coefficient i = z := by
  cases z with
  | ofNat k =>
    have hk : k ≤ 5 := by simpa using hz
    refine ⟨⟨k + 5, by omega⟩, ?_⟩
    simp [coefficient]
  | negSucc k =>
    have hk : k ≤ 4 := by change k + 1 ≤ 5 at hz; omega
    refine ⟨⟨4 - k, by omega⟩, ?_⟩
    simp only [coefficient, Nat.cast_sub hk, Nat.cast_ofNat, Int.negSucc_eq]
    omega

theorem mem_catalog (z : ℤ) (hz : z.natAbs ≤ 5) : z ∈ catalog := by
  obtain ⟨i, rfl⟩ := index_of_small z hz
  simp only [catalog, List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem catalog_bound (z : ℤ) (hz : z ∈ catalog) : z.natAbs ≤ 5 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact coefficient_bound i

theorem catalog_length : catalog.length = 11 := by simp only [catalog, List.length_ofFn]

theorem word_bound (z : ℤ) (hz : z.natAbs ≤ 5) : (BitCodec.integerCode z).length ≤ 8 := by
  obtain ⟨i, rfl⟩ := index_of_small z hz
  have h : ∀ j : Fin 11, (BitCodec.integerCode (coefficient j)).length ≤ 8 := by decide
  exact h i

theorem equalCode_true_iff (bits : List Bool) (z : ℤ) :
    equalCode bits z = true ↔ BinaryDifference.value bits = BinaryDifference.value (BitCodec.integerCode z) := by
  have hnot (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide
  simp only [equalCode, Bool.and_eq_true, hnot]
  have h1 := BinaryDifferenceValue.borrow_iff bits (BitCodec.integerCode z)
  have h2 := BinaryDifferenceValue.borrow_iff (BitCodec.integerCode z) bits
  constructor
  · rintro ⟨hxy, hyx⟩
    simp only [hxy, Bool.false_eq_true, false_iff] at h1
    simp only [hyx, Bool.false_eq_true, false_iff] at h2
    omega
  · intro he
    constructor
    · cases h : (BinaryDifference.subtract bits (BitCodec.integerCode z) false).2 with
      | false => rfl
      | true => have := h1.mp h; omega
    · cases h : (BinaryDifference.subtract (BitCodec.integerCode z) bits false).2 with
      | false => rfl
      | true => have := h2.mp h; omega

theorem matches_code (a b : ℤ) (ha : a.natAbs ≤ 5) (hb : b.natAbs ≤ 5) :
    equalCode (BitCodec.integerCode a) b = decide (a = b) := by
  obtain ⟨i, rfl⟩ := index_of_small a ha
  obtain ⟨j, rfl⟩ := index_of_small b hb
  have h : ∀ i j : Fin 11, BinaryDifference.value (BitCodec.integerCode (coefficient i)) =
      BinaryDifference.value (BitCodec.integerCode (coefficient j)) ↔ coefficient i = coefficient j := by decide
  have hiff := (equalCode_true_iff (BitCodec.integerCode (coefficient i)) (coefficient j)).trans (h i j)
  by_cases he : coefficient i = coefficient j
  · have hc := hiff.mpr he
    simpa only [he, decide_true] using hc
  · have hc : equalCode (BitCodec.integerCode (coefficient i)) (coefficient j) = false := by
      cases hc : equalCode (BitCodec.integerCode (coefficient i)) (coefficient j) with
      | false => rfl
      | true => exact False.elim (he (hiff.mp hc))
    simp only [hc, he, decide_false]

def product (a b : ℤ) : List Bool := BitCodec.integerCode (-256 * a * b)

theorem product_bound (a b : ℤ) (ha : a.natAbs ≤ 5) (hb : b.natAbs ≤ 5) : (product a b).length ≤ 28 := by
  obtain ⟨i, rfl⟩ := index_of_small a ha
  obtain ⟨j, rfl⟩ := index_of_small b hb
  have h : ∀ i j : Fin 11, (product (coefficient i) (coefficient j)).length ≤ 28 := by decide
  exact h i j

theorem select_code (a : ℤ) (ha : a.natAbs ≤ 5) (f : ℤ → List Bool) (fallback : List Bool)
    (entries : List ℤ) (he : ∀ z ∈ entries, z.natAbs ≤ 5) (hm : a ∈ entries) :
    select (BitCodec.integerCode a) f fallback entries = f a := by
  induction entries with
  | nil => simp at hm
  | cons z rest ih =>
    have hz := he z (by simp)
    rw [select, matches_code a z ha hz]
    by_cases haz : a = z
    · subst z
      simp
    · simp only [haz, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (fun b hb => he b (by simp [hb])) ((List.mem_cons.mp hm).resolve_left haz)

theorem select_catalog (a : ℤ) (ha : a.natAbs ≤ 5) (f : ℤ → List Bool) (fallback : List Bool) :
    select (BitCodec.integerCode a) f fallback catalog = f a :=
  select_code a ha f fallback catalog catalog_bound (mem_catalog a ha)

end JointThermoComplexity.Complexity.SmallCoefficientTable

#print axioms JointThermoComplexity.Complexity.SmallCoefficientTable.matches_code
#print axioms JointThermoComplexity.Complexity.SmallCoefficientTable.product_bound
#print axioms JointThermoComplexity.Complexity.SmallCoefficientTable.select_catalog
