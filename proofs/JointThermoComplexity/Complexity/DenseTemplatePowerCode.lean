module
public import proofs.JointThermoComplexity.Complexity.OccurrencePowerWeights
public import proofs.JointThermoComplexity.Complexity.DenseBlockWords
public import proofs.JointThermoComplexity.Complexity.RawNormalizationTemplates

set_option autoImplicit false
@[expose] public section

/-! Exact boxed and ordered signed-coordinate codes for occurrence templates. -/

namespace JointThermoComplexity.Complexity.DenseTemplatePowerCode
open RawNormalizationTemplates
variable {m n : ℕ}

def positive : List (Fin m ⊕ Fin m) → List (Fin m)
  | [] => []
  | Sum.inl p :: rest => p :: positive rest
  | Sum.inr _ :: rest => positive rest

def negative : List (Fin m ⊕ Fin m) → List (Fin m)
  | [] => []
  | Sum.inl _ :: rest => negative rest
  | Sum.inr p :: rest => p :: negative rest

def signedMonomial (vs : List (Fin n)) (occ : List (Fin vs.length ⊕ Fin vs.length)) : List (Fin (n + n)) :=
  (occ.map (Sum.map (lookup vs) (lookup vs))).map finSumFinEquiv

theorem positive_length (occ : List (Fin m ⊕ Fin m)) : (positive occ).length ≤ occ.length := by
  induction occ with
  | nil => exact le_rfl
  | cons p rest ih => cases p <;> simp only [positive, List.length_cons] <;> omega

theorem negative_length (occ : List (Fin m ⊕ Fin m)) : (negative occ).length ≤ occ.length := by
  induction occ with
  | nil => exact le_rfl
  | cons p rest ih => cases p <;> simp only [negative, List.length_cons] <;> omega

theorem boxed_code (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length)) :
    PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight occ)
      (DensePowerReady.values vs) 0 n =
      FiniteCodec.functionCode FiniteCodec.natural (fun v : Fin n => (occ.map (lookup vs)).count v) := by
  rw [PowerVectorControl.words_code]
  congr 1
  funext v
  rw [Nat.zero_add, OccurrencePowerWeights.cell_count]
  have hh := List.count_map_of_injective (occ.map (lookup vs)) Fin.val Fin.val_injective v
  have he : (occ.map (lookup vs)).map Fin.val = occ.map (fun p => vs[p.val].val) := by
    rw [List.map_map]
    rfl
  rw [he] at hh
  exact hh

theorem count_positive (occ : List (Fin m ⊕ Fin m)) (refs : Fin m → Fin n) (v : Fin n) :
    (occ.map (Sum.map refs refs)).count (Sum.inl v) = ((positive occ).map refs).count v := by
  induction occ with
  | nil => rfl
  | cons p rest ih => cases p <;> simp [positive, List.count_cons, ih]

theorem count_negative (occ : List (Fin m ⊕ Fin m)) (refs : Fin m → Fin n) (v : Fin n) :
    (occ.map (Sum.map refs refs)).count (Sum.inr v) = ((negative occ).map refs).count v := by
  induction occ with
  | nil => rfl
  | cons p rest ih => cases p <;> simp [negative, List.count_cons, ih]

theorem signed_left (vs : List (Fin n)) (occ : List (Fin vs.length ⊕ Fin vs.length)) (v : Fin n) :
    (signedMonomial vs occ).count (finSumFinEquiv (Sum.inl v)) = ((positive occ).map (lookup vs)).count v := by
  unfold signedMonomial
  rw [List.count_map_of_injective _ finSumFinEquiv finSumFinEquiv.injective]
  exact count_positive occ (lookup vs) v

theorem signed_right (vs : List (Fin n)) (occ : List (Fin vs.length ⊕ Fin vs.length)) (v : Fin n) :
    (signedMonomial vs occ).count (finSumFinEquiv (Sum.inr v)) = ((negative occ).map (lookup vs)).count v := by
  unfold signedMonomial
  rw [List.count_map_of_injective _ finSumFinEquiv finSumFinEquiv.injective]
  exact count_negative occ (lookup vs) v

theorem signed_array (vs : List (Fin n)) (occ : List (Fin vs.length ⊕ Fin vs.length)) :
    (fun v : Fin (n + n) => (signedMonomial vs occ).count v) =
      Fin.append (fun v : Fin n => ((positive occ).map (lookup vs)).count v)
        (fun v : Fin n => ((negative occ).map (lookup vs)).count v) := by
  funext v
  obtain ⟨s, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)).surjective v
  cases s with
  | inl v =>
    change (signedMonomial vs occ).count (finSumFinEquiv (Sum.inl v)) =
      (Fin.append _ _) (Fin.castAdd n v)
    rw [Fin.append_left]
    exact signed_left vs occ v
  | inr v =>
    change (signedMonomial vs occ).count (finSumFinEquiv (Sum.inr v)) =
      (Fin.append _ _) (Fin.natAdd n v)
    rw [Fin.append_right]
    exact signed_right vs occ v

theorem signed_code (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length)) :
    FiniteCodec.functionCode FiniteCodec.natural (fun v : Fin (n + n) => (signedMonomial vs occ).count v) =
      PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight (positive occ))
        (DensePowerReady.values vs) 0 n ++
      PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight (negative occ))
        (DensePowerReady.values vs) 0 n := by
  rw [signed_array, DenseBlockWords.code_append, ← boxed_code vs hcap (positive occ), ← boxed_code vs hcap (negative occ)]

theorem unboxed_code (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length)) :
    FiniteCodec.functionCode FiniteCodec.natural (Fin.cons 0 (fun v : Fin (n + n) => (signedMonomial vs occ).count v)) =
      BitCodec.naturalCode 0 ++
        (PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight (positive occ))
          (DensePowerReady.values vs) 0 n ++
        PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight (negative occ))
          (DensePowerReady.values vs) 0 n) := by
  simpa only [FiniteCodec.functionCode, Fin.cons_zero, Fin.cons_succ, FiniteCodec.natural] using
    congrArg (fun rest => BitCodec.naturalCode 0 ++ rest) (signed_code vs hcap occ)

end JointThermoComplexity.Complexity.DenseTemplatePowerCode

#print axioms JointThermoComplexity.Complexity.DenseTemplatePowerCode.boxed_code
#print axioms JointThermoComplexity.Complexity.DenseTemplatePowerCode.signed_code
#print axioms JointThermoComplexity.Complexity.DenseTemplatePowerCode.unboxed_code
