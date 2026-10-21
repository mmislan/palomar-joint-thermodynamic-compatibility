module
public import proofs.JointThermoComplexity.Complexity.DenseCanonicalControl

set_option autoImplicit false
@[expose] public section

/-! Fixed-four comparison banks emit exactly the canonical occurrence powers.
Repeated reference values contribute their full stored multiplicities. -/

namespace JointThermoComplexity.Complexity.DenseRawPowerIdentity
open scoped BigOperators
variable {n m k : ℕ}

theorem cell_count (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (occ : List (Fin m)) (i : ℕ) :
    PowerVectorControl.cell (DensePowerPorts.cellLayout m hm) (OccurrencePowerWeights.weight occ) values i =
      (occ.map (fun p => values (DensePowerPorts.reference m hm p))).count i := by
  change ((List.ofFn (DensePowerPorts.comparison m hm)).map
    (fun p => if i = values p.constant then OccurrencePowerWeights.weight occ p else 0)).sum = _
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ p : Fin m, if i = values (DensePowerPorts.reference m hm p)
    then OccurrencePowerWeights.weight occ (DensePowerPorts.comparison m hm p) else 0) = _
  simp_rw [OccurrencePowerWeights.weight_comparison]
  exact OccurrencePowerWeights.weighted_count occ (fun p => values (DensePowerPorts.reference m hm p)) i

theorem raw_values (vs : List (Fin n)) : DenseRawReady.values (vs.map Fin.val) = DensePowerReady.values vs := by
  funext j
  simp [DenseRawReady.values, DensePowerReady.values]

theorem boxed_count (vs : List (Fin n)) (hm : vs.length ≤ 4) (occ : List (Fin vs.length)) :
    DenseRawExternal.boxedGamma 4 (by decide) (DenseRawReady.values (vs.map Fin.val)) (occ.map (Fin.castLE hm)) n =
      (fun v : Fin n => (occ.map (RawNormalizationTemplates.lookup vs)).count v) := by
  funext v
  unfold DenseRawExternal.boxedGamma
  rw [cell_count, raw_values]
  have he : (occ.map (Fin.castLE hm)).map (fun p => DensePowerReady.values vs (DensePowerPorts.reference 4 (by decide) p)) =
      (occ.map (RawNormalizationTemplates.lookup vs)).map Fin.val := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    exact DensePowerReady.values_reference vs hm i
  rw [he]
  exact List.count_map_of_injective _ Fin.val Fin.val_injective v

theorem positive_map (f : Fin m → Fin k) (occ : List (Fin m ⊕ Fin m)) :
    DenseTemplatePowerCode.positive (occ.map (Sum.map f f)) = (DenseTemplatePowerCode.positive occ).map f := by
  induction occ with
  | nil => rfl
  | cons p rest ih => cases p <;> simp [DenseTemplatePowerCode.positive, ih]

theorem negative_map (f : Fin m → Fin k) (occ : List (Fin m ⊕ Fin m)) :
    DenseTemplatePowerCode.negative (occ.map (Sum.map f f)) = (DenseTemplatePowerCode.negative occ).map f := by
  induction occ with
  | nil => rfl
  | cons p rest ih => cases p <;> simp [DenseTemplatePowerCode.negative, ih]

theorem unboxed_count (vs : List (Fin n)) (hm : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length)) :
    DenseRawExternal.unboxedGamma 4 (by decide) (DenseRawReady.values (vs.map Fin.val))
      (occ.map (Sum.map (Fin.castLE hm) (Fin.castLE hm))) n =
      Fin.cons 0 (fun v : Fin (n + n) => (DenseTemplatePowerCode.signedMonomial vs occ).count v) := by
  unfold DenseRawExternal.unboxedGamma
  rw [positive_map, negative_map, boxed_count, boxed_count, DenseTemplatePowerCode.signed_array]

theorem boxed_original (right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (vs : List (Fin p.arity)) (hm : vs.length ≤ 4) (occ : List (Fin vs.length))
    (hrow : p.payload[j.val].2 = occ.map (RawNormalizationTemplates.lookup vs)) :
    DenseRawExternal.boxedGamma 4 (by decide) (DenseRawReady.values (vs.map Fin.val)) (occ.map (Fin.castLE hm)) p.arity =
      DenseComplexOriginal.gamma right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p) j.succ.succ := by
  have hg := (FiniteCodec.finiteFunction FiniteCodec.natural p.arity).code_injective
    (DenseComplexOriginal.boxed_gamma_code right p j vs hm occ hrow)
  exact (boxed_count vs hm occ).trans hg.symm

theorem unboxed_original (right : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (j : Fin payload.length)
    (vs : List (Fin n)) (hm : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length))
    (hrow : payload[j.val].2 = DenseTemplatePowerCode.signedMonomial vs occ) :
    DenseRawExternal.unboxedGamma 4 (by decide) (DenseRawReady.values (vs.map Fin.val))
      (occ.map (Sum.map (Fin.castLE hm) (Fin.castLE hm))) n =
      DenseComplexOriginal.gamma right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩) (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) j.succ.succ := by
  have hg := (FiniteCodec.finiteFunction FiniteCodec.natural ((n + n) + 1)).code_injective
    (DenseComplexOriginal.unboxed_gamma_code right payload j vs hm occ hrow)
  exact (unboxed_count vs hm occ).trans hg.symm

end JointThermoComplexity.Complexity.DenseRawPowerIdentity

#print axioms JointThermoComplexity.Complexity.DenseRawPowerIdentity.boxed_original
#print axioms JointThermoComplexity.Complexity.DenseRawPowerIdentity.unboxed_original
