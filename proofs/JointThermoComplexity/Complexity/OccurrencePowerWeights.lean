module
public import proofs.JointThermoComplexity.Complexity.DensePowerReady
public import proofs.JointThermoComplexity.Complexity.RawChemicalPolynomial

set_option autoImplicit false
@[expose] public section

/-! Static template occurrence multiplicities give exact powers, including repeated variable values. -/

namespace JointThermoComplexity.Complexity.OccurrencePowerWeights
open scoped BigOperators
variable {m n w : ℕ}

def weight (occ : List (Fin m)) (p : SmallCoefficientMatch.Ports 63) : ℕ :=
  (occ.map Fin.val).count (p.flag.val - 44)

theorem weight_comparison (occ : List (Fin m)) (hm : m ≤ 4) (i : Fin m) :
    weight occ (DensePowerPorts.comparison m hm i) = occ.count i := by
  change (occ.map Fin.val).count ((44 + i.val) - 44) = _
  rw [Nat.add_sub_cancel_left]
  exact List.count_map_of_injective occ Fin.val Fin.val_injective i

theorem weight_eq_sum (xs : List (PowerCellWord.Item w)) :
    PowerCellWord.weight xs = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons p rest ih => simp only [PowerCellWord.weight, List.map_cons, List.sum_cons, ih]

theorem weight_total (occ : List (Fin m)) (hm : m ≤ 4) :
    PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout m hm).comparisons (weight occ)) = occ.length := by
  rw [weight_eq_sum]
  simp only [PowerCellEmit.items, DensePowerPorts.cellLayout, List.map_ofFn]
  change (List.ofFn (fun i : Fin m => weight occ (DensePowerPorts.comparison m hm i))).sum = occ.length
  simp_rw [weight_comparison]
  rw [List.sum_ofFn]
  exact RawChemicalPolynomial.sum_counts occ

theorem count_indicator (xs : List ℕ) (i : ℕ) :
    xs.count i = (xs.map (fun a => if i = a then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    by_cases h : i = a
    · subst a
      simp [ih, Nat.add_comm]
    · simp [ih, h, Ne.symm h]

theorem weighted_count (occ : List (Fin m)) (refs : Fin m → ℕ) (i : ℕ) :
    (∑ p : Fin m, if i = refs p then occ.count p else 0) = (occ.map refs).count i := by
  rw [count_indicator, List.map_map]
  rw [Finset.sum_list_map_count]
  simp only [Function.comp_apply, nsmul_eq_mul, Nat.cast_id, mul_ite, mul_one, mul_zero]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  have hz : occ.count p = 0 := List.count_eq_zero_of_not_mem (by simpa only [List.mem_toFinset] using hp)
  simp only [hz, ite_self]

theorem cell_count (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length)) (i : ℕ) :
    PowerVectorControl.cell (DensePowerPorts.cellLayout vs.length hcap) (weight occ) (DensePowerReady.values vs) i =
      (occ.map (fun p => vs[p.val].val)).count i := by
  change ((List.ofFn (DensePowerPorts.comparison vs.length hcap)).map
    (fun p => if i = DensePowerReady.values vs p.constant then weight occ p else 0)).sum = _
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ p : Fin vs.length, if i = DensePowerReady.values vs (DensePowerPorts.reference vs.length hcap p)
    then weight occ (DensePowerPorts.comparison vs.length hcap p) else 0) = _
  simp_rw [DensePowerReady.values_reference, weight_comparison]
  exact weighted_count occ (fun p => vs[p.val].val) i

end JointThermoComplexity.Complexity.OccurrencePowerWeights

#print axioms JointThermoComplexity.Complexity.OccurrencePowerWeights.weight_total
#print axioms JointThermoComplexity.Complexity.OccurrencePowerWeights.weighted_count
#print axioms JointThermoComplexity.Complexity.OccurrencePowerWeights.cell_count
