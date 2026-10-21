module
public import proofs.JointThermoComplexity.Complexity.DenseTemplatePowerCode
public import proofs.JointThermoComplexity.Complexity.RationalPolynomialNetwork

set_option autoImplicit false
@[expose] public section

/-! Exact original branch powers, including the unboxed offset and coordinate order. -/

namespace JointThermoComplexity.Complexity.RationalPowerCode
open RationalBranchData RationalPolynomialNetwork RationalPolynomialBranches
open SparsePolynomialCodec RawChemicalPolynomial
variable {E : Type} {N n : ℕ}

theorem powers_zero (b : Data E N) (e : E) : b.powers 0 e = 0 := by
  simp only [Data.powers, Fin.val_zero, ↓reduceDIte]

theorem powers_succ (b : Data E N) (i : Fin (N + 1)) (e : E) : b.powers i.succ e = b.exponent i e := by
  unfold Data.powers
  rw [dite_eq_right (by change i.val + 1 ≠ 0; omega)]
  congr 1

theorem left_right (boxed : Bool) (p : PolynomialData) : (left boxed p).powers = (right boxed p).powers := by
  cases boxed <;> rfl

theorem baseline (boxed : Bool) (p : PolynomialData) : (left boxed p).powers 0 = fun _ => 0 := by
  funext e
  exact powers_zero _ e

theorem boxed_offset (p : PolynomialData) :
    (left true p).powers (0 : Fin (p.payload.length + 1)).succ = fun _ => 0 := by
  funext e
  rw [powers_succ]
  simp only [left, boxedLeft, Fin.cases_zero]

theorem boxed_row (p : PolynomialData) (j : Fin p.payload.length) :
    (left true p).powers j.succ.succ = exponents p.payload j := by
  funext e
  rw [powers_succ]
  simp only [left, boxedLeft, Fin.cases_succ]

theorem unboxed_offset (p : PolynomialData) :
    (left false p).powers (0 : Fin (p.payload.length + 1)).succ = Fin.cons 1 (fun _ => 0) := by
  funext e
  refine Fin.cases ?_ (fun v => ?_) e
  · rw [powers_succ]
    simp only [left, RationalBranchRelabel.relabel, Equiv.symm_symm, unboxedLeft, Fin.cases_zero,
      finSuccEquiv_zero, Fin.cons_zero]
  · rw [powers_succ]
    simp only [left, RationalBranchRelabel.relabel, Equiv.symm_symm, unboxedLeft, Fin.cases_zero,
      finSuccEquiv_succ, Fin.cons_succ]

theorem unboxed_row (p : PolynomialData) (j : Fin p.payload.length) :
    (left false p).powers j.succ.succ = Fin.cons 0 (exponents p.payload j) := by
  funext e
  refine Fin.cases ?_ (fun v => ?_) e
  · rw [powers_succ]
    simp only [left, RationalBranchRelabel.relabel, Equiv.symm_symm, unboxedLeft, Fin.cases_succ,
      finSuccEquiv_zero, Fin.cons_zero]
  · rw [powers_succ]
    simp only [left, RationalBranchRelabel.relabel, Equiv.symm_symm, unboxedLeft, Fin.cases_succ,
      finSuccEquiv_succ, Fin.cons_succ]

theorem unboxed_row_code (p : PolynomialData) (j : Fin p.payload.length) :
    FiniteCodec.functionCode FiniteCodec.natural ((left false p).powers j.succ.succ) =
      BitCodec.naturalCode 0 ++ FiniteCodec.functionCode FiniteCodec.natural (exponents p.payload j) := by
  rw [unboxed_row]
  simp only [FiniteCodec.functionCode, Fin.cons_zero, Fin.cons_succ, FiniteCodec.natural]

theorem boxed_template_code (p : PolynomialData) (j : Fin p.payload.length)
    (vs : List (Fin p.arity)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length))
    (hrow : p.payload[j.val].2 = occ.map (RawNormalizationTemplates.lookup vs)) :
    FiniteCodec.functionCode FiniteCodec.natural ((left true p).powers j.succ.succ) =
      PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight occ)
        (DensePowerReady.values vs) 0 p.arity := by
  rw [boxed_row]
  change FiniteCodec.functionCode FiniteCodec.natural (fun v => p.payload[j.val].2.count v) = _
  rw [hrow]
  exact (DenseTemplatePowerCode.boxed_code vs hcap occ).symm

theorem unboxed_template_code (payload : SparseInteger.Poly (Fin (n + n))) (j : Fin payload.length)
    (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length))
    (hrow : payload[j.val].2 = DenseTemplatePowerCode.signedMonomial vs occ) :
    FiniteCodec.functionCode FiniteCodec.natural
      ((left false ⟨n + n, payload⟩).powers j.succ.succ) =
      BitCodec.naturalCode 0 ++
        (PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight (DenseTemplatePowerCode.positive occ))
          (DensePowerReady.values vs) 0 n ++
        PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap) (OccurrencePowerWeights.weight (DenseTemplatePowerCode.negative occ))
          (DensePowerReady.values vs) 0 n) := by
  rw [unboxed_row_code]
  change BitCodec.naturalCode 0 ++ FiniteCodec.functionCode FiniteCodec.natural
    (fun v => payload[j.val].2.count v) = _
  rw [hrow, DenseTemplatePowerCode.signed_code vs hcap occ]

end JointThermoComplexity.Complexity.RationalPowerCode

#print axioms JointThermoComplexity.Complexity.RationalPowerCode.left_right
#print axioms JointThermoComplexity.Complexity.RationalPowerCode.baseline
#print axioms JointThermoComplexity.Complexity.RationalPowerCode.boxed_offset
#print axioms JointThermoComplexity.Complexity.RationalPowerCode.unboxed_offset
#print axioms JointThermoComplexity.Complexity.RationalPowerCode.boxed_template_code
#print axioms JointThermoComplexity.Complexity.RationalPowerCode.unboxed_template_code
