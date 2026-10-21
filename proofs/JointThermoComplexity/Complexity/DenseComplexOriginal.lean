module
public import proofs.JointThermoComplexity.Complexity.DenseComplexEmit
public import proofs.JointThermoComplexity.Complexity.DenseLiteralComplexCode

set_option autoImplicit false
@[expose] public section

/-! Complete actual complex emitters serialize the unchanged original rational reactions. -/

namespace JointThermoComplexity.Complexity.DenseComplexOriginal
open _root_.Complexity _root_.Complexity.TM RationalBranchData
open DenseComplexPorts DenseComplexFrame DenseComplexCore
variable {e N n : ℕ}

def vertex (product : Bool) (i : Fin (N + 2)) : Fin (N + 2) := if product then finRotate (N + 2) i else i
def amount (product : Bool) (N : ℕ) (i : Fin (N + 2)) : ℕ := if product then RationalLiteralNetwork.gain N i else 1
def gamma (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) : Fin e → ℕ :=
  if right then Rdata.powers i else L.powers i
def index (right : Bool) (N : ℕ) (i : Fin (N + 2)) :=
  RationalLiteralNetwork.reactionNumbering N N (if right then Sum.inr i else Sum.inl i)
def complex (right product : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) :
    Fin (RationalLiteralNetwork.speciesCount e N N) → ℕ :=
  if product then (RationalLiteralNetwork.reaction L Rdata (index right N i)).product
  else (RationalLiteralNetwork.reaction L Rdata (index right N i)).reactant

theorem vector_eq (right product : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) :
    complex right product L Rdata i =
      values right (amount product N i) (vertex product i).val N e (gamma right L Rdata i) := by
  cases right with
  | false =>
    cases product with
    | false =>
      simpa only [complex, index, values, amount, vertex, gamma, Bool.false_eq_true, ↓reduceIte] using
        DenseLiteralComplexCode.left_reactant L Rdata i
    | true =>
      simpa only [complex, index, values, amount, vertex, gamma, Bool.false_eq_true, ↓reduceIte] using
        DenseLiteralComplexCode.left_product L Rdata i
  | true =>
    cases product with
    | false =>
      simpa only [complex, index, values, amount, vertex, gamma, Bool.false_eq_true, ↓reduceIte] using
        DenseLiteralComplexCode.right_reactant L Rdata i
    | true =>
      simpa only [complex, index, values, amount, vertex, gamma, ↓reduceIte] using
        DenseLiteralComplexCode.right_product L Rdata i

theorem original_hoareTime (right product : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2))
    (k : ℕ) (hk : k = amount product N i) (m : ℕ) (hm : m ≤ 4) (sourceValues : Fin 64 → ℕ) (n B : ℕ)
    (hM : (vertex product i).val.bits.length ≤ B) (external : TM 64) (E : ℕ)
    (he : Emits external m hm sourceValues n (FiniteCodec.functionCode FiniteCodec.natural (gamma right L Rdata i)) E)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k external).HoareTime
      (Pre product m hm sourceValues n N (vertex product i).val before input emitted R)
      (Pre product m hm sourceValues n N (vertex product i).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural (complex right product L Rdata i)) R)
      (bound right N B k E) := by
  have hv : complex right product L Rdata i = values right k (vertex product i).val N e (gamma right L Rdata i) := by
    rw [hk]
    exact vector_eq right product L Rdata i
  have hh := code_hoareTime right product m hm sourceValues n N (vertex product i).val B k e hM
    external (gamma right L Rdata i) E he before input emitted R hR
  apply hh.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    rw [hv]
    exact hp
  · exact le_rfl

theorem boxed_gamma_code (right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (vs : List (Fin p.arity)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length))
    (hrow : p.payload[j.val].2 = occ.map (RawNormalizationTemplates.lookup vs)) :
    FiniteCodec.functionCode FiniteCodec.natural
      (gamma right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p) j.succ.succ) =
      FiniteCodec.functionCode FiniteCodec.natural (fun v : Fin p.arity => (occ.map (RawNormalizationTemplates.lookup vs)).count v) := by
  have hl := (RationalPowerCode.boxed_template_code p j vs hcap occ hrow).trans
    (DenseTemplatePowerCode.boxed_code vs hcap occ)
  cases right with
  | false => exact hl
  | true =>
    change FiniteCodec.functionCode FiniteCodec.natural ((RationalPolynomialNetwork.right true p).powers j.succ.succ) = _
    rw [← RationalPowerCode.left_right true p]
    exact hl

theorem boxed_hoareTime (right product : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (vs : List (Fin p.arity)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : p.payload[j.val].2 = occ.map (RawNormalizationTemplates.lookup vs)) (B k : ℕ)
    (hk : k = amount product p.payload.length j.succ.succ) (hM : (vertex product j.succ.succ).val.bits.length ≤ B)
    (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k (DenseExternalPower.boxedMachine vs.length hcap occ)).HoareTime
      (Pre product vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length (vertex product j.succ.succ).val before input emitted R)
      (Pre product vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length (vertex product j.succ.succ).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right product (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p) j.succ.succ)) R)
      (bound right p.payload.length B k (DenseExternalPower.vectorBound p.arity B)) := by
  have he := DenseComplexEmit.boxed_emits vs hcap occ hocc B hbits
  have hc := boxed_gamma_code right p j vs hcap occ hrow
  have he' : Emits (DenseExternalPower.boxedMachine vs.length hcap occ) vs.length hcap (DensePowerReady.values vs) p.arity
      (FiniteCodec.functionCode FiniteCodec.natural
        (gamma right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p) j.succ.succ))
      (DenseExternalPower.vectorBound p.arity B) := by
    rw [hc]
    exact he
  exact original_hoareTime right product _ _ j.succ.succ k hk vs.length hcap (DensePowerReady.values vs) p.arity B hM
    (DenseExternalPower.boxedMachine vs.length hcap occ) (DenseExternalPower.vectorBound p.arity B) he' before input emitted R hR

theorem unboxed_gamma_code (right : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (j : Fin payload.length)
    (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length))
    (hrow : payload[j.val].2 = DenseTemplatePowerCode.signedMonomial vs occ) :
    FiniteCodec.functionCode FiniteCodec.natural
      (gamma right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
        (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) j.succ.succ) =
      FiniteCodec.functionCode FiniteCodec.natural
        (Fin.cons 0 (fun v : Fin (n + n) => (DenseTemplatePowerCode.signedMonomial vs occ).count v)) := by
  have hl := (RationalPowerCode.unboxed_template_code payload j vs hcap occ hrow).trans
    (DenseTemplatePowerCode.unboxed_code vs hcap occ).symm
  cases right with
  | false => exact hl
  | true =>
    change FiniteCodec.functionCode FiniteCodec.natural
      ((RationalPolynomialNetwork.right false ⟨n + n, payload⟩).powers j.succ.succ) = _
    rw [← RationalPowerCode.left_right false ⟨n + n, payload⟩]
    exact hl

theorem unboxed_hoareTime (right product : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (j : Fin payload.length)
    (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : payload[j.val].2 = DenseTemplatePowerCode.signedMonomial vs occ) (B k : ℕ)
    (hk : k = amount product payload.length j.succ.succ) (hM : (vertex product j.succ.succ).val.bits.length ≤ B)
    (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k (DenseExternalPower.unboxedMachine vs.length hcap occ)).HoareTime
      (Pre product vs.length hcap (DensePowerReady.values vs) n payload.length (vertex product j.succ.succ).val before input emitted R)
      (Pre product vs.length hcap (DensePowerReady.values vs) n payload.length (vertex product j.succ.succ).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right product (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
            (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) j.succ.succ)) R)
      (bound right payload.length B k (DenseExternalPower.unboxedBound n B)) := by
  have he := DenseComplexEmit.unboxed_emits vs hcap occ hocc B hbits
  have hc := unboxed_gamma_code right payload j vs hcap occ hrow
  have he' : Emits (DenseExternalPower.unboxedMachine vs.length hcap occ) vs.length hcap (DensePowerReady.values vs) n
      (FiniteCodec.functionCode FiniteCodec.natural
        (gamma right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
          (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) j.succ.succ)) (DenseExternalPower.unboxedBound n B) := by
    rw [hc]
    exact he
  exact original_hoareTime right product _ _ j.succ.succ k hk vs.length hcap (DensePowerReady.values vs) n B hM
    (DenseExternalPower.unboxedMachine vs.length hcap occ) (DenseExternalPower.unboxedBound n B) he' before input emitted R hR

end JointThermoComplexity.Complexity.DenseComplexOriginal

#print axioms JointThermoComplexity.Complexity.DenseComplexOriginal.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseComplexOriginal.unboxed_hoareTime
