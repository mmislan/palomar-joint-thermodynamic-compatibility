module
public import proofs.JointThermoComplexity.Complexity.DenseComplexCore

set_option autoImplicit false
@[expose] public section

/-! Actual boxed/unboxed complete complex emitters, with the external-machine premise discharged. -/

namespace JointThermoComplexity.Complexity.DenseComplexEmit
open _root_.Complexity _root_.Complexity.TM
open DenseComplexPorts DenseComplexFrame DenseComplexCore
variable {n : ℕ}

theorem boxed_emits (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length))
    (hocc : occ.length ≤ 4) (B : ℕ) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B) :
    Emits (DenseExternalPower.boxedMachine vs.length hcap occ) vs.length hcap (DensePowerReady.values vs) n
      (FiniteCodec.functionCode FiniteCodec.natural (fun v : Fin n => (occ.map (RawNormalizationTemplates.lookup vs)).count v))
      (DenseExternalPower.vectorBound n B) := by
  intro before input emitted R hR
  exact DenseExternalPower.boxed_hoareTime vs hcap occ hocc B hbits before input emitted R hR

theorem unboxed_emits (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length))
    (hocc : occ.length ≤ 4) (B : ℕ) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B) :
    Emits (DenseExternalPower.unboxedMachine vs.length hcap occ) vs.length hcap (DensePowerReady.values vs) n
      (FiniteCodec.functionCode FiniteCodec.natural (Fin.cons 0 (fun v : Fin (n + n) => (DenseTemplatePowerCode.signedMonomial vs occ).count v)))
      (DenseExternalPower.unboxedBound n B) := by
  intro before input emitted R hR
  exact DenseExternalPower.unboxed_hoareTime vs hcap occ hocc B hbits before input emitted R hR

theorem boxed_hoareTime (right product : Bool) (vs : List (Fin n)) (hcap : vs.length ≤ 4)
    (occ : List (Fin vs.length)) (hocc : occ.length ≤ 4) (N M B k : ℕ)
    (hM : M.bits.length ≤ B) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k (DenseExternalPower.boxedMachine vs.length hcap occ)).HoareTime
      (Pre product vs.length hcap (DensePowerReady.values vs) n N M before input emitted R)
      (Pre product vs.length hcap (DensePowerReady.values vs) n N M before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (values right k M N n (fun v : Fin n => (occ.map (RawNormalizationTemplates.lookup vs)).count v))) R)
      (bound right N B k (DenseExternalPower.vectorBound n B)) := by
  exact code_hoareTime right product vs.length hcap (DensePowerReady.values vs) n N M B k n hM
    (DenseExternalPower.boxedMachine vs.length hcap occ) _ (DenseExternalPower.vectorBound n B)
    (boxed_emits vs hcap occ hocc B hbits) before input emitted R hR

theorem unboxed_hoareTime (right product : Bool) (vs : List (Fin n)) (hcap : vs.length ≤ 4)
    (occ : List (Fin vs.length ⊕ Fin vs.length)) (hocc : occ.length ≤ 4) (N M B k : ℕ)
    (hM : M.bits.length ≤ B) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k (DenseExternalPower.unboxedMachine vs.length hcap occ)).HoareTime
      (Pre product vs.length hcap (DensePowerReady.values vs) n N M before input emitted R)
      (Pre product vs.length hcap (DensePowerReady.values vs) n N M before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (values right k M N ((n + n) + 1)
            (Fin.cons 0 (fun v : Fin (n + n) => (DenseTemplatePowerCode.signedMonomial vs occ).count v)))) R)
      (bound right N B k (DenseExternalPower.unboxedBound n B)) := by
  exact code_hoareTime right product vs.length hcap (DensePowerReady.values vs) n N M B k ((n + n) + 1) hM
    (DenseExternalPower.unboxedMachine vs.length hcap occ) _ (DenseExternalPower.unboxedBound n B)
    (unboxed_emits vs hcap occ hocc B hbits) before input emitted R hR

end JointThermoComplexity.Complexity.DenseComplexEmit

#print axioms JointThermoComplexity.Complexity.DenseComplexEmit.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseComplexEmit.unboxed_hoareTime
