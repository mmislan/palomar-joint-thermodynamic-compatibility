module
public import proofs.JointThermoComplexity.Complexity.DenseProductBranch

set_option autoImplicit false
@[expose] public section

/-! The one fixed gain branch emits original product complexes for every row family. -/

namespace JointThermoComplexity.Complexity.DenseProductEmit
open _root_.Complexity _root_.Complexity.TM
open DenseComplexPorts DenseComplexFrame DenseComplexOriginal DenseProductBranch
variable {n : ℕ}

theorem boxed_hoareTime (right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (vs : List (Fin p.arity)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : p.payload[j.val].2 = occ.map (RawNormalizationTemplates.lookup vs)) (B : ℕ)
    (hM : (vertex true j.succ.succ).val.bits.length ≤ B) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable true R) :
    (DenseProductBranch.machine right (DenseExternalPower.boxedMachine vs.length hcap occ)).HoareTime
      (Pre true vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length (vertex true j.succ.succ).val
        before input emitted (FlagFrame j.succ.succ R))
      (Pre true vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length (vertex true j.succ.succ).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right true (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p) j.succ.succ))
        (FlagFrame j.succ.succ R))
      (timeBound right p.payload.length B (DenseExternalPower.vectorBound p.arity B)) := by
  apply DenseProductBranch.hoareTime right _ vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length B
    j.succ.succ _ (DenseExternalPower.vectorBound p.arity B) ?_ before input emitted R hR
  intro k hk before' input' emitted' R' hR'
  exact DenseComplexOriginal.boxed_hoareTime right true p j vs hcap occ hocc hrow B k hk hM hbits before' input' emitted' R' hR'

theorem unboxed_hoareTime (right : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (j : Fin payload.length)
    (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : payload[j.val].2 = DenseTemplatePowerCode.signedMonomial vs occ) (B : ℕ)
    (hM : (vertex true j.succ.succ).val.bits.length ≤ B) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable true R) :
    (DenseProductBranch.machine right (DenseExternalPower.unboxedMachine vs.length hcap occ)).HoareTime
      (Pre true vs.length hcap (DensePowerReady.values vs) n payload.length (vertex true j.succ.succ).val
        before input emitted (FlagFrame j.succ.succ R))
      (Pre true vs.length hcap (DensePowerReady.values vs) n payload.length (vertex true j.succ.succ).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right true (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
            (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) j.succ.succ)) (FlagFrame j.succ.succ R))
      (timeBound right payload.length B (DenseExternalPower.unboxedBound n B)) := by
  apply DenseProductBranch.hoareTime right _ vs.length hcap (DensePowerReady.values vs) n payload.length B
    j.succ.succ _ (DenseExternalPower.unboxedBound n B) ?_ before input emitted R hR
  intro k hk before' input' emitted' R' hR'
  exact DenseComplexOriginal.unboxed_hoareTime right true payload j vs hcap occ hocc hrow B k hk hM hbits before' input' emitted' R' hR'

theorem fixed_boxed_hoareTime (right offset : Bool) (p : SparsePolynomialCodec.PolynomialData) (B : ℕ)
    (hM : (vertex true (DenseFixedComplexOriginal.initialVertex offset p.payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable true R) :
    (DenseProductBranch.machine right DenseFixedExternalPower.boxedMachine).HoareTime
      (Pre true 0 (by decide) (fun _ => 0) p.arity p.payload.length
        (vertex true (DenseFixedComplexOriginal.initialVertex offset p.payload.length)).val before input emitted
        (FlagFrame (DenseFixedComplexOriginal.initialVertex offset p.payload.length) R))
      (Pre true 0 (by decide) (fun _ => 0) p.arity p.payload.length
        (vertex true (DenseFixedComplexOriginal.initialVertex offset p.payload.length)).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right true (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p)
            (DenseFixedComplexOriginal.initialVertex offset p.payload.length)))
        (FlagFrame (DenseFixedComplexOriginal.initialVertex offset p.payload.length) R))
      (timeBound right p.payload.length B (DenseFixedExternalPower.boxedBound p.arity)) := by
  apply DenseProductBranch.hoareTime right _ 0 (by decide) (fun _ => 0) p.arity p.payload.length B
    (DenseFixedComplexOriginal.initialVertex offset p.payload.length) _ (DenseFixedExternalPower.boxedBound p.arity)
    ?_ before input emitted R hR
  intro k hk before' input' emitted' R' hR'
  exact DenseFixedComplexOriginal.boxed_hoareTime right true offset p B k hk hM before' input' emitted' R' hR'

theorem fixed_unboxed_hoareTime (right offset : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (B : ℕ)
    (hM : (vertex true (DenseFixedComplexOriginal.initialVertex offset payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable true R) :
    (DenseProductBranch.machine right (DenseFixedExternalPower.unboxedMachine (DenseFixedComplexOriginal.offsetPower offset))).HoareTime
      (Pre true 0 (by decide) (fun _ => 0) n payload.length
        (vertex true (DenseFixedComplexOriginal.initialVertex offset payload.length)).val before input emitted
        (FlagFrame (DenseFixedComplexOriginal.initialVertex offset payload.length) R))
      (Pre true 0 (by decide) (fun _ => 0) n payload.length
        (vertex true (DenseFixedComplexOriginal.initialVertex offset payload.length)).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right true (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
            (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) (DenseFixedComplexOriginal.initialVertex offset payload.length)))
        (FlagFrame (DenseFixedComplexOriginal.initialVertex offset payload.length) R))
      (timeBound right payload.length B (DenseFixedExternalPower.unboxedBound n (DenseFixedComplexOriginal.offsetPower offset))) := by
  apply DenseProductBranch.hoareTime right _ 0 (by decide) (fun _ => 0) n payload.length B
    (DenseFixedComplexOriginal.initialVertex offset payload.length) _
    (DenseFixedExternalPower.unboxedBound n (DenseFixedComplexOriginal.offsetPower offset)) ?_ before input emitted R hR
  intro k hk before' input' emitted' R' hR'
  exact DenseFixedComplexOriginal.unboxed_hoareTime right true offset payload B k hk hM before' input' emitted' R' hR'

end JointThermoComplexity.Complexity.DenseProductEmit

#print axioms JointThermoComplexity.Complexity.DenseProductEmit.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseProductEmit.unboxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseProductEmit.fixed_boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseProductEmit.fixed_unboxed_hoareTime
