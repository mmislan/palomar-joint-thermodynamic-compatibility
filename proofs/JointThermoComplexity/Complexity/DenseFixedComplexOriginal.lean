module
public import proofs.JointThermoComplexity.Complexity.DenseFixedExternalPower
public import proofs.JointThermoComplexity.Complexity.DenseComplexOriginal

set_option autoImplicit false
@[expose] public section

/-! Actual complete baseline/offset complexes with no canonical absent-reference premise. -/

namespace JointThermoComplexity.Complexity.DenseFixedComplexOriginal
open _root_.Complexity _root_.Complexity.TM
open DenseComplexPorts DenseComplexFrame DenseComplexCore DenseComplexOriginal
variable {n : ℕ}

def initialVertex (offset : Bool) (N : ℕ) : Fin (N + 2) := if offset then (0 : Fin (N + 1)).succ else 0
def offsetPower (offset : Bool) : ℕ := if offset then 1 else 0

theorem boxed_gamma (right offset : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    gamma right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p)
      (initialVertex offset p.payload.length) = (fun _ : Fin p.arity => 0) := by
  have hl : (RationalPolynomialNetwork.left true p).powers (initialVertex offset p.payload.length) = (fun _ => 0) := by
    cases offset with
    | false => exact RationalPowerCode.baseline true p
    | true => exact RationalPowerCode.boxed_offset p
  cases right with
  | false => exact hl
  | true =>
    change (RationalPolynomialNetwork.right true p).powers (initialVertex offset p.payload.length) = _
    rw [← RationalPowerCode.left_right true p]
    exact hl

theorem zero_cons (n : ℕ) : Fin.cons (0 : ℕ) (fun _ : Fin n => 0) = (fun _ : Fin (n + 1) => 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ]

theorem unboxed_gamma (right offset : Bool) (payload : SparseInteger.Poly (Fin (n + n))) :
    gamma right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
      (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) (initialVertex offset payload.length) =
      Fin.cons (offsetPower offset) (fun _ : Fin (n + n) => 0) := by
  have hl : (RationalPolynomialNetwork.left false ⟨n + n, payload⟩).powers (initialVertex offset payload.length) =
      Fin.cons (offsetPower offset) (fun _ : Fin (n + n) => 0) := by
    cases offset with
    | false =>
      change (RationalPolynomialNetwork.left false ⟨n + n, payload⟩).powers 0 = Fin.cons 0 (fun _ => 0)
      rw [RationalPowerCode.baseline, zero_cons]
      rfl
    | true => exact RationalPowerCode.unboxed_offset ⟨n + n, payload⟩
  cases right with
  | false => exact hl
  | true =>
    change (RationalPolynomialNetwork.right false ⟨n + n, payload⟩).powers (initialVertex offset payload.length) = _
    rw [← RationalPowerCode.left_right false ⟨n + n, payload⟩]
    exact hl

theorem boxed_hoareTime (right product offset : Bool) (p : SparsePolynomialCodec.PolynomialData) (B k : ℕ)
    (hk : k = amount product p.payload.length (initialVertex offset p.payload.length))
    (hM : (vertex product (initialVertex offset p.payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k DenseFixedExternalPower.boxedMachine).HoareTime
      (Pre product 0 (by decide) (fun _ => 0) p.arity p.payload.length
        (vertex product (initialVertex offset p.payload.length)).val before input emitted R)
      (Pre product 0 (by decide) (fun _ => 0) p.arity p.payload.length
        (vertex product (initialVertex offset p.payload.length)).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right product (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p)
            (initialVertex offset p.payload.length))) R)
      (bound right p.payload.length B k (DenseFixedExternalPower.boxedBound p.arity)) := by
  have he : Emits DenseFixedExternalPower.boxedMachine 0 (by decide) (fun _ => 0) p.arity
      (FiniteCodec.functionCode FiniteCodec.natural
        (gamma right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p)
          (initialVertex offset p.payload.length))) (DenseFixedExternalPower.boxedBound p.arity) := by
    rw [boxed_gamma]
    exact DenseFixedExternalPower.boxed_emits 0 (by decide) (fun _ => 0) p.arity
  exact original_hoareTime right product _ _ (initialVertex offset p.payload.length) k hk 0 (by decide) (fun _ => 0)
    p.arity B hM DenseFixedExternalPower.boxedMachine (DenseFixedExternalPower.boxedBound p.arity) he before input emitted R hR

theorem unboxed_hoareTime (right product offset : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (B k : ℕ)
    (hk : k = amount product payload.length (initialVertex offset payload.length))
    (hM : (vertex product (initialVertex offset payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k (DenseFixedExternalPower.unboxedMachine (offsetPower offset))).HoareTime
      (Pre product 0 (by decide) (fun _ => 0) n payload.length
        (vertex product (initialVertex offset payload.length)).val before input emitted R)
      (Pre product 0 (by decide) (fun _ => 0) n payload.length
        (vertex product (initialVertex offset payload.length)).val before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (complex right product (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
            (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) (initialVertex offset payload.length))) R)
      (bound right payload.length B k (DenseFixedExternalPower.unboxedBound n (offsetPower offset))) := by
  have he : Emits (DenseFixedExternalPower.unboxedMachine (offsetPower offset)) 0 (by decide) (fun _ => 0) n
      (FiniteCodec.functionCode FiniteCodec.natural
        (gamma right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
          (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) (initialVertex offset payload.length)))
      (DenseFixedExternalPower.unboxedBound n (offsetPower offset)) := by
    rw [unboxed_gamma]
    exact DenseFixedExternalPower.unboxed_emits 0 (by decide) (fun _ => 0) n (offsetPower offset)
  exact original_hoareTime right product _ _ (initialVertex offset payload.length) k hk 0 (by decide) (fun _ => 0)
    n B hM (DenseFixedExternalPower.unboxedMachine (offsetPower offset))
    (DenseFixedExternalPower.unboxedBound n (offsetPower offset)) he before input emitted R hR

end JointThermoComplexity.Complexity.DenseFixedComplexOriginal

#print axioms JointThermoComplexity.Complexity.DenseFixedComplexOriginal.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseFixedComplexOriginal.unboxed_hoareTime
