module
public import proofs.JointThermoComplexity.Complexity.DenseRawExternal

set_option autoImplicit false
@[expose] public section

/-! The fixed product gain branch works for every raw external vector. -/

namespace JointThermoComplexity.Complexity.DenseRawProduct
open _root_.Complexity _root_.Complexity.TM
open DenseComplexPorts DenseComplexFrame DenseComplexCore DenseComplexOriginal
variable {N : ℕ}

def word (right : Bool) (N : ℕ) (i : Fin (N + 2)) (e : ℕ) (gamma : Fin e → ℕ) : List Bool :=
  FiniteCodec.functionCode FiniteCodec.natural (DenseComplexCore.values right (RationalLiteralNetwork.gain N i)
    (vertex true i).val N e gamma)

theorem hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (sourceValues : Fin 64 → ℕ) (n N B : ℕ)
    (i : Fin (N + 2)) (e : ℕ) (gamma : Fin e → ℕ) (hM : (vertex true i).val.bits.length ≤ B)
    (external : TM 64) (E : ℕ)
    (he : Emits external m hm sourceValues n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable true R) :
    (DenseProductBranch.machine right external).HoareTime
      (Pre true m hm sourceValues n N (vertex true i).val before input emitted (DenseProductBranch.FlagFrame i R))
      (Pre true m hm sourceValues n N (vertex true i).val before input
        (emitted ++ word right N i e gamma) (DenseProductBranch.FlagFrame i R))
      (DenseProductBranch.timeBound right N B E) := by
  apply DenseProductBranch.hoareTime right external m hm sourceValues n N B i (word right N i e gamma) E ?_
    before input emitted R hR
  intro k hk before' input' emitted' S hS
  subst k
  exact DenseComplexCore.code_hoareTime right true m hm sourceValues n N (vertex true i).val B
    (RationalLiteralNetwork.gain N i) e hM external gamma E he before' input' emitted' S hS

end JointThermoComplexity.Complexity.DenseRawProduct

#print axioms JointThermoComplexity.Complexity.DenseRawProduct.hoareTime
