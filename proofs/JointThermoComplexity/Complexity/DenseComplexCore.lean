module
public import proofs.JointThermoComplexity.Complexity.DenseComplexFrame

set_option autoImplicit false
@[expose] public section

/-! Complete literal complex machines, with an explicitly supplied external-block Hoare theorem. -/

namespace JointThermoComplexity.Complexity.DenseComplexCore
open _root_.Complexity _root_.Complexity.TM
open DenseComplexPorts DenseComplexFrame

def Emits (external : TM 64) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n : ℕ) (middle : List Bool) (E : ℕ) : Prop :=
  ∀ (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop),
    PowerVectorLoop.Stable (DensePowerPorts.layout m hm) R →
    external.HoareTime (DenseExternalPower.Pre m hm values n before input emitted R)
      (DenseExternalPower.Pre m hm values n before input (emitted ++ middle) R) E

def leftWords (k M N : ℕ) (middle : List Bool) : List Bool :=
  DenseBlockWords.leftBefore k M N ++ middle ++ DenseBlockWords.leftAfter N

def rightWords (k M N : ℕ) (middle : List Bool) : List Bool :=
  DenseBlockWords.rightBefore k M N ++ middle ++ DenseBlockWords.rightAfter k M N

def leftMachine (product : Bool) (k : ℕ) (external : TM 64) : TM 64 :=
  seqTM (DenseInternalBlocks.leftBefore (ports product) k) (seqTM external (DenseInternalBlocks.zeros (ports product)))

def rightMachine (product : Bool) (k : ℕ) (external : TM 64) : TM 64 :=
  seqTM (DenseInternalBlocks.rightBefore (ports product) k) (seqTM external (DenseInternalBlocks.rightAfter (ports product) k))

def leftBound (N B k E : ℕ) : ℕ := DenseInternalBlocks.leftBound N B k + E + DenseInternalBlocks.zeroBound N + 2
def rightBound (N B k E : ℕ) : ℕ := DenseInternalBlocks.rightBeforeBound N B k + E + DenseInternalBlocks.rightAfterBound N B k + 2

theorem external_hoareTime (product : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N M : ℕ)
    (external : TM 64) (middle : List Bool) (E : ℕ) (he : Emits external m hm values n middle E)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    external.HoareTime (Pre product m hm values n N M before input emitted R)
      (Pre product m hm values n N M before input (emitted ++ middle) R) E := by
  have hh := he before input emitted (ExternalR product N M R) (external_stable product m hm N M R hR)
  apply hh.consequence
  · exact fun inp work out hp => (external_iff product m hm values n N M before input emitted R inp work out).mp hp
  · exact fun inp work out hp => (external_iff product m hm values n N M before input (emitted ++ middle) R inp work out).mpr hp
  · exact le_rfl

theorem left_hoareTime (product : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N M B k : ℕ)
    (hM : M.bits.length ≤ B) (external : TM 64) (middle : List Bool) (E : ℕ) (he : Emits external m hm values n middle E)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (leftMachine product k external).HoareTime (Pre product m hm values n N M before input emitted R)
      (Pre product m hm values n N M before input (emitted ++ leftWords k M N middle) R) (leftBound N B k E) := by
  have h1 := DenseInternalBlocks.left_before_hoareTime (ports product) k N M B hM before input emitted
    (InternalR m hm values n R) (internal_stable product m hm values n R hR)
  have h2 := external_hoareTime product m hm values n N M external middle E he before input
    (emitted ++ DenseBlockWords.leftBefore k M N) R hR
  have h3 := DenseInternalBlocks.zeros_hoareTime (ports product) N M 0 before input
    ((emitted ++ DenseBlockWords.leftBefore k M N) ++ middle) (InternalR m hm values n R)
  have h23 := seqTM_hoareTime _ _ h2 (phase product m hm values n N M before input _ R) h3
  have hh := seqTM_hoareTime _ _ h1 (phase product m hm values n N M before input _ R) h23
  apply hh.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    simpa only [Pre, leftWords, DenseBlockWords.leftAfter, List.append_assoc] using hp
  · unfold leftBound
    omega

theorem right_hoareTime (product : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N M B k : ℕ)
    (hM : M.bits.length ≤ B) (external : TM 64) (middle : List Bool) (E : ℕ) (he : Emits external m hm values n middle E)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (rightMachine product k external).HoareTime (Pre product m hm values n N M before input emitted R)
      (Pre product m hm values n N M before input (emitted ++ rightWords k M N middle) R) (rightBound N B k E) := by
  have h1 := DenseInternalBlocks.right_before_hoareTime (ports product) k N M B hM before input emitted
    (InternalR m hm values n R) (internal_stable product m hm values n R hR)
  have h2 := external_hoareTime product m hm values n N M external middle E he before input
    (emitted ++ DenseBlockWords.rightBefore k M N) R hR
  have h3 := DenseInternalBlocks.right_after_hoareTime (ports product) k N M B hM before input
    ((emitted ++ DenseBlockWords.rightBefore k M N) ++ middle) (InternalR m hm values n R)
    (internal_stable product m hm values n R hR)
  have h23 := seqTM_hoareTime _ _ h2 (phase product m hm values n N M before input _ R) h3
  have hh := seqTM_hoareTime _ _ h1 (phase product m hm values n N M before input _ R) h23
  apply hh.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    simpa only [Pre, rightWords, List.append_assoc] using hp
  · unfold rightBound
    omega

def machine (right product : Bool) (k : ℕ) (external : TM 64) : TM 64 :=
  if right then rightMachine product k external else leftMachine product k external
def bound (right : Bool) (N B k E : ℕ) : ℕ := if right then rightBound N B k E else leftBound N B k E
def values (right : Bool) (k M N e : ℕ) (gamma : Fin e → ℕ) : Fin ((N + 2) + (e + N)) → ℕ :=
  if right then DenseBlockWords.rightValues k M N e gamma else DenseBlockWords.leftValues k M N e gamma

theorem code_hoareTime (right product : Bool) (m : ℕ) (hm : m ≤ 4) (sourceValues : Fin 64 → ℕ) (n N M B k e : ℕ)
    (hM : M.bits.length ≤ B) (external : TM 64) (gamma : Fin e → ℕ) (E : ℕ)
    (he : Emits external m hm sourceValues n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    (machine right product k external).HoareTime (Pre product m hm sourceValues n N M before input emitted R)
      (Pre product m hm sourceValues n N M before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural (values right k M N e gamma)) R) (bound right N B k E) := by
  cases right with
  | false =>
    have hh := left_hoareTime product m hm sourceValues n N M B k hM external _ E he before input emitted R hR
    simpa only [machine, bound, values, Bool.false_eq_true, ↓reduceIte, leftWords, DenseBlockWords.left_full_code] using hh
  | true =>
    have hh := right_hoareTime product m hm sourceValues n N M B k hM external _ E he before input emitted R hR
    simpa only [machine, bound, values, ↓reduceIte, rightWords, DenseBlockWords.right_full_code] using hh

end JointThermoComplexity.Complexity.DenseComplexCore

#print axioms JointThermoComplexity.Complexity.DenseComplexCore.code_hoareTime
