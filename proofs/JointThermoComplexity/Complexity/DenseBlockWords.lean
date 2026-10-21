module
public import proofs.JointThermoComplexity.Complexity.IndicatorVectorControl
public import proofs.JointThermoComplexity.Complexity.RepeatedOutput

set_option autoImplicit false
@[expose] public section

/-! Complex word blocks retain the exact shared/external/private species order. -/

namespace JointThermoComplexity.Complexity.DenseBlockWords

def zeros (N : ℕ) : List Bool := RepeatedOutput.copies (BitCodec.naturalCode 0) N
def leftBefore (k M N : ℕ) : List Bool := IndicatorVectorControl.words k M 0 (N + 2)
def leftAfter (N : ℕ) : List Bool := zeros N
def rightBefore (k M N : ℕ) : List Bool := IndicatorVectorControl.words k M 0 2 ++ zeros N
def rightAfter (k M N : ℕ) : List Bool := IndicatorVectorControl.words k M 2 N

theorem zeros_code (N : ℕ) : zeros N = FiniteCodec.functionCode FiniteCodec.natural (fun _ : Fin N => 0) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change zeros N ++ BitCodec.naturalCode 0 = _
    rw [ih]
    simp only [FiniteCodec.functionCode_eq_flatMap, List.ofFn_succ_last, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, FiniteCodec.natural]

theorem code_append {α : Type} (A : FiniteCodec.Codec α) {n m : ℕ} (f : Fin n → α) (g : Fin m → α) :
    FiniteCodec.functionCode A (Fin.append f g) = FiniteCodec.functionCode A f ++ FiniteCodec.functionCode A g := by
  simp only [FiniteCodec.functionCode_eq_flatMap, List.ofFn_fin_append, List.flatMap_append]

def rightShared (k M N : ℕ) (j : Fin (N + 2)) : ℕ := if j.val < 2 then if j.val = M then k else 0 else 0

theorem right_shared_code (k M N : ℕ) : FiniteCodec.functionCode FiniteCodec.natural (rightShared k M N) = rightBefore k M N := by
  have ht : (fun j : Fin N => rightShared k M N j.succ.succ) = fun _ => 0 := by
    funext j
    unfold rightShared
    rw [ite_eq_right (by change ¬j.val + 1 + 1 < 2; omega)]
  change BinaryEqualityEmit.word k 0 M ++ (BinaryEqualityEmit.word k 1 M ++
    FiniteCodec.functionCode FiniteCodec.natural (fun j : Fin N => rightShared k M N j.succ.succ)) = _
  rw [ht, ← zeros_code]
  unfold rightBefore
  rw [IndicatorVectorControl.words_succ, IndicatorVectorControl.words_succ, IndicatorVectorControl.words_zero]
  simp only [Nat.zero_add, List.nil_append, List.append_assoc]

def leftValues (k M N e : ℕ) (γ : Fin e → ℕ) : Fin ((N + 2) + (e + N)) → ℕ :=
  Fin.append (fun j : Fin (N + 2) => if j.val = M then k else 0) (Fin.append γ (fun _ : Fin N => 0))

def rightValues (k M N e : ℕ) (γ : Fin e → ℕ) : Fin ((N + 2) + (e + N)) → ℕ :=
  Fin.append (rightShared k M N) (Fin.append γ (fun j : Fin N => if 2 + j.val = M then k else 0))

theorem left_full_code (k M N e : ℕ) (γ : Fin e → ℕ) :
    leftBefore k M N ++ FiniteCodec.functionCode FiniteCodec.natural γ ++ leftAfter N =
      FiniteCodec.functionCode FiniteCodec.natural (leftValues k M N e γ) := by
  have hl := IndicatorVectorControl.words_code k M 0 (N + 2)
  simp only [Nat.zero_add] at hl
  unfold leftValues leftBefore leftAfter
  rw [code_append, code_append, ← hl, ← zeros_code]
  rw [List.append_assoc]

theorem right_full_code (k M N e : ℕ) (γ : Fin e → ℕ) :
    rightBefore k M N ++ FiniteCodec.functionCode FiniteCodec.natural γ ++ rightAfter k M N =
      FiniteCodec.functionCode FiniteCodec.natural (rightValues k M N e γ) := by
  unfold rightValues rightAfter
  rw [code_append, code_append, right_shared_code, ← IndicatorVectorControl.words_code k M 2 N]
  rw [List.append_assoc]

end JointThermoComplexity.Complexity.DenseBlockWords

#print axioms JointThermoComplexity.Complexity.DenseBlockWords.left_full_code
#print axioms JointThermoComplexity.Complexity.DenseBlockWords.right_full_code
