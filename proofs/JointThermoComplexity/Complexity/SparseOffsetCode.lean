module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetLoopControl
public import proofs.JointThermoComplexity.Complexity.SparseOffsetLoop
public import proofs.JointThermoComplexity.Complexity.SparsePolynomialCodec

set_option autoImplicit false
@[expose] public section

/-! Exact marked-polynomial control agreement, retaining raw term order. -/

namespace JointThermoComplexity.Complexity.SparseOffsetCode
open SparseInteger SparseSubstitution SparseOffsetLoopControl
variable {V W : Type} {n : ℕ}

def termCode (a : ℤ × List (Fin n)) : List Bool :=
  BitCodec.integerCode a.1 ++ SparseListCodec.listCode (SparseListCodec.finite n) a.2

def code (p : Poly (Fin n)) : List Bool := SparseListCodec.listCode (SparsePolynomialCodec.term n) p

def weight (boxed : Bool) (a : ℤ × List V) : ℕ :=
  OffsetTemplateProgram.total (decide (a.1 < 0)) a.1.natAbs (OffsetTemplateData.template boxed a.2.length)

def total (boxed : Bool) (p : Poly V) : ℕ := (p.map (weight boxed)).sum

theorem code_nil : code ([] : Poly (Fin n)) = [false] := rfl
theorem code_cons (a : ℤ × List (Fin n)) (p : Poly (Fin n)) : code (a :: p) = true :: (termCode a ++ code p) := rfl

theorem step_cons (boxed : Bool) (a : ℤ × List (Fin n)) (p : Poly (Fin n))
    (before suffix : List Bool) (A : ℕ) (ha : a.2.length ≤ 4) :
    step boxed ⟨true, before, code (a :: p) ++ suffix, A⟩ =
      ⟨true, (before ++ [true]) ++ termCode a, code p ++ suffix, A + weight boxed a⟩ := by
  rw [code_cons]
  simp only [List.cons_append, step, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix, ↓reduceIte]
  have ht := SparseTermOffsetControl.taken_code a.1 a.2 (code p ++ suffix) ha
  have hr := SparseTermOffsetControl.rest_code a.1 a.2 (code p ++ suffix) ha
  have hd := SparseTermOffsetControl.delta_code boxed a.1 a.2 (code p ++ suffix) ha
  change SparseTermOffsetControl.taken (termCode a ++ (code p ++ suffix)) = termCode a at ht
  change SparseTermOffsetControl.rest (termCode a ++ (code p ++ suffix)) = code p ++ suffix at hr
  change SparseTermOffsetControl.delta boxed (termCode a ++ (code p ++ suffix)) = weight boxed a at hd
  simp only [List.append_assoc, ht, hr, hd]

theorem run_code (boxed : Bool) (p : Poly (Fin n)) (hp : DegreeLE 4 p)
    (k : ℕ) (hk : p.length + 1 ≤ k) (before suffix : List Bool) (A : ℕ) :
    run boxed k ⟨true, before, code p ++ suffix, A⟩ =
      ⟨false, before ++ code p, suffix, A + total boxed p⟩ := by
  induction p generalizing k before A with
  | nil =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by simp only [List.length_nil] at hk; omega)
    change run boxed k (step boxed ⟨true, before, [false] ++ suffix, A⟩) = _
    have he : step boxed ⟨true, before, [false] ++ suffix, A⟩ = ⟨false, before ++ [false], suffix, A⟩ := rfl
    rw [he, run_stopped boxed k _ rfl]
    simp only [total, List.map_nil, List.sum_nil, Nat.add_zero, code_nil]
  | cons a p ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by simp only [List.length_cons] at hk; omega)
    have ha := hp a List.mem_cons_self
    have hp' : DegreeLE 4 p := fun b hb => hp b (List.mem_cons_of_mem a hb)
    change run boxed k (step boxed ⟨true, before, code (a :: p) ++ suffix, A⟩) = _
    rw [step_cons boxed a p before suffix A ha]
    rw [ih hp' k (by simp only [List.length_cons] at hk; omega)]
    simp only [total, List.map_cons, List.sum_cons, code_cons]
    congr 1
    · simp only [List.append_assoc, List.cons_append, List.nil_append]
    · omega

theorem enough_fuel (p : Poly (Fin n)) : p.length + 1 ≤ (code p).length := by
  induction p with
  | nil => rfl
  | cons a p ih => rw [code_cons]; simp only [List.length_cons, List.length_append]; omega

theorem hoareTime (boxed : Bool) (p : Poly (Fin n)) (hp : DegreeLE 4 p)
    (L C A : ℕ) (before suffix emitted : List Bool)
    (hlen : (code p ++ suffix).length ≤ L) (hA : A.bits.length ≤ C)
    (R : (Fin 32 → _root_.Complexity.Tape) → Prop) (hR : SparseOffsetLoop.Stable R) :
    (SparseOffsetLoop.machine boxed).HoareTime
      (fun inp work out => SparseOffsetMarkedStep.Inv L emitted R
        ⟨true, before, code p ++ suffix, A⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (fun inp work out => SparseOffsetMarkedStep.Inv L emitted R
        ⟨false, before ++ code p, suffix, A + total boxed p⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (SparseOffsetLoop.timeBound L C L) := by
  have hk : p.length + 1 ≤ L := (enough_fuel p).trans
    ((by simp only [List.length_append]; omega : (code p).length ≤ (code p ++ suffix).length).trans hlen)
  have ht := SparseOffsetLoop.hoareTime boxed L C L emitted R hR
    ⟨true, before, code p ++ suffix, A⟩ hlen hA
  rw [run_code boxed p hp L hk before suffix A] at ht
  exact ht

theorem rawSum_append (p q : Poly V) :
    OffsetTemplateData.rawSum (p ++ q) = OffsetTemplateData.rawSum p + OffsetTemplateData.rawSum q := by
  simp only [OffsetTemplateData.rawSum, List.map_append, List.sum_append]

theorem rawSum_relabel (f : V → W) (p : Poly V) :
    OffsetTemplateData.rawSum (relabel f p) = OffsetTemplateData.rawSum p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change RationalBranchCoefficients.rightDenominator a.1 * 2 ^ (a.2.map f).length +
      OffsetTemplateData.rawSum (relabel f p) =
      RationalBranchCoefficients.rightDenominator a.1 * 2 ^ a.2.length + OffsetTemplateData.rawSum p
    rw [List.length_map, ih]

theorem total_cube (p : Poly V) : total true p = OffsetTemplateData.rawSum (cube 4 p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [cube_cons, rawSum_append]
    change weight true a + total true p = _
    rw [ih, show weight true a = OffsetTemplateData.rawSum (cubeTerm 4 a) from OffsetTemplateData.cube_total a.1 a.2]

theorem total_orthant (p : Poly V) : total false p = OffsetTemplateData.rawSum (orthant p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change weight false a + total false p = OffsetTemplateData.rawSum
      (scale a.1 (expand orthantVariable a.2) ++ orthant p)
    rw [rawSum_append, ih, show weight false a = OffsetTemplateData.rawSum
      (scale a.1 (expand orthantVariable a.2)) from OffsetTemplateData.orthant_total a.1 a.2]

end JointThermoComplexity.Complexity.SparseOffsetCode

#print axioms JointThermoComplexity.Complexity.SparseOffsetCode.run_code
#print axioms JointThermoComplexity.Complexity.SparseOffsetCode.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseOffsetCode.total_cube
#print axioms JointThermoComplexity.Complexity.SparseOffsetCode.total_orthant
