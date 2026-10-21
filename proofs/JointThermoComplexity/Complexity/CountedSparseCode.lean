module
public import proofs.JointThermoComplexity.Complexity.CountedSparseControl
public import proofs.JointThermoComplexity.Complexity.CountedSparseLoop

set_option autoImplicit false
@[expose] public section

/-! Exact row-count and offset control on raw marked polynomial codes. -/

namespace JointThermoComplexity.Complexity.CountedSparseCode
open SparseInteger SparseSubstitution CountedSparseControl
variable {V : Type} {n : ℕ}

def rowTotal (p : Poly V) : ℕ := (p.map (fun a => 2 ^ a.2.length)).sum

theorem step_cons (boxed : Bool) (a : ℤ × List (Fin n)) (p : Poly (Fin n))
    (before suffix : List Bool) (A N : ℕ) (ha : a.2.length ≤ 4) :
    step boxed ⟨⟨true, before, SparseOffsetCode.code (a :: p) ++ suffix, A⟩, N⟩ =
      ⟨⟨true, (before ++ [true]) ++ SparseOffsetCode.termCode a,
        SparseOffsetCode.code p ++ suffix, A + SparseOffsetCode.weight boxed a⟩, N + 2 ^ a.2.length⟩ := by
  unfold step
  rw [SparseOffsetCode.step_cons boxed a p before suffix A ha]
  congr 1
  simp only [increment, SparseOffsetCode.code_cons, List.cons_append, SourceBitRead.value,
    BooleanMachine.suffix, ↓reduceIte, SparseOffsetCode.termCode, List.append_assoc]
  have hc := SparseTermOffsetControl.count_code a.1 a.2 (SparseOffsetCode.code p ++ suffix) ha
  simpa only [List.append_assoc] using congrArg (fun m => N + m) hc

theorem run_code (boxed : Bool) (p : Poly (Fin n)) (hp : DegreeLE 4 p)
    (k : ℕ) (hk : p.length + 1 ≤ k) (before suffix : List Bool) (A N : ℕ) :
    run boxed k ⟨⟨true, before, SparseOffsetCode.code p ++ suffix, A⟩, N⟩ =
      ⟨⟨false, before ++ SparseOffsetCode.code p, suffix, A + SparseOffsetCode.total boxed p⟩, N + rowTotal p⟩ := by
  induction p generalizing k before A N with
  | nil =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by simp only [List.length_nil] at hk; omega)
    change run boxed k (step boxed ⟨⟨true, before, [false] ++ suffix, A⟩, N⟩) = _
    have he : step boxed ⟨⟨true, before, [false] ++ suffix, A⟩, N⟩ =
        ⟨⟨false, before ++ [false], suffix, A⟩, N⟩ := rfl
    rw [he, run_stopped boxed k _ rfl]
    simp only [SparseOffsetCode.total, rowTotal, List.map_nil, List.sum_nil, Nat.add_zero, SparseOffsetCode.code_nil]
  | cons a p ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by simp only [List.length_cons] at hk; omega)
    have ha := hp a List.mem_cons_self
    have hp' : DegreeLE 4 p := fun b hb => hp b (List.mem_cons_of_mem a hb)
    change run boxed k (step boxed ⟨⟨true, before, SparseOffsetCode.code (a :: p) ++ suffix, A⟩, N⟩) = _
    rw [step_cons boxed a p before suffix A N ha]
    rw [ih hp' k (by simp only [List.length_cons] at hk; omega)]
    simp only [SparseOffsetCode.total, rowTotal, List.map_cons, List.sum_cons, SparseOffsetCode.code_cons]
    congr 1
    · congr 1
      · simp only [List.append_assoc, List.cons_append, List.nil_append]
      · omega
    · omega

theorem cubeTerm_length (d : ℕ) (a : ℤ × List V) : (cubeTerm d a).length = 2 ^ a.2.length := by
  rw [cubeTerm, length_scale]
  exact RawNormalizationTemplates.length_expand_two cubeVariable (fun _ => rfl) a.2

theorem cube_length (d : ℕ) (p : Poly V) : (cube d p).length = rowTotal p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [cube_cons, List.length_append, cubeTerm_length, ih]
    rfl

theorem orthant_length (p : Poly V) : (orthant p).length = rowTotal p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change (scale a.1 (expand orthantVariable a.2) ++ orthant p).length = _
    rw [List.length_append, length_scale,
      RawNormalizationTemplates.length_expand_two orthantVariable (fun _ => rfl), ih]
    rfl

theorem rowTotal_le (p : Poly V) (hp : DegreeLE 4 p) : rowTotal p ≤ 16 * p.length := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    have ha : 2 ^ a.2.length ≤ 16 :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) (hp a List.mem_cons_self)
    have hi := ih (fun b hb => hp b (List.mem_cons_of_mem a hb))
    change 2 ^ a.2.length + rowTotal p ≤ _
    simp only [List.length_cons]
    omega

theorem hoareTime (boxed : Bool) (p : Poly (Fin n)) (hp : DegreeLE 4 p)
    (L C B A N : ℕ) (before suffix emitted : List Bool)
    (hlen : (SparseOffsetCode.code p ++ suffix).length ≤ L) (hA : A.bits.length ≤ C) (hN : N.bits.length ≤ B)
    (R : (Fin 32 → _root_.Complexity.Tape) → Prop) (hR : CountedSparseLoop.Stable R) :
    (CountedSparseLoop.machine boxed).HoareTime
      (fun inp work out => CountedMarkedStep.Inv L emitted R
        ⟨⟨true, before, SparseOffsetCode.code p ++ suffix, A⟩, N⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (fun inp work out => CountedMarkedStep.Inv L emitted R
        ⟨⟨false, before ++ SparseOffsetCode.code p, suffix, A + SparseOffsetCode.total boxed p⟩, N + rowTotal p⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (CountedSparseLoop.timeBound L C B L) := by
  have hk : p.length + 1 ≤ L := (SparseOffsetCode.enough_fuel p).trans
    ((by simp only [List.length_append]; omega : (SparseOffsetCode.code p).length ≤
      (SparseOffsetCode.code p ++ suffix).length).trans hlen)
  have ht := CountedSparseLoop.hoareTime boxed L C B L emitted R hR
    ⟨⟨true, before, SparseOffsetCode.code p ++ suffix, A⟩, N⟩ hlen hA hN
  rw [run_code boxed p hp L hk before suffix A N] at ht
  exact ht

end JointThermoComplexity.Complexity.CountedSparseCode

#print axioms JointThermoComplexity.Complexity.CountedSparseCode.run_code
#print axioms JointThermoComplexity.Complexity.CountedSparseCode.cube_length
#print axioms JointThermoComplexity.Complexity.CountedSparseCode.orthant_length
#print axioms JointThermoComplexity.Complexity.CountedSparseCode.hoareTime
