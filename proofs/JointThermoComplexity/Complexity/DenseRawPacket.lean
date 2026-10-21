module
public import proofs.JointThermoComplexity.Complexity.DensePacketControl

set_option autoImplicit false
@[expose] public section

/-! Exact raw words and actual time for a finite static sequence of row programs. -/

namespace JointThermoComplexity.Complexity.DenseRawPacket
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DensePacketControl
variable {A : Type}

theorem hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B e E : ℕ)
    (external : A → TM 64) (coefficient : A → ℤ) (gamma : A → Fin e → ℕ)
    (v : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (hbase : N + 2 ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input : List Bool)
    (rows : List A) (ht : ∀ row ∈ rows, (coefficient row).natAbs ≤ 81)
    (he : ∀ row ∈ rows, DenseComplexCore.Emits (external row) m hm values n (FiniteCodec.functionCode FiniteCodec.natural (gamma row)) E)
    (current : ℕ) (hfit : current + rows.length ≤ N + 2) (emitted : List Bool) :
    (machine right external coefficient rows).HoareTime (Pre current m hm values n N v negative before input emitted R)
      (Pre (current + rows.length) m hm values n N v negative before input
        (emitted ++ words right N e gamma coefficient v negative current rows) R) (timeBound right N B E rows.length) := by
  induction rows generalizing current emitted with
  | nil =>
    have hh := FixedOutput.hoareTime [] before input emitted (Ready current m hm values n N v negative R)
    apply hh.consequence (fun _ _ _ h => h)
    · intro inp work out h
      simpa only [Pre, words, List.length_nil, Nat.add_zero] using h
    · simp only [timeBound, List.length_nil, Nat.zero_mul, le_refl]
  | cons row rows ih =>
    have hcurrent : current ≤ N + 1 := by simp only [List.length_cons] at hfit; omega
    have hiEq : (index N current).val = current := index_val N current hcurrent
    have hI : (index N current).val.bits.length ≤ B := by
      rw [hiEq]
      exact (BoundedUnaryControl.bits_le current).trans (by omega)
    have hM : (DenseComplexOriginal.vertex true (index N current)).val.bits.length ≤ B := by
      have hi := (DenseComplexOriginal.vertex true (index N current)).isLt
      exact (BoundedUnaryControl.bits_le _).trans (by omega)
    have hend : (N + 1).bits.length ≤ B := (BoundedUnaryControl.bits_le _).trans (by omega)
    let headWord := DenseRawRecord.word right N (index N current) e (gamma row) (coefficient row) v negative
    have hhead : (DenseRowStep.machine right (external row) (coefficient row)).HoareTime
        (Pre current m hm values n N v negative before input emitted R)
        (Pre (current + 1) m hm values n N v negative before input (emitted ++ headWord) R)
        (DenseRowStep.timeBound right N B E) := by
      rintro inp work out ⟨hc, hs, u, hu, hw⟩
      have hubits : u.bits.length ≤ B := (BoundedUnaryControl.bits_le u).trans (by omega)
      have hh := DenseRowStep.hoareTime right m hm values n N B (index N current) u e (gamma row) (external row) E
        (he row List.mem_cons_self) (coefficient row) v negative hB (ht row List.mem_cons_self) hI hM hend hubits R hR before input emitted
      obtain ⟨d, time, htime, hreach, hhalt, hc', hs', hw'⟩ := hh inp work out ⟨hc, hs, by simpa only [hiEq] using hw⟩
      refine ⟨d, time, htime, hreach, hhalt, hc', hs', (DenseComplexOriginal.vertex true (index N current)).val, ?_, ?_⟩
      · have hi := (DenseComplexOriginal.vertex true (index N current)).isLt
        omega
      · simpa only [hiEq] using hw'
    have htail : ∀ a ∈ rows, (coefficient a).natAbs ≤ 81 := fun a ha => ht a (List.mem_cons_of_mem row ha)
    have hetail : ∀ a ∈ rows, DenseComplexCore.Emits (external a) m hm values n
        (FiniteCodec.functionCode FiniteCodec.natural (gamma a)) E := fun a ha => he a (List.mem_cons_of_mem row ha)
    have hfitTail : current + 1 + rows.length ≤ N + 2 := by simp only [List.length_cons] at hfit; omega
    have hrest := ih htail hetail (current + 1) hfitTail (emitted ++ headWord)
    have hh := seqTM_hoareTime _ _ hhead (by
      intro inp work out h
      obtain ⟨hi, hw, ho⟩ := h.1.phase
      rw [hi, hw, ho]
      exact h) hrest
    apply hh.consequence (fun _ _ _ h => h)
    · intro inp work out h
      simpa only [words, List.length_cons, headWord, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    · simp only [timeBound, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end JointThermoComplexity.Complexity.DenseRawPacket

#print axioms JointThermoComplexity.Complexity.DenseRawPacket.hoareTime
