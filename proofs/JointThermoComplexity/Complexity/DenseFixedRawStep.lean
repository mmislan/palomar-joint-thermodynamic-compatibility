module
public import proofs.JointThermoComplexity.Complexity.DenseFixedRawRecord
public import proofs.JointThermoComplexity.Complexity.DenseRowFrame

set_option autoImplicit false
@[expose] public section

/-! Actual fixed-row successor/record/increment with generic returned reference
bank, reusable scratch and adjusted head. The coefficient buffer need not be a
canonical register at this boundary. -/

namespace JointThermoComplexity.Complexity.DenseFixedRawStep
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseComplexOriginal

def Source (U : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register U (work 13) ∧ (work 12).head = 1 ∧ R work
def Keep (N : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register (N + 1) (work 40) ∧ (work 43).head = 1 ∧ BinaryCopyRegister.Empty (work 63) ∧ (work 12).head = 1 ∧ R work
def Work (current u m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U : ℕ)
    (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register current (work 38) ∧ Register u (work 41) ∧ DenseRecordPrepare.Static m hm values n N (Source U R) work ∧
    Register (N + 1) (work 40) ∧ (work 43).head = 1 ∧ BinaryCopyRegister.Empty (work 63)
def At (current u m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U : ℕ)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Work current u m hm values n N U R work

theorem source_cycle (U : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) :
    DenseCycleFrame.Stable (Source U R) := by
  rintro work next he ⟨hu, hh, hr⟩
  exact ⟨by rw [he 13 (by decide) (by decide) (by decide)]; exact hu,
    by rw [he 12 (by decide) (by decide) (by decide)]; exact hh, DenseRowFrame.cycle_stable R hR work next he hr⟩

theorem keep_complex (product : Bool) (N : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) :
    DenseComplexPorts.Stable product (Keep N R) := by
  rintro work next he ⟨hend, hh, ht, hadj, hr⟩
  have safe (j : Fin 64) (hj : j = 40 ∨ j = 43 ∨ j = 63 ∨ j = 12) : DenseComplexPorts.Outside product j := by
    rcases hj with rfl | rfl | rfl | rfl <;>
      cases product <;> unfold DenseComplexPorts.Outside DenseComplexPorts.target <;> decide
  exact ⟨by rw [he 40 (safe 40 (by simp))]; exact hend,
    by rw [he 43 (safe 43 (by simp))]; exact hh,
    by rw [he 63 (safe 63 (by simp))]; exact ht,
    by rw [he 12 (safe 12 (by simp))]; exact hadj, DenseRowFrame.complex_stable product R hR work next he hr⟩

theorem keep_increment (N : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) :
    BinaryIncrementFramed.Stable (38 : Fin 64) (Keep N R) := by
  rintro work next he ⟨hend, hh, ht, hadj, hr⟩
  exact ⟨by rw [he 40 (by decide)]; exact hend, by rw [he 43 (by decide)]; exact hh,
    by rw [he 63 (by decide)]; exact ht, by rw [he 12 (by decide)]; exact hadj,
    DenseRowFrame.increment_stable R hR work next he hr⟩

def machine (boxed right offset : Bool) (external : TM 64) : TM 64 :=
  seqTM BinaryCycleSuccessor.machine (DenseRecordAdvance.machine (DenseFixedRecord.machine boxed right offset external))
def timeBound (right : Bool) (N B E : ℕ) : ℕ := DenseFixedRecord.timeBound right N B E + 40 * B + 80

theorem hoareTime (boxed right offset : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U B : ℕ)
    (i : Fin (N + 2)) (u e : ℕ) (gamma : Fin e → ℕ) (external : TM 64) (E : ℕ)
    (he : DenseComplexCore.Emits external m hm values n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (hU : U.bits.length ≤ B) (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (hend : (N + 1).bits.length ≤ B) (hu : u.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input emitted : List Bool) :
    (machine boxed right offset external).HoareTime (At i.val u m hm values n N U before input emitted R)
      (At (i.val + 1) (vertex true i).val m hm values n N U before input
        (emitted ++ DenseFixedRawRecord.word boxed right offset U N i e gamma) R) (timeBound right N B E) := by
  have hp := DenseRecordPrepare.hoareTime m hm values n N i u B hI hend hu before input emitted (Source U R)
    (source_cycle U R hR)
  have h1 : BinaryCycleSuccessor.machine.HoareTime (At i.val u m hm values n N U before input emitted R)
      (DenseRecordFrame.Pre m hm values n N i before input emitted (DenseFixedRecord.Source U (Keep N R))) (38 * B + 74) := by
    apply hp.consequence
    · rintro inp work out ⟨hc, hs, hi, hu', hstatic, hend', hhead, ht⟩
      exact ⟨hc, hs, hi, hend', hu', hhead, ht, hstatic⟩
    · rintro inp work out ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hend', hhead, ht, hu', hadj, hr⟩
      exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hu', hend', hhead, ht, hadj, hr⟩
    · exact le_rfl
  have hr := DenseFixedRawRecord.advanced_hoareTime boxed right offset m hm values n N U B i e gamma external E he hU hI hM
    (Keep N R) (keep_complex false N R hR) (keep_complex true N R hR) (keep_increment N R hR) before input emitted
  have h2 : (DenseRecordAdvance.machine (DenseFixedRecord.machine boxed right offset external)).HoareTime
      (DenseRecordFrame.Pre m hm values n N i before input emitted (DenseFixedRecord.Source U (Keep N R)))
      (At (i.val + 1) (vertex true i).val m hm values n N U before input
        (emitted ++ DenseFixedRawRecord.word boxed right offset U N i e gamma) R) (DenseFixedRecord.timeBound right N B E + 2 * B + 5) := by
    apply hr.consequence (fun _ _ _ h => h)
    · rintro inp work out ⟨hc, hs, hi, hn, _hf, hz, hh, hN, hb, href, ha, hu', hend', hhead, ht, hadj, hx⟩
      exact ⟨hc, hs, hi, hn, ⟨hz, hh, hN, hb, href, ha, hu', hadj, hx⟩, hend', hhead, ht⟩
    · exact le_rfl
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  exact hh.mono_bound (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.DenseFixedRawStep

#print axioms JointThermoComplexity.Complexity.DenseFixedRawStep.hoareTime
