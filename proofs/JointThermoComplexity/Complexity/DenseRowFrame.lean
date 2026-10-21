module
public import proofs.JointThermoComplexity.Complexity.DenseRawRecord

set_option autoImplicit false
@[expose] public section

/-! Reusable row boundaries before and after successor/record/increment. -/

namespace JointThermoComplexity.Complexity.DenseRowFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun

def Outside (j : Fin 64) : Prop :=
  j ≠ 12 ∧ j ≠ 16 ∧ j ≠ 33 ∧ j ≠ 34 ∧ j ≠ 38 ∧ j ≠ 39 ∧ j ≠ 41 ∧ j ≠ 42 ∧ j ≠ 43 ∧ j ≠ 63 ∧
    (j.val < 44 ∨ 48 ≤ j.val)
def Stable (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, Outside j → next j = work j) → R work → R next

theorem complex_stable (product : Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : DenseComplexPorts.Stable product R := by
  rintro work next he hr
  apply hR work next _ hr
  rintro j ⟨_, h16, h33, h34, h38, h39, h41, h42, _, _, hflags⟩
  apply he j
  cases product
  · exact ⟨h39, h38, h42, h33, h34, h16, hflags⟩
  · exact ⟨h39, h41, h42, h33, h34, h16, hflags⟩
theorem factor_stable (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : DenseFactorFrame.Stable R := by
  rintro work next he hr
  apply hR work next _ hr
  rintro j ⟨h12, _, _, _, _, _, _, _, _, h63, _⟩
  exact he j h12 h63
theorem cycle_stable (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : DenseCycleFrame.Stable R := by
  rintro work next he hr
  apply hR work next _ hr
  rintro j ⟨_, _, _, _, _, _, h41, _, h43, h63, _⟩
  exact he j h41 h43 h63
theorem increment_stable (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : BinaryIncrementFramed.Stable (38 : Fin 64) R := by
  rintro work next he hr
  apply hR work next _ hr
  rintro j ⟨_, _, _, _, h38, _⟩
  exact he j h38

def Source (v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register v (work 0) ∧ (work 1).read = Γ.ofBool negative ∧ (work 12).head = 1 ∧ R work
def EndFrame (N : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register (N + 1) (work 40) ∧ (work 43).head = 1 ∧ R work

theorem source_cycle (v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    DenseCycleFrame.Stable (Source v negative R) := by
  rintro work next he ⟨hv, hn, ha, hr⟩
  exact ⟨by rw [he 0 (by decide) (by decide) (by decide)]; exact hv,
    by rw [he 1 (by decide) (by decide) (by decide)]; exact hn,
    by rw [he 12 (by decide) (by decide) (by decide)]; exact ha, cycle_stable R hR work next he hr⟩
theorem end_complex (product : Bool) (N : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    DenseComplexPorts.Stable product (EndFrame N R) := by
  rintro work next he ⟨hend, hhead, hr⟩
  have h40 : DenseComplexPorts.Outside product 40 := by
    cases product <;> unfold DenseComplexPorts.Outside DenseComplexPorts.target <;> decide
  have h43 : DenseComplexPorts.Outside product 43 := by
    cases product <;> unfold DenseComplexPorts.Outside DenseComplexPorts.target <;> decide
  exact ⟨by rw [he 40 h40]; exact hend, by rw [he 43 h43]; exact hhead, complex_stable product R hR work next he hr⟩
theorem end_factor (N : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : DenseFactorFrame.Stable (EndFrame N R) := by
  rintro work next he ⟨hend, hhead, hr⟩
  exact ⟨by rw [he 40 (by decide) (by decide)]; exact hend,
    by rw [he 43 (by decide) (by decide)]; exact hhead, factor_stable R hR work next he hr⟩
theorem end_increment (N : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    BinaryIncrementFramed.Stable (38 : Fin 64) (EndFrame N R) := by
  rintro work next he ⟨hend, hhead, hr⟩
  exact ⟨by rw [he 40 (by decide)]; exact hend, by rw [he 43 (by decide)]; exact hhead, increment_stable R hR work next he hr⟩

def Work (current u m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool)
    (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register current (work 38) ∧ Register u (work 41) ∧ DenseRecordPrepare.Static m hm values n N (Source v negative R) work ∧
    Register (N + 1) (work 40) ∧ (work 43).head = 1 ∧ BinaryCopyRegister.Empty (work 63)
def At (current u m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Work current u m hm values n N v negative R work

theorem cycle_pre (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (i : Fin (N + 2))
    (u : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    ∀ inp work out, At i.val u m hm values n N v negative before input emitted R inp work out →
      DenseCycleFrame.Pre i u before input emitted (DenseRecordPrepare.Static m hm values n N (Source v negative R)) inp work out := by
  rintro inp work out ⟨hc, hs, hi, hu, hstatic, hend, hhead, ht⟩
  exact ⟨hc, hs, hi, hend, hu, hhead, ht, hstatic⟩

theorem prepared (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (i : Fin (N + 2))
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    ∀ inp work out, DenseRecordFrame.Pre m hm values n N i before input emitted
      (DenseRecordPrepare.Retained N (Source v negative R)) inp work out →
      DenseRecordFrame.Pre m hm values n N i before input emitted (DenseRegularRecord.Source v negative (EndFrame N R)) inp work out := by
  rintro inp work out ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hend, hhead, ht, hv, hsign, hadj, hr⟩
  exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hv, hsign, hadj, ht.1, ht.2, hend, hhead, hr⟩

theorem advanced (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (i : Fin (N + 2))
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    ∀ inp work out, DenseRecordAdvance.At (i.val + 1) m hm values n N i before input emitted
      (DenseRegularRecord.Source v negative (EndFrame N R)) inp work out →
      At (i.val + 1) (DenseComplexOriginal.vertex true i).val m hm values n N v negative before input emitted R inp work out := by
  rintro inp work out ⟨hc, hs, hi, hn, _hf, hz, hh, hN, hb, href, ha, hv, hsign, hadj, ht, hstart, hend, hhead, hr⟩
  exact ⟨hc, hs, hi, hn, ⟨hz, hh, hN, hb, href, ha, hv, hsign, hadj, hr⟩, hend, hhead, ht, hstart⟩

end JointThermoComplexity.Complexity.DenseRowFrame

#print axioms JointThermoComplexity.Complexity.DenseRowFrame.prepared
#print axioms JointThermoComplexity.Complexity.DenseRowFrame.advanced
