module
public import proofs.JointThermoComplexity.Complexity.DenseFactorFrame

set_option autoImplicit false
@[expose] public section

/-! Common returned row fields and their two physical complex-frame views. -/

namespace JointThermoComplexity.Complexity.DenseRecordFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseComplexOriginal
variable {N : ℕ}

def Fields (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register i.val (work 38) ∧ Register (vertex true i).val (work 41) ∧
    (work 43).read = Γ.ofBool (decide (i.val ≠ N + 1)) ∧ Register 0 (work 39) ∧
    (work 42).head = 1 ∧ IsReg N (work 33) ∧ IsReg (N + 2) (work 34) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧ IsReg n (work 16) ∧ R work
def Pre (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Fields m hm values n N i R work

def ReactR (i : Fin (N + 2)) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register (vertex true i).val (work 41) ∧ DenseProductBranch.FlagFrame i R work
def ProductR (i : Fin (N + 2)) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register i.val (work 38) ∧ R work

theorem react_stable (i : Fin (N + 2)) (R : (Fin 64 → Tape) → Prop) (hR : DenseComplexPorts.Stable false R) :
    DenseComplexPorts.Stable false (ReactR i R) := by
  rintro work next he ⟨hn, hf, hr⟩
  exact ⟨by rw [he 41 (by unfold DenseComplexPorts.Outside DenseComplexPorts.target; decide)]; exact hn,
    by rw [he 43 (by unfold DenseComplexPorts.Outside DenseComplexPorts.target; decide)]; exact hf,
    hR work next he hr⟩
theorem product_stable (i : Fin (N + 2)) (R : (Fin 64 → Tape) → Prop) (hR : DenseComplexPorts.Stable true R) :
    DenseComplexPorts.Stable true (ProductR i R) := by
  rintro work next he ⟨hi, hr⟩
  exact ⟨by rw [he 38 (by unfold DenseComplexPorts.Outside DenseComplexPorts.target; decide)]; exact hi, hR work next he hr⟩

theorem react_iff (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (inp : Tape) (work : Fin 64 → Tape) (out : Tape) :
    Pre m hm values n N i before input emitted R inp work out ↔
      DenseComplexFrame.Pre false m hm values n N (vertex false i).val before input emitted (ReactR i R) inp work out := by
  constructor
  · rintro ⟨hc, hs, hi, hn, hf, hz, hh, hN, hbranch, href, ha, hr⟩
    exact ⟨hc, hs, hz, hi, hh, hN, hbranch, href, ha, hn, hf, hr⟩
  · rintro ⟨hc, hs, hz, hi, hh, hN, hbranch, href, ha, hn, hf, hr⟩
    exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hbranch, href, ha, hr⟩

theorem product_iff (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (inp : Tape) (work : Fin 64 → Tape) (out : Tape) :
    Pre m hm values n N i before input emitted R inp work out ↔
      DenseComplexFrame.Pre true m hm values n N (vertex true i).val before input emitted
        (DenseProductBranch.FlagFrame i (ProductR i R)) inp work out := by
  constructor
  · rintro ⟨hc, hs, hi, hn, hf, hz, hh, hN, hbranch, href, ha, hr⟩
    exact ⟨hc, hs, hz, hn, hh, hN, hbranch, href, ha, hf, hi, hr⟩
  · rintro ⟨hc, hs, hz, hn, hh, hN, hbranch, href, ha, hf, hi, hr⟩
    exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hbranch, href, ha, hr⟩

theorem fields_factor_stable (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (R : (Fin 64 → Tape) → Prop) (hR : DenseFactorFrame.Stable R) :
    DenseFactorFrame.Stable (Fields m hm values n N i R) := by
  rintro work next he ⟨hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
  refine ⟨by rw [he 38 (by decide) (by decide)]; exact hi,
    by rw [he 41 (by decide) (by decide)]; exact hn,
    by rw [he 43 (by decide) (by decide)]; exact hf,
    by rw [he 39 (by decide) (by decide)]; exact hz,
    by rw [he 42 (by decide) (by decide)]; exact hh,
    by rw [he 33 (by decide) (by decide)]; exact hN,
    by rw [he 34 (by decide) (by decide)]; exact hb, ?_,
    by rw [he 16 (by decide) (by decide)]; exact ha, hR work next he hr⟩
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  have hrange : 2 ≤ (DensePowerPorts.reference m hm j).val ∧ (DensePowerPorts.reference m hm j).val ≤ 5 := by
    change 2 ≤ 2 + j.val ∧ 2 + j.val ≤ 5
    constructor <;> omega
  have hflag : 44 ≤ (DensePowerPorts.flag m hm j).val ∧ (DensePowerPorts.flag m hm j).val ≤ 47 := by
    change 44 ≤ 44 + j.val ∧ 44 + j.val ≤ 47
    constructor <;> omega
  have away (q : Fin 64) (hq : q.val ≤ 5 ∨ 44 ≤ q.val ∧ q.val ≤ 47) : q ≠ 12 ∧ q ≠ 63 := by
    constructor
    · intro hh
      have hv := congrArg Fin.val hh
      change q.val = 12 at hv
      omega
    · intro hh
      have hv := congrArg Fin.val hh
      change q.val = 63 at hv
      omega
  have hc := away (DensePowerPorts.reference m hm j) (Or.inl hrange.2)
  have hf := away (DensePowerPorts.flag m hm j) (Or.inr hflag)
  change Register (values (DensePowerPorts.reference m hm j)) (next (DensePowerPorts.reference m hm j)) ∧
    (next (DensePowerPorts.flag m hm j)).head = 1
  rw [he _ hc.1 hc.2, he _ hf.1 hf.2]
  exact href (DensePowerPorts.comparison m hm j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

end JointThermoComplexity.Complexity.DenseRecordFrame

#print axioms JointThermoComplexity.Complexity.DenseRecordFrame.react_iff
#print axioms JointThermoComplexity.Complexity.DenseRecordFrame.product_iff
#print axioms JointThermoComplexity.Complexity.DenseRecordFrame.fields_factor_stable
