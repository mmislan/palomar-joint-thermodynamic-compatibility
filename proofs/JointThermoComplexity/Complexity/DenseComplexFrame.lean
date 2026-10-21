module
public import proofs.JointThermoComplexity.Complexity.DenseComplexPorts

set_option autoImplicit false
@[expose] public section

/-! Reframe returned internal/external blocks without asserting logical fuel inside their loops. -/

namespace JointThermoComplexity.Complexity.DenseComplexFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseComplexPorts

def InternalR (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n : ℕ) (R : (Fin 64 → Tape) → Prop)
    (work : Fin 64 → Tape) : Prop :=
  PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧ IsReg n (work 16) ∧ R work

def ExternalR (product : Bool) (N M : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register M (work (target product)) ∧ (work 42).head = 1 ∧ IsReg N (work 33) ∧ IsReg (N + 2) (work 34) ∧ R work

def Pre (product : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N M : ℕ)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  DenseInternalBlocks.Pre (ports product) N M 0 before input emitted (InternalR m hm values n R)

theorem internal_stable (product : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n : ℕ)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    DenseInternalBlocks.Stable (ports product) (InternalR m hm values n R) := by
  rintro work next he ⟨hr, hn, hx⟩
  have keep (j : Fin 64) (hj : j.val ≤ 16 ∨ 44 ≤ j.val ∧ j.val < 48) : next j = work j := by
    have ha := internal_away product j hj
    exact he j ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    have hd := keep (DensePowerPorts.reference m hm i) (Or.inl (by change 2 + i.val ≤ 16; omega))
    have hf := keep (DensePowerPorts.flag m hm i) (Or.inr (by change 44 ≤ 44 + i.val ∧ 44 + i.val < 48; constructor <;> omega))
    change Register (values (DensePowerPorts.reference m hm i)) (next (DensePowerPorts.reference m hm i)) ∧
      (next (DensePowerPorts.flag m hm i)).head = 1
    rw [hd, hf]
    exact hr (DensePowerPorts.comparison m hm i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · rw [keep 16 (Or.inl (by decide))]
    exact hn
  · apply hR work next _ hx
    intro j hj
    exact he j hj.1 hj.2.1 hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2.1

theorem external_stable (product : Bool) (m : ℕ) (hm : m ≤ 4) (N M : ℕ)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable product R) :
    PowerVectorLoop.Stable (DensePowerPorts.layout m hm) (ExternalR product N M R) := by
  rintro work next he ⟨ht, hf, hn, hb, hx⟩
  have away (j : Fin 64) (hj : j.val < 44 ∨ 48 ≤ j.val) :
      ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, j ≠ p.flag := by
    intro p hp hh
    have hr := power_flag_range m hm p hp
    have hv := congrArg (fun k : Fin 64 => k.val) hh
    omega
  have keep (j : Fin 64) (hi : j ≠ 39) (hfu : j ≠ 16) (hj : j.val < 44) : next j = work j :=
    he j hi (away j (Or.inl hj)) hfu
  have hti : target product ≠ (39 : Fin 64) := by cases product <;> decide
  have htf : target product ≠ (16 : Fin 64) := by cases product <;> decide
  have htr := target_range product
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [keep (target product) hti htf (by omega)]
    exact ht
  · rw [keep 42 (by decide) (by decide) (by decide)]
    exact hf
  · rw [keep 33 (by decide) (by decide) (by decide)]
    exact hn
  · rw [keep 34 (by decide) (by decide) (by decide)]
    exact hb
  · apply hR work next _ hx
    intro j hj
    exact he j hj.1 (away j hj.2.2.2.2.2.2) hj.2.2.2.2.2.1

theorem external_iff (product : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N M : ℕ)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (inp : Tape) (work : Fin 64 → Tape) (out : Tape) :
    Pre product m hm values n N M before input emitted R inp work out ↔
      DenseExternalPower.Pre m hm values n before input emitted (ExternalR product N M R) inp work out := by
  constructor
  · rintro ⟨hc, hs, hi, ht, hf, hn, hb, hr, ha, hx⟩
    exact ⟨hc, hs, hi, hr, ha, ht, hf, hn, hb, hx⟩
  · rintro ⟨hc, hs, hi, hr, ha, ht, hf, hn, hb, hx⟩
    exact ⟨hc, hs, hi, ht, hf, hn, hb, hr, ha, hx⟩

theorem phase (product : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N M : ℕ)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    ∀ inp work out, Pre product m hm values n N M before input emitted R inp work out →
      Pre product m hm values n N M before input emitted R (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out hp
  obtain ⟨hi, hw, ho⟩ := hp.1.phase
  rw [hi, hw, ho]
  exact hp

end JointThermoComplexity.Complexity.DenseComplexFrame

#print axioms JointThermoComplexity.Complexity.DenseComplexFrame.internal_stable
#print axioms JointThermoComplexity.Complexity.DenseComplexFrame.external_stable
#print axioms JointThermoComplexity.Complexity.DenseComplexFrame.external_iff
