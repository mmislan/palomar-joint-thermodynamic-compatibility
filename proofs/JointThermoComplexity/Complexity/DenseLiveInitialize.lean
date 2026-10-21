module
public import proofs.JointThermoComplexity.Complexity.DenseEndFrame
public import proofs.JointThermoComplexity.Complexity.DenseFixedSourceBank

set_option autoImplicit false
@[expose] public section

/-! One-time allocation from the fresh high workspace, ending setup and actual
reference clearing. Later uses receive reusable fields rather than Fresh. -/

namespace JointThermoComplexity.Complexity.DenseLiveInitialize
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun BoxBufferState

def zeroKeys : List (Fin 64) := [38, 39, 41, 42, 43, 44, 45, 46, 47]
def Fields (L n N U : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  DenseSourceFrame.Parser L work ∧ (work 12).head = 1 ∧ IsReg n (work 16) ∧ IsReg N (work 33) ∧
    IsReg (N + 2) (work 34) ∧ Register U (work 13) ∧ (∀ j ∈ zeroKeys, work j = regTape 0) ∧ R work
def Pre (L n N U : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    DenseSourceFrame.Parser L work ∧ (work 12).head = 1 ∧ IsReg n (work 16) ∧ IsReg N (work 33) ∧
      IsReg (N + 2) (work 34) ∧ Register N (work 17) ∧ Register U (work 13) ∧
        (∀ j, 38 ≤ j.val → work j = regTape 0) ∧ R work
def Retained (N U : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register N (work 17) ∧ Register U (work 13) ∧ R work
def Marks (L : ℕ) (work : Fin 64 → Tape) : Prop :=
  Reusable L (work 0) ∧ (work 1).head = 1 ∧ (work 6).head = 1 ∧ (work 7).head = 1 ∧
    (work 8).head = 1 ∧ (work 9).head = 1 ∧ (work 10).head = 1 ∧ (work 11).head = 1
def ClearFrame (L n N U : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Marks L work ∧ DenseSourceFrame.Core n N 0 (Retained N U R) work

theorem fields_stable (L n N U : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : DenseEndFrame.Stable R) :
    DenseEndFrame.Stable (Fields L n N U R) := by
  rintro work next he ⟨hp, hh, ha, hn, hb, hu, hz, hr⟩
  refine ⟨DenseSourceFrame.parser_transfer L work next (by
    intro j hj
    apply he j
    · intro h; have hv := congrArg Fin.val h; change j.val = 40 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change j.val = 63 at hv; omega) hp,
    by rw [he 12 (by decide) (by decide)]; exact hh,
    by rw [he 16 (by decide) (by decide)]; exact ha,
    by rw [he 33 (by decide) (by decide)]; exact hn,
    by rw [he 34 (by decide) (by decide)]; exact hb,
    by rw [he 13 (by decide) (by decide)]; exact hu, ?_, hR work next he hr⟩
  intro j hj
  have hsafe : ∀ j : Fin 64, j ∈ zeroKeys → j ≠ 40 ∧ j ≠ 63 := by decide
  rw [he j (hsafe j hj).1 (hsafe j hj).2]
  exact hz j hj

theorem retained_stable (N U : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : DenseSourceFrame.Stable R) :
    DenseSourceFrame.Stable (Retained N U R) := by
  rintro work next he ⟨hn, hu, hr⟩
  have h17 : DenseSourceFrame.Outside (17 : Fin 64) := by unfold DenseSourceFrame.Outside DenseRowFrame.Outside; decide
  have h13 : DenseSourceFrame.Outside (13 : Fin 64) := by unfold DenseSourceFrame.Outside DenseRowFrame.Outside; decide
  exact ⟨by rw [he 17 h17]; exact hn, by rw [he 13 h13]; exact hu, hR work next he hr⟩

theorem marks_of_parser (L : ℕ) (work : Fin 64 → Tape) (hp : DenseSourceFrame.Parser L work) : Marks L work :=
  ⟨hp.1, hp.2.1, (hp.2.2.1 (2, 6) (by decide)).2, (hp.2.2.1 (3, 7) (by decide)).2,
    (hp.2.2.1 (4, 8) (by decide)).2, (hp.2.2.1 (5, 9) (by decide)).2, hp.2.2.2.1, hp.2.2.2.2⟩

theorem clear_stable (L n N U : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : DenseSourceFrame.Stable R) :
    DenseReferenceClear.Stable (DenseReferenceBank.unused 0) (ClearFrame L n N U R) := by
  rintro work next he ⟨⟨hb, h1, h6, h7, h8, h9, h10, h11⟩, hcore⟩
  refine ⟨⟨by rw [he 0 (by decide)]; exact hb, by rw [he 1 (by decide)]; exact h1,
    by rw [he 6 (by decide)]; exact h6, by rw [he 7 (by decide)]; exact h7,
    by rw [he 8 (by decide)]; exact h8, by rw [he 9 (by decide)]; exact h9,
    by rw [he 10 (by decide)]; exact h10, by rw [he 11 (by decide)]; exact h11⟩,
    DenseSourceFrame.core_bank_stable 0 n N 0 (Retained N U R) (retained_stable N U R hR) work next he hcore⟩

theorem parser_of_bank (L : ℕ) (work : Fin 64 → Tape) (hb : DenseReferenceBank.Bank L [] work) (hm : Marks L work) :
    DenseSourceFrame.Parser L work := by
  rcases hm with ⟨h0, h1, h6, h7, h8, h9, h10, h11⟩
  refine ⟨h0, h1, ?_, h10, h11⟩
  intro p hp
  have hh : p ∈ ([(2, 6), (3, 7), (4, 8), (5, 9)] : List (Fin 64 × Fin 64)) := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact ⟨(hb 0).2, h6⟩
  · exact ⟨(hb 1).2, h7⟩
  · exact ⟨(hb 2).2, h8⟩
  · exact ⟨(hb 3).2, h9⟩

def machine : TM 64 := seqTM DenseEndRegister.machine (DenseReferenceBank.machine 0)
def timeBound (L B : ℕ) : ℕ := (14 * B + 50) + 1 + 4 * (12 * L + 10)

theorem hoareTime (L n N U B : ℕ) (hN : N.bits.length ≤ B) (before input emitted : List Bool)
    (R : (Fin 64 → Tape) → Prop) (hRe : DenseEndFrame.Stable R) (hRs : DenseSourceFrame.Stable R) :
    machine.HoareTime (Pre L n N U before input emitted R)
      (DenseFixedSourceBank.Pre L n N U 0 (DenseRawReady.values []) before input emitted (Retained N U R))
      (timeBound L B) := by
  have he := DenseEndFrame.hoareTime N 0 B hN (by simp only [Nat.zero_bits, List.length_nil]; omega)
    before input emitted (Fields L n N U R) (fields_stable L n N U R hRe)
  have hclear := DenseReferenceBank.hoareTime L [] (by decide) before input emitted (ClearFrame L n N U R) (clear_stable L n N U R hRs)
  have h1 : DenseEndRegister.machine.HoareTime (Pre L n N U before input emitted R)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        DenseReferenceClear.Ready L DenseReferenceBank.slots work ∧ DenseReferenceBank.Present [] (by decide) work ∧ ClearFrame L n N U R work)
      (14 * B + 50) := by
    apply he.consequence
    · rintro inp work out ⟨hc, hs, hp, hh, ha, hn, hb, hN', hU, hz, hr⟩
      have reg0 (j : Fin 64) (hj : 38 ≤ j.val) : IsReg 0 (work j) := by rw [hz j hj]; exact reg_regT 0
      refine ⟨hc, hs, hN', AddressCodeProgram.binary_zero (reg0 40 (by decide)),
        ⟨CountTape.empty_prefix_of_zero (reg0 63 (by decide)), (reg0 63 (by decide)).cell0⟩,
        hp, hh, ha, hn, hb, hU, ?_, hr⟩
      intro j hj
      have high : ∀ j : Fin 64, j ∈ zeroKeys → 38 ≤ j.val := by decide
      exact hz j (high j hj)
    · rintro inp work out ⟨hc, hs, hN', hend, ht, hp, hh, ha, hn, hb, hU, hz, hr⟩
      have reg0 (j : Fin 64) (hj : j ∈ zeroKeys) : IsReg 0 (work j) := by rw [hz j hj]; exact reg_regT 0
      have core : DenseSourceFrame.Core n N 0 (Retained N U R) work :=
        ⟨hh, ha, hn, hb, AddressCodeProgram.binary_zero (reg0 38 (by decide)),
          ⟨0, by omega, AddressCodeProgram.binary_zero (reg0 41 (by decide))⟩,
          AddressCodeProgram.binary_zero (reg0 39 (by decide)), (reg0 42 (by decide)).head_eq,
          hend, (reg0 43 (by decide)).head_eq, (by
            intro i
            have hkey : ∀ i : Fin 4, DensePowerPorts.flag 4 (by decide) i ∈ zeroKeys := by decide
            exact (reg0 _ (hkey i)).head_eq), ht, ⟨hN', hU, hr⟩⟩
      exact ⟨hc, hs, DenseSourceFrame.ref_ready L work hp, (by intro i; exact Fin.elim0 i), marks_of_parser L work hp, core⟩
    · exact le_rfl
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) hclear
  apply hh.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hs, hbank, hm, hcore⟩
    have href : PowerVectorUnit.Refs (DensePowerPorts.cellLayout 4 (by decide)) (DenseRawReady.values []) work := by
      apply DensePowerPorts.refs
      · intro i; exact (hbank i).1
      · exact hcore.powers
    exact ⟨⟨hc, hs, parser_of_bank L work hbank hm, hcore⟩, hcore.frame.2.1, href⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseLiveInitialize

#print axioms JointThermoComplexity.Complexity.DenseLiveInitialize.hoareTime
