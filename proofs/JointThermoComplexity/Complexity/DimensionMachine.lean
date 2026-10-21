module
public import proofs.JointThermoComplexity.Complexity.HeaderAt
public import proofs.JointThermoComplexity.Complexity.DimensionHeaders
public import proofs.Complexitylib.Models.TuringMachine.Hoare

set_option autoImplicit false
@[expose] public section

/-! Three retained dimension registers, using actual sequential TM composition. -/

namespace JointThermoComplexity.Complexity.DimensionMachine
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def slot (n : ℕ) (j : Fin 3) : Fin (n + 4) := ⟨n + j.val, by omega⟩
def flag (n : ℕ) : Fin (n + 4) := HeaderMachine.flagIndex (n + 2)

theorem slot_injective (n : ℕ) : Function.Injective (slot n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [slot] using hv

theorem slot_ne_flag (n : ℕ) (j : Fin 3) : slot n j ≠ flag n := by
  intro h
  have hv := congrArg Fin.val h
  simp [slot, flag, HeaderMachine.flagIndex, NaturalMachine.flagIndex] at hv
  omega

def permutation (n : ℕ) (j : Fin 3) : Fin (n + 4) ≃ Fin (n + 4) :=
  Equiv.swap (HeaderMachine.counterIndex (n + 2)) (slot n j)

@[simp] theorem counter_permutation (n : ℕ) (j : Fin 3) :
    HeaderAt.counter (permutation n j) = slot n j := by
  simp [HeaderAt.counter, permutation]

@[simp] theorem flag_permutation (n : ℕ) (j : Fin 3) :
    HeaderAt.flag (permutation n j) = flag n := by
  have h₀ := (HeaderMachine.counter_ne_flag (n + 2)).symm
  have h₁ := (slot_ne_flag n j).symm
  simpa [HeaderAt.flag, permutation, flag] using Equiv.swap_apply_of_ne_of_ne h₀ h₁

def header (n : ℕ) (j : Fin 3) : TM (n + 4) := HeaderAt.machine (permutation n j)

def Registers {n : ℕ} (v : Fin 3 → ℕ) (work : Fin (n + 4) → Tape) : Prop :=
  ∀ j, IsReg (v j) (work (slot n j))

def Frame {n : ℕ} (before remaining emitted : List Bool) (v : Fin 3 → ℕ)
    (P : (Fin (n + 4) → Tape) → Prop) : _root_.Complexity.TM.TapePred (n + 4) :=
  fun inp work out => Cursor before remaining emitted inp work out ∧
    Registers v work ∧ (work (flag n)).head = 1 ∧ P work

theorem header_hoareTime (n : ℕ) (j : Fin 3) (before remaining emitted : List Bool)
    (v : Fin 3 → ℕ) (hv : v j = 0) (P : (Fin (n + 4) → Tape) → Prop)
    (hP : ∀ work work', (∀ i, i ≠ slot n j → i ≠ flag n → work' i = work i) → P work → P work') :
    (header n j).HoareTime (Frame before remaining emitted v P)
      (fun inp work out =>
        Frame (before ++ HeaderControl.copied remaining) (HeaderControl.suffix remaining)
          (emitted ++ HeaderControl.copied remaining) (Function.update v j (HeaderControl.count remaining)) P inp work out ∧
        (work (flag n)).read = Γ.ofBool (HeaderControl.valid remaining))
      (2 * HeaderControl.count remaining + 5) := by
  rintro inp work out ⟨hc, hregs, hf, hp⟩
  have hr : IsReg 0 (work (HeaderAt.counter (permutation n j))) := by
    simpa only [counter_permutation, hv] using hregs j
  have hf' : (work (HeaderAt.flag (permutation n j))).head = 1 := by simpa using hf
  obtain ⟨d, t, ht, hreach, hhalt, hcursor, hreg, hfh, hfr, hother⟩ :=
    HeaderAt.run (permutation n j) before remaining emitted ⟨.start, inp, work, out⟩ rfl hc hr hf'
  simp only [counter_permutation, flag_permutation] at hreg hfh hfr hother
  have hregs' : Registers (Function.update v j (HeaderControl.count remaining)) d.work := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa only [Function.update_self] using hreg
    · have hslots : slot n k ≠ slot n j := fun h => hkj (slot_injective n h)
      rw [Function.update_of_ne hkj, hother (slot n k) hslots (slot_ne_flag n k)]
      exact hregs k
  exact ⟨d, t, ht, hreach, hhalt, ⟨hcursor, hregs', hfh, hP work d.work hother hp⟩, hfr⟩

def machine (n : ℕ) : TM (n + 4) := seqTM (seqTM (header n 0) (header n 1)) (header n 2)

theorem hoareTime (n : ℕ) (before remaining emitted : List Bool)
    (P : (Fin (n + 4) → Tape) → Prop)
    (hP : ∀ j work work', (∀ i, i ≠ slot n j → i ≠ flag n → work' i = work i) → P work → P work') :
    (machine n).HoareTime (Frame before remaining emitted (fun _ => 0) P)
      (fun inp work out =>
        Cursor (((before ++ HeaderControl.copied remaining) ++ HeaderControl.copied (DimensionHeaders.tail₁ remaining)) ++
          HeaderControl.copied (DimensionHeaders.tail₂ remaining)) (DimensionHeaders.tail₃ remaining)
          (((emitted ++ HeaderControl.copied remaining) ++ HeaderControl.copied (DimensionHeaders.tail₁ remaining)) ++
            HeaderControl.copied (DimensionHeaders.tail₂ remaining)) inp work out ∧
        IsReg (DimensionHeaders.species remaining) (work (slot n 0)) ∧
        IsReg (DimensionHeaders.reactions remaining) (work (slot n 1)) ∧
        IsReg (DimensionHeaders.cores remaining) (work (slot n 2)) ∧
        (work (flag n)).head = 1 ∧
        (work (flag n)).read = Γ.ofBool (DimensionHeaders.accepted remaining) ∧ P work)
      (2 * remaining.length + 17) := by
  let a := HeaderControl.copied remaining
  let b := HeaderControl.copied (DimensionHeaders.tail₁ remaining)
  let c := HeaderControl.copied (DimensionHeaders.tail₂ remaining)
  let v₁ : Fin 3 → ℕ := Function.update (fun _ => 0) 0 (HeaderControl.count remaining)
  let v₂ : Fin 3 → ℕ := Function.update v₁ 1 (HeaderControl.count (DimensionHeaders.tail₁ remaining))
  let v₃ : Fin 3 → ℕ := Function.update v₂ 2 (HeaderControl.count (DimensionHeaders.tail₂ remaining))
  have h₀ := header_hoareTime n 0 before remaining emitted (fun _ => 0) rfl P (hP 0)
  have h₁ := header_hoareTime n 1 (before ++ a) (DimensionHeaders.tail₁ remaining)
    (emitted ++ a) v₁ (by simp [v₁]) P (hP 1)
  have h₂ := header_hoareTime n 2 ((before ++ a) ++ b) (DimensionHeaders.tail₂ remaining)
    ((emitted ++ a) ++ b) v₂ (by simp [v₂, v₁]) P (hP 2)
  have h₀₁ := seqTM_hoareTime (header n 0) (header n 1) h₀ (by
    rintro inp work out ⟨hframe, _⟩
    obtain ⟨hi, hw, ho⟩ := hframe.1.phase
    simpa only [hi, hw, ho, a, v₁, DimensionHeaders.tail₁] using hframe) h₁
  have h₀₁₂ := seqTM_hoareTime (seqTM (header n 0) (header n 1)) (header n 2) h₀₁ (by
    rintro inp work out ⟨hframe, _⟩
    obtain ⟨hi, hw, ho⟩ := hframe.1.phase
    simpa only [hi, hw, ho, b, v₂, DimensionHeaders.tail₂] using hframe) h₂
  apply HoareTime.mono_bound (b :=
    (2 * HeaderControl.count remaining + 5 + 1 + (2 * HeaderControl.count (DimensionHeaders.tail₁ remaining) + 5)) + 1 +
      (2 * HeaderControl.count (DimensionHeaders.tail₂ remaining) + 5))
  · apply HoareTime.strengthen_post h₀₁₂
    rintro inp work out ⟨⟨hc, hregs, hf, hp⟩, hstatus⟩
    change Registers v₃ work at hregs
    refine ⟨hc, ?_, ?_, ?_, hf, ?_, hp⟩
    · simpa [v₃, v₂, v₁, DimensionHeaders.species] using hregs 0
    · simpa [v₃, v₂, v₁, DimensionHeaders.reactions] using hregs 1
    · simpa [v₃, DimensionHeaders.cores] using hregs 2
    · simpa only [DimensionHeaders.accepted_eq_last] using hstatus
  · have hsum := DimensionHeaders.count_sum_bound remaining
    simp only [DimensionHeaders.species, DimensionHeaders.reactions, DimensionHeaders.cores] at hsum
    omega

end JointThermoComplexity.Complexity.DimensionMachine

#print axioms JointThermoComplexity.Complexity.DimensionMachine.header_hoareTime
#print axioms JointThermoComplexity.Complexity.DimensionMachine.hoareTime
