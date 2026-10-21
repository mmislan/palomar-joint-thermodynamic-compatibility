module
public import proofs.JointThermoComplexity.Complexity.DenseReusableClear

set_option autoImplicit false
@[expose] public section

/-! Clear a finite static list of reusable reference buffers and retain the
exact frame outside that list. -/

namespace JointThermoComplexity.Complexity.DenseReferenceClear
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun BoxBufferState
variable {w : ℕ}

def Stable (slots : List (Fin w)) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ∉ slots → next j = work j) → R work → R next
def Ready (L : ℕ) (slots : List (Fin w)) (work : Fin w → Tape) : Prop := ∀ j ∈ slots, Reusable L (work j)
def Zeros (L : ℕ) (slots : List (Fin w)) (work : Fin w → Tape) : Prop :=
  ∀ j ∈ slots, Register 0 (work j) ∧ Reusable L (work j)
def machine : List (Fin w) → TM w
  | [] => emitBitsTM []
  | idx :: slots => seqTM (BinaryBufferReset.machine idx) (machine slots)

theorem hoareTime (slots : List (Fin w)) (hnd : slots.Nodup) (L : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable slots R) :
    (machine slots).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready L slots work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Zeros L slots work ∧ R work)
      (slots.length * (12 * L + 10)) := by
  induction slots generalizing R with
  | nil =>
    have hh := FixedOutput.hoareTime [] before input emitted R
    apply hh.consequence
    · rintro inp work out ⟨hc, hs, _, hr⟩
      exact ⟨hc, hs, hr⟩
    · rintro inp work out ⟨hc, hs, hr⟩
      exact ⟨by simpa only [List.append_nil] using hc, hs, by simp only [Zeros, List.not_mem_nil, false_implies, implies_true], hr⟩
    · simp only [List.length_nil, Nat.zero_mul, le_refl]
  | cons idx slots ih =>
    have hn := List.nodup_cons.mp hnd
    let S : (Fin w → Tape) → Prop := fun work => Ready L slots work ∧ R work
    have hS : BinaryIncrementFramed.Stable idx S := by
      rintro work next he ⟨hready, hr⟩
      refine ⟨?_, hR work next (fun j hj => he j (by intro hh; apply hj; rw [hh]; exact List.mem_cons_self)) hr⟩
      intro j hj
      have hjn : j ≠ idx := by intro hh; subst j; exact hn.1 hj
      rw [he j hjn]
      exact hready j hj
    let T : (Fin w → Tape) → Prop := fun work => Register 0 (work idx) ∧ Reusable L (work idx) ∧ R work
    have hT : Stable slots T := by
      rintro work next he ⟨hz, hreuse, hr⟩
      refine ⟨by rw [he idx hn.1]; exact hz, by rw [he idx hn.1]; exact hreuse, ?_⟩
      apply hR work next _ hr
      intro j hj
      exact he j (fun hmem => hj (List.mem_cons_of_mem idx hmem))
    have hh := DenseReusableClear.hoareTime idx L before input emitted S hS
    have ht := ih (hnd := hn.2) (R := T) (hR := hT)
    have hall := seqTM_hoareTime _ _ hh (by
      rintro inp work out ⟨hc, hs, hz, hreuse, hready, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hready, hz, hreuse, hr⟩) ht
    apply hall.consequence
    · rintro inp work out ⟨hc, hs, hready, hr⟩
      exact ⟨hc, hs, hready idx List.mem_cons_self, (fun j hj => hready j (List.mem_cons_of_mem idx hj)), hr⟩
    · rintro inp work out ⟨hc, hs, hzeros, hz, hreuse, hr⟩
      refine ⟨hc, hs, ?_, hr⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨hz, hreuse⟩
      · exact hzeros j hj
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end JointThermoComplexity.Complexity.DenseReferenceClear

#print axioms JointThermoComplexity.Complexity.DenseReferenceClear.hoareTime
