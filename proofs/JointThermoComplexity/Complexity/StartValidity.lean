module
public import proofs.JointThermoComplexity.Complexity.WriteStatus
public import proofs.Complexitylib.Models.TuringMachine.Hoare

set_option autoImplicit false
@[expose] public section

/-! Copy checked header status into the retained record-validity cell. -/

namespace JointThermoComplexity.Complexity.StartValidity
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (master flag : Fin w) : TM w :=
  seqTM (WriteStatus.machine master true) (ValidityAnd.machine master flag)

theorem hoareTime (master flag : Fin w) (hm : master ≠ flag) (header : Bool)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ master → work' j = work j) → R work → R work') :
    (machine master flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work master).head = 1 ∧ (work flag).head = 1 ∧ (work flag).read = Γ.ofBool header ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work master).head = 1 ∧ (work master).read = Γ.ofBool header ∧
        (work flag).head = 1 ∧ (work flag).read = Γ.ofBool header ∧ R work) 3 := by
  let RP : (Fin w → Tape) → Prop := fun work =>
    (work flag).head = 1 ∧ (work flag).read = Γ.ofBool header ∧ R work
  have hRP : ∀ work work', (∀ j, j ≠ master → work' j = work j) → RP work → RP work' := by
    rintro work work' h ⟨hh, hv, hr⟩
    exact ⟨by simpa only [h flag hm.symm] using hh, by simpa only [h flag hm.symm] using hv,
      hR work work' h hr⟩
  have hw := WriteStatus.hoareTime master true before input emitted RP hRP
  have ha := AndCursor.hoareTime master flag true header before input emitted RP hRP
  have hseq := seqTM_hoareTime (WriteStatus.machine master true) (ValidityAnd.machine master flag) hw (by
    rintro inp work out ⟨hc, hmh, hmr, hfh, hfr, hr⟩
    obtain ⟨hi, hwork, ho⟩ := hc.phase
    rw [hi, hwork, ho]
    exact ⟨hc, hmh, hmr, hfr, hfh, hfr, hr⟩) ha
  apply HoareTime.strengthen_post hseq
  rintro inp work out ⟨hc, hmh, hmr, hfh, hfr, hr⟩
  exact ⟨hc, hmh, by simpa only [Bool.true_and] using hmr, hfh, hfr, hr⟩

end JointThermoComplexity.Complexity.StartValidity

#print axioms JointThermoComplexity.Complexity.StartValidity.hoareTime
