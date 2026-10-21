module
public import proofs.JointThermoComplexity.Complexity.NumericCursor
public import proofs.JointThermoComplexity.Complexity.AndCursor
public import proofs.Complexitylib.Models.TuringMachine.Hoare

set_option autoImplicit false
@[expose] public section

/-!
# Canonical signed-integer fields with retained validity

The scanner consumes the sign and structural binary payload, rejecting negative zero. The composed machine
then updates a separate retained validity bit, so a later valid field cannot
erase an earlier failure. Binary numeric values are never expanded into unary.
-/

namespace JointThermoComplexity.Complexity.IntegerField
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ}

theorem scan_hoareTime (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (IntegerMachine.machine n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ R work)
      (fun inp work out =>
        Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
          (emitted ++ IntegerMachineRun.copied input) inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧
        (work (NaturalMachine.flagIndex n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted input) ∧ R work)
      (input.length + 3) := by
  rintro inp work out ⟨hc, hf, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hcells, hhead, hother, hfh, hfr, hz, hp⟩ :=
    IntegerMachineRun.run_from_cursor before emitted input
      ⟨.start, inp, work, out⟩ rfl hc.cells hc.head (fun j => (hc.works j).1) hf hc.tapePrefix hc.zero
  have hready : ∀ j, (d.work j).read ≠ Γ.start ∧ 1 ≤ (d.work j).head := by
    intro j
    by_cases hj : j = NaturalMachine.flagIndex n
    · subst j
      refine ⟨?_, by rw [hfh]⟩
      rw [hfr]
      exact Γ.ofBool_ne_start _
    · rw [hother j hj]
      exact hc.works j
  have hcursor := NumericCursor.advance hc (NumericCursor.integer_split input) hcells hhead hready hp hz
  exact ⟨d, t, ht, hreach, hhalt, hcursor, hfh, hfr, hR work d.work hother hr⟩

def machine (master : Fin (n + 1)) : TM (n + 1) :=
  seqTM (IntegerMachine.machine n) (ValidityAnd.machine master (NaturalMachine.flagIndex n))

theorem hoareTime (initial : Bool) (master : Fin (n + 1))
    (hm : master ≠ NaturalMachine.flagIndex n) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (machine master).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool initial ∧ R work)
      (fun inp work out =>
        Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
          (emitted ++ IntegerMachineRun.copied input) inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧
        (work (NaturalMachine.flagIndex n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted input) ∧
        (work master).head = 1 ∧
        (work master).read = Γ.ofBool (initial && NaturalMachineParser.integerAccepted input) ∧ R work)
      (input.length + 5) := by
  let RN : (Fin (n + 1) → Tape) → Prop := fun work =>
    (work master).head = 1 ∧ (work master).read = Γ.ofBool initial ∧ R work
  have hRN : ∀ work work', (∀ j, j ≠ NaturalMachine.flagIndex n → work' j = work j) → RN work → RN work' := by
    rintro work work' h ⟨hh, hv, hr⟩
    have he := h master hm
    refine ⟨by simpa only [he] using hh, by simpa only [he] using hv, ?_⟩
    exact hR work work' (fun j _ hj => h j hj) hr
  let RA : (Fin (n + 1) → Tape) → Prop := fun work =>
    (work (NaturalMachine.flagIndex n)).head = 1 ∧
    (work (NaturalMachine.flagIndex n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted input) ∧ R work
  have hRA : ∀ work work', (∀ j, j ≠ master → work' j = work j) → RA work → RA work' := by
    rintro work work' h ⟨hh, hv, hr⟩
    have he := h (NaturalMachine.flagIndex n) hm.symm
    refine ⟨by simpa only [he] using hh, by simpa only [he] using hv, ?_⟩
    exact hR work work' (fun j hj _ => h j hj) hr
  have hscan := scan_hoareTime before input emitted RN hRN
  have hand := AndCursor.hoareTime master (NaturalMachine.flagIndex n) initial
    (NaturalMachineParser.integerAccepted input)
    (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
    (emitted ++ IntegerMachineRun.copied input) RA hRA
  have hseq := seqTM_hoareTime (IntegerMachine.machine n)
    (ValidityAnd.machine master (NaturalMachine.flagIndex n)) hscan (by
      rintro inp work out ⟨hc, hfh, hfr, hmh, hmr, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hmh, hmr, hfr, hfh, hfr, hr⟩) hand
  apply HoareTime.strengthen_post hseq
  rintro inp work out ⟨hc, hmh, hmr, hfh, hfr, hr⟩
  exact ⟨hc, hfh, hfr, hmh, hmr, hr⟩

end JointThermoComplexity.Complexity.IntegerField

#print axioms JointThermoComplexity.Complexity.IntegerField.scan_hoareTime
#print axioms JointThermoComplexity.Complexity.IntegerField.hoareTime
