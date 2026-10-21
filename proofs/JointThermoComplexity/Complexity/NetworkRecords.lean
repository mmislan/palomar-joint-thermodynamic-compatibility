module
public import proofs.JointThermoComplexity.Complexity.NetworkScanner
public import proofs.JointThermoComplexity.Complexity.EndScanner

set_option autoImplicit false
@[expose] public section

/-! Complete network records followed by actual rejection of trailing binary data. -/

namespace JointThermoComplexity.Complexity.NetworkRecords
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec

variable {n : ℕ}

def machine (species reactions cores master : Fin (n + 1)) : TM (n + 1) :=
  seqTM (NetworkScanner.machine species reactions cores master) (EndScanner.machine master)

def accepted (ns nr nc : ℕ) (input : List Bool) : Bool :=
  (RecordControl.network ns nr nc).valid input && ((RecordControl.network ns nr nc).rest input).isEmpty

theorem hoareTime (species reactions cores master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hr : reactions ≠ NaturalMachine.flagIndex n)
    (hc : cores ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n)
    (hsm : species ≠ master) (hrm : reactions ≠ master) (hcm : cores ≠ master)
    (hsr : species ≠ reactions) (hsc : species ≠ cores) (hrc : reactions ≠ cores)
    (ns nr nc : ℕ) (initial : Bool) (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (machine species reactions cores master).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool initial ∧ NetworkScanner.Env species reactions cores ns nr nc work ∧ R work)
      (fun inp work out =>
        Cursor (before ++ (RecordControl.network ns nr nc).taken input) ((RecordControl.network ns nr nc).rest input)
          (emitted ++ (RecordControl.network ns nr nc).taken input) inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool (initial && accepted ns nr nc input) ∧
        NetworkScanner.Env species reactions cores ns nr nc work ∧ R work)
      (NetworkScanner.timeBound ns nr nc input.length + 2) := by
  let RA : (Fin (n + 1) → Tape) → Prop := fun work =>
    (work (NaturalMachine.flagIndex n)).head = 1 ∧ NetworkScanner.Env species reactions cores ns nr nc work ∧ R work
  have hRA : ∀ work work', (∀ j, j ≠ master → work' j = work j) → RA work → RA work' := by
    rintro work work' h ⟨hf, ⟨hss, hrr, hcc⟩, hr'⟩
    refine ⟨?_, ⟨?_, ?_, ?_⟩, hR work work' (fun j hj _ => h j hj) hr'⟩
    · simpa only [h (NaturalMachine.flagIndex n) hm.symm] using hf
    · simpa only [h species hsm] using hss
    · simpa only [h reactions hrm] using hrr
    · simpa only [h cores hcm] using hcc
  have hscan := NetworkScanner.runs species reactions cores master hs hr hc hm hsm hrm hcm hsr hsc hrc ns nr nc
    initial before input emitted R hR
  have hend := EndScanner.hoareTime master (initial && (RecordControl.network ns nr nc).valid input)
    (before ++ (RecordControl.network ns nr nc).taken input) ((RecordControl.network ns nr nc).rest input)
    (emitted ++ (RecordControl.network ns nr nc).taken input) RA hRA
  have hseq := seqTM_hoareTime (NetworkScanner.machine species reactions cores master) (EndScanner.machine master)
    hscan (by
      rintro inp work out ⟨hcur, hf, hmh, hmr, he, hr'⟩
      obtain ⟨hi, hw, ho⟩ := hcur.phase
      rw [hi, hw, ho]
      exact ⟨hcur, hmh, hmr, hf, he, hr'⟩) hend
  apply HoareTime.strengthen_post hseq
  rintro inp work out ⟨hcur, hmh, hmr, hf, he, hr'⟩
  refine ⟨hcur, hf, hmh, ?_, he, hr'⟩
  simpa only [accepted, Bool.and_assoc] using hmr

theorem status_iff_parse_empty (ns nr nc : ℕ) (input : List Bool) :
    accepted ns nr nc input = true ↔ ∃ Q, (DataCodec.network ns nr nc).parse input = some (Q, []) := by
  let S := RecordControl.network ns nr nc
  cases hp : (DataCodec.network ns nr nc).parse input with
  | none =>
    have hv : S.valid input ≠ true := by
      intro h
      obtain ⟨Q, rest, hparse⟩ := (S.accepts input).mp h
      simp [hp] at hparse
    change S.valid input && (S.rest input).isEmpty = true ↔ _
    simp [hv]
  | some pair =>
    obtain ⟨Q, rest⟩ := pair
    have hv := (S.accepts input).mpr ⟨Q, rest, hp⟩
    have hr := (S.parsed hp).2
    change S.valid input && (S.rest input).isEmpty = true ↔ _
    simp [hv, hr]

end JointThermoComplexity.Complexity.NetworkRecords

#print axioms JointThermoComplexity.Complexity.NetworkRecords.hoareTime
#print axioms JointThermoComplexity.Complexity.NetworkRecords.status_iff_parse_empty
