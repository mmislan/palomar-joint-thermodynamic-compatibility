module
public import proofs.JointThermoComplexity.Complexity.NetworkRecords
public import proofs.JointThermoComplexity.Complexity.StartValidity

set_option autoImplicit false
@[expose] public section

/-! Start record validation with the checked header verdict, then check the full suffix. -/

namespace JointThermoComplexity.Complexity.NetworkBody
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ}

def machine (species reactions cores master : Fin (n + 1)) : TM (n + 1) :=
  seqTM (StartValidity.machine master (NaturalMachine.flagIndex n)) (NetworkRecords.machine species reactions cores master)

theorem hoareTime (species reactions cores master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hr : reactions ≠ NaturalMachine.flagIndex n)
    (hc : cores ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n)
    (hsm : species ≠ master) (hrm : reactions ≠ master) (hcm : cores ≠ master)
    (hsr : species ≠ reactions) (hsc : species ≠ cores) (hrc : reactions ≠ cores)
    (ns nr nc : ℕ) (header : Bool) (before input emitted : List Bool) :
    (machine species reactions cores master).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work master).head = 1 ∧ (work (NaturalMachine.flagIndex n)).head = 1 ∧
        (work (NaturalMachine.flagIndex n)).read = Γ.ofBool header ∧ NetworkScanner.Env species reactions cores ns nr nc work)
      (fun inp work out =>
        Cursor (before ++ (RecordControl.network ns nr nc).taken input) ((RecordControl.network ns nr nc).rest input)
          (emitted ++ (RecordControl.network ns nr nc).taken input) inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool (header && NetworkRecords.accepted ns nr nc input) ∧
        NetworkScanner.Env species reactions cores ns nr nc work)
      (NetworkScanner.timeBound ns nr nc input.length + 6) := by
  let Env := NetworkScanner.Env species reactions cores ns nr nc
  have hEnv : ∀ (work work' : Fin (n + 1) → Tape), (∀ j, j ≠ master → work' j = work j) → Env work → Env work' := by
    rintro work work' h ⟨hss, hrr, hcc⟩
    exact ⟨by simpa only [h species hsm] using hss, by simpa only [h reactions hrm] using hrr,
      by simpa only [h cores hcm] using hcc⟩
  have hi := StartValidity.hoareTime master (NaturalMachine.flagIndex n) hm header before input emitted Env hEnv
  have hruns := NetworkRecords.hoareTime species reactions cores master hs hr hc hm hsm hrm hcm hsr hsc hrc
    ns nr nc header before input emitted (fun _ => True) (by intros; trivial)
  have hseq := seqTM_hoareTime (StartValidity.machine master (NaturalMachine.flagIndex n))
    (NetworkRecords.machine species reactions cores master) hi (by
      rintro inp work out ⟨hcur, hmh, hmr, hfh, _, he⟩
      obtain ⟨hi', hw, ho⟩ := hcur.phase
      rw [hi', hw, ho]
      exact ⟨hcur, hfh, hmh, hmr, he, True.intro⟩) hruns
  apply HoareTime.mono_bound (b := 3 + 1 + (NetworkScanner.timeBound ns nr nc input.length + 2))
  · apply HoareTime.strengthen_post hseq
    rintro inp work out ⟨hcur, hfh, hmh, hmr, he, _⟩
    exact ⟨hcur, hfh, hmh, hmr, he⟩
  · omega

end JointThermoComplexity.Complexity.NetworkBody

#print axioms JointThermoComplexity.Complexity.NetworkBody.hoareTime
