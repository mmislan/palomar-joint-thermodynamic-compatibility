module
public import proofs.JointThermoComplexity.Complexity.NetworkBody

set_option autoImplicit false
@[expose] public section

/-! Preserve spare-register predicates through the existing actual network parser body. -/

namespace JointThermoComplexity.Complexity.NetworkBodyFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ}

theorem hoareTime (species reactions cores master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hr : reactions ≠ NaturalMachine.flagIndex n)
    (hc : cores ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n)
    (hsm : species ≠ master) (hrm : reactions ≠ master) (hcm : cores ≠ master)
    (hsr : species ≠ reactions) (hsc : species ≠ cores) (hrc : reactions ≠ cores)
    (ns nr nc : ℕ) (header : Bool) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (NetworkBody.machine species reactions cores master).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work master).head = 1 ∧ (work (NaturalMachine.flagIndex n)).head = 1 ∧
        (work (NaturalMachine.flagIndex n)).read = Γ.ofBool header ∧ NetworkScanner.Env species reactions cores ns nr nc work ∧ R work)
      (fun inp work out =>
        Cursor (before ++ (RecordControl.network ns nr nc).taken input) ((RecordControl.network ns nr nc).rest input)
          (emitted ++ (RecordControl.network ns nr nc).taken input) inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool (header && NetworkRecords.accepted ns nr nc input) ∧
        NetworkScanner.Env species reactions cores ns nr nc work ∧ R work)
      (NetworkScanner.timeBound ns nr nc input.length + 6) := by
  let P := fun work => NetworkScanner.Env species reactions cores ns nr nc work ∧ R work
  have hP : ∀ (work work' : Fin (n + 1) → Tape), (∀ j, j ≠ master → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨⟨hss, hrr, hcc⟩, hrest⟩
    exact ⟨⟨by simpa only [hw species hsm] using hss, by simpa only [hw reactions hrm] using hrr,
      by simpa only [hw cores hcm] using hcc⟩, hR work work' (fun j hj _ => hw j hj) hrest⟩
  have hi := StartValidity.hoareTime master (NaturalMachine.flagIndex n) hm header before input emitted P hP
  have hrecords := NetworkRecords.hoareTime species reactions cores master hs hr hc hm hsm hrm hcm hsr hsc hrc
    ns nr nc header before input emitted R hR
  have hseq := seqTM_hoareTime (StartValidity.machine master (NaturalMachine.flagIndex n))
    (NetworkRecords.machine species reactions cores master) hi (by
      rintro inp work out ⟨hcur, hmh, hmr, hfh, _, he, hrest⟩
      obtain ⟨hi', hw, ho⟩ := hcur.phase
      rw [hi', hw, ho]
      exact ⟨hcur, hfh, hmh, hmr, he, hrest⟩) hrecords
  exact hseq.consequence
    (fun _ _ _ ⟨hcur, hmh, hfh, hfr, he, hrest⟩ => ⟨hcur, hmh, hfh, hfr, he, hrest⟩)
    (fun _ _ _ h => h) (by omega)

end JointThermoComplexity.Complexity.NetworkBodyFrame

#print axioms JointThermoComplexity.Complexity.NetworkBodyFrame.hoareTime
