module
public import proofs.JointThermoComplexity.Complexity.SourceTermFields

set_option autoImplicit false
@[expose] public section

/-! Actual total field/operator branches and finite tag selection. -/

namespace JointThermoComplexity.Complexity.SourceTermBranch
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryDifferenceCursor SourceIndexField SourceTermToken
variable {n : ℕ}

theorem branch_hoareTime (bits : List Bool) (L : ℕ) (left right : Fin (n + 1))
    (sep : Separate left right (NaturalMachine.flagIndex n)) (arity : ℕ) (ha : arity.bits.length ≤ L)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (branchMachine left right bits).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work)
      (fun inp work out => Cursor (before ++ branchTaken bits input) (branchRest bits input) emitted inp work out ∧
        Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (branchStatus arity bits input)) (32 * L + 46) := by
  cases hk : classify bits with
  | integer =>
    have h := SourceTermFields.integer_hoareTime L left right sep arity before input emitted hlen R hR
    simpa only [branchMachine, branchTaken, branchRest, branchStatus, hk] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 13 * L + 13 ≤ 32 * L + 46)
  | «variable» =>
    simpa only [branchMachine, branchTaken, branchRest, branchStatus, hk] using
      SourceIndexField.hoareTime L left right sep arity ha before input emitted hlen R hR
  | add =>
    have h := SourceTermFields.constant_hoareTime true L left right sep arity before input emitted R hR
    simpa only [branchMachine, branchTaken, branchRest, branchStatus, hk, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 1 ≤ 32 * L + 46)
  | mul =>
    have h := SourceTermFields.constant_hoareTime true L left right sep arity before input emitted R hR
    simpa only [branchMachine, branchTaken, branchRest, branchStatus, hk, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 1 ≤ 32 * L + 46)
  | neg =>
    have h := SourceTermFields.constant_hoareTime true L left right sep arity before input emitted R hR
    simpa only [branchMachine, branchTaken, branchRest, branchStatus, hk, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 1 ≤ 32 * L + 46)
  | invalid =>
    have h := SourceTermFields.constant_hoareTime false L left right sep arity before input emitted R hR
    simpa only [branchMachine, branchTaken, branchRest, branchStatus, hk, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 1 ≤ 32 * L + 46)

theorem dispatch_hoareTime (ports : Fin 3 → Fin (n + 1)) (bits : List Bool) (hbits : bits.length = 3)
    (L : ℕ) (left right : Fin (n + 1)) (sep : Separate left right (NaturalMachine.flagIndex n))
    (arity : ℕ) (ha : arity.bits.length ≤ L) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (dispatchMachine ports left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        SourceTagDispatch.Reads (List.ofFn (fun i => (ports i).castSucc)) bits work)
      (fun inp work out => Cursor (before ++ branchTaken bits input) (branchRest bits input) emitted inp work out ∧
        Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (branchStatus arity bits input)) (32 * L + 52) := by
  have h := SourceTagDispatch.hoareTime (List.ofFn (fun i => (ports i).castSucc)) bits
    (by simpa only [List.length_ofFn] using hbits) (branchMachine left right)
    before input emitted (before ++ branchTaken bits input) (branchRest bits input) emitted
    (Ready L left right arity R)
    (fun work => Ready L left right arity R work ∧
      (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (branchStatus arity bits input)) (32 * L + 46)
    (branch_hoareTime bits L left right sep arity ha before input emitted hlen R hR)
  exact h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by simp only [List.length_ofFn]; omega)

end JointThermoComplexity.Complexity.SourceTermBranch

#print axioms JointThermoComplexity.Complexity.SourceTermBranch.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermBranch.dispatch_hoareTime
