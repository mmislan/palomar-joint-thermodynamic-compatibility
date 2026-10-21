module
public import proofs.JointThermoComplexity.Complexity.SourceTermTokenRun
public import proofs.JointThermoComplexity.Complexity.UnaryPredecessor
public import proofs.JointThermoComplexity.Complexity.UnarySuccessor

set_option autoImplicit false
@[expose] public section

/-! Actual pending-child updates use only the small tag arity, never a literal's numeric value. -/

namespace JointThermoComplexity.Complexity.SourcePendingUpdate
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceTermToken
variable {w : ℕ}

def branchMachine (idx : Fin w) (bits : List Bool) : TM w := match classify bits with
  | .add | .mul => UnarySuccessor.machine idx
  | .neg => emitBitsTM []
  | _ => UnaryPredecessor.machine idx

def machine (ports : Fin 3 → Fin w) (idx : Fin w) : TM w :=
  SourceTagDispatch.machine (List.ofFn ports) (branchMachine idx)

theorem branch_hoareTime (idx : Fin w) (bits : List Bool) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (branchMachine idx bits).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (v + 1) (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (v + children (classify bits)) (work idx) ∧ R work) (2 * v + 12) := by
  cases hk : classify bits with
  | integer =>
    simpa only [branchMachine, children, hk, Nat.add_zero] using UnaryPredecessor.hoareTime idx v before input emitted R hR
  | «variable» =>
    simpa only [branchMachine, children, hk, Nat.add_zero] using UnaryPredecessor.hoareTime idx v before input emitted R hR
  | add =>
    have h := UnarySuccessor.hoareTime idx (v + 1) before input emitted R hR
    simpa only [branchMachine, children, hk, Nat.add_assoc] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 2 * (v + 1) + 6 ≤ 2 * v + 12)
  | mul =>
    have h := UnarySuccessor.hoareTime idx (v + 1) before input emitted R hR
    simpa only [branchMachine, children, hk, Nat.add_assoc] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 2 * (v + 1) + 6 ≤ 2 * v + 12)
  | neg =>
    have h := FixedOutput.hoareTime [] before input emitted (fun work => IsReg (v + 1) (work idx) ∧ R work)
    simpa only [branchMachine, children, hk, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega : 0 ≤ 2 * v + 12)
  | invalid =>
    simpa only [branchMachine, children, hk, Nat.add_zero] using UnaryPredecessor.hoareTime idx v before input emitted R hR

theorem hoareTime (ports : Fin 3 → Fin w) (idx : Fin w) (bits : List Bool) (hbits : bits.length = 3)
    (v : ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine ports idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        ((∀ j, Parked (work j)) ∧ IsReg (v + 1) (work idx) ∧ R work) ∧
        SourceTagDispatch.Reads (List.ofFn ports) bits work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (v + children (classify bits)) (work idx) ∧ R work) (2 * v + 18) := by
  have h := SourceTagDispatch.hoareTime (List.ofFn ports) bits (by simpa only [List.length_ofFn] using hbits)
    (branchMachine idx) before input emitted before input emitted
    (fun work => (∀ j, Parked (work j)) ∧ IsReg (v + 1) (work idx) ∧ R work)
    (fun work => (∀ j, Parked (work j)) ∧ IsReg (v + children (classify bits)) (work idx) ∧ R work)
    (2 * v + 12) (branch_hoareTime idx bits v before input emitted R hR)
  exact h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by simp only [List.length_ofFn]; omega)

theorem children_bound (bits : List Bool) : children (classify bits) ≤ 2 := by
  cases classify bits <;> simp [children]

theorem pending_next_bound (v : ℕ) (bits : List Bool) : v + children (classify bits) ≤ (v + 1) + 1 := by
  have h := children_bound bits
  omega

end JointThermoComplexity.Complexity.SourcePendingUpdate

#print axioms JointThermoComplexity.Complexity.SourcePendingUpdate.hoareTime
