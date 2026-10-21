module
public import proofs.JointThermoComplexity.Complexity.MonomialInput
public import proofs.JointThermoComplexity.Complexity.PowerStartCircuit

set_option autoImplicit false
@[expose] public section

/-! The species-copy machine emits exactly the input gate preceding BinaryPower.build. -/

namespace JointThermoComplexity.Complexity.MonomialInputCircuit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts RealCircuit RealSyntax CircuitSerialization PowerAddressCircuit PowerStartCircuit

variable {n k : ℕ}

def temporary (offset oldAcc oldPower : ℕ) (_c : Circuit n k) : PowerAddressState.State :=
  ⟨offset + k, oldAcc, oldPower⟩

theorem snoc_stream (offset arity : ℕ) (c : Circuit n k) (i : Fin n)
    (inputs : Fin n → Fin arity) (h : offset + (k + 1) ≤ arity) :
    equationStream (c.snoc (.input i)) inputs (index offset _ arity h) =
      equationStream c inputs (index offset k arity (by omega)) ++
        (Formula.eq (.var (⟨offset + k, by omega⟩ : Fin arity)) (.var (inputs i))).code := by
  have hi : (fun j : Fin k => index offset (k + 1) arity h j.castSucc) =
      index offset k arity (by omega) := by funext j; apply Fin.ext; rfl
  change equationStream c inputs (fun j => index offset (k + 1) arity h j.castSucc) ++
    (Formula.eq (.var (index offset (k + 1) arity h (Fin.last k))) (.var (inputs i))).code = _
  rw [hi]
  rfl

theorem hoareTime (m offset arity L oldAcc oldPower : ℕ) (ha : arity ≤ 4 * L)
    (c : Circuit n k) (i : Fin n) (inputs : Fin n → Fin arity)
    (h : offset + (k + 1) ≤ arity) (hp : oldPower ≤ 4 * L)
    (before input initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ power (m + 1) → work' j = work j) → R work → R work') :
    (MonomialInput.machine m).HoareTime
      (fun inp work out => Cursor before input
        (initial ++ equationStream c inputs (index offset k arity (by omega))) inp work out ∧
        PowerAddressFrame.Ready (m + 1) (temporary offset oldAcc oldPower c) R work ∧
        IsReg (inputs i).val (work (species m)))
      (fun inp work out => Cursor before input
        (initial ++ equationStream (c.snoc (.input i)) inputs (index offset _ arity h)) inp work out ∧
        PowerAddressFrame.Ready (m + 1)
          (beforeState offset oldAcc (c.snoc (.input i)) (Fin.last k)) R work ∧
        IsReg (inputs i).val (work (species m))) (64 * L ^ 2 + 132 * L + 69) := by
  have hn : (temporary offset oldAcc oldPower c).nextAddress < arity := by
    change offset + k < arity
    omega
  have ht := MonomialInput.hoareTime m arity L ha (temporary offset oldAcc oldPower c) hn
    (inputs i) hp before input (initial ++ equationStream c inputs (index offset k arity (by omega))) R hR
  exact ht.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hr, hi⟩
    refine ⟨?_, ?_, hi⟩
    · rw [snoc_stream offset arity c i inputs h]
      simpa only [temporary, List.append_assoc] using hc
    · simpa only [temporary, beforeState, Fin.val_last, Nat.add_assoc] using hr) le_rfl

end JointThermoComplexity.Complexity.MonomialInputCircuit

#print axioms JointThermoComplexity.Complexity.MonomialInputCircuit.hoareTime
