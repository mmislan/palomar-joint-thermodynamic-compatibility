module
public import proofs.JointThermoComplexity.Complexity.BinaryAddBuffer
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset
public import proofs.JointThermoComplexity.Complexity.CountSumAt

set_option autoImplicit false
@[expose] public section

/-! Copy a canonical sum from final scratch to an empty old register, then
clear scratch. The permutation changes physical routing, not tape contents. -/

namespace JointThermoComplexity.Complexity.BinaryScratchRestore
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def copyMachine (idx : Fin w) : TM (w + 1) :=
  WorkPermutation.machine (Equiv.swap idx.castSucc (Fin.last w)) (BinaryScaleBuffer.machine 1 idx)

def machine (idx : Fin w) : TM (w + 1) := seqTM (copyMachine idx) (BinaryBufferReset.machine (Fin.last w))

theorem copy_hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ idx → next j = work j) → R work → R next) :
    (copyMachine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx.castSucc).HasBinaryPrefix [] ∧ (work idx.castSucc).cells 0 = Γ.start ∧
        Register v (work (Fin.last w)) ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ Register v (work (Fin.last w)) ∧ R (oldWork work))
      (3 * v.bits.length + 12) := by
  rintro inp work out ⟨hc, hs, hp, hz, hv, hx⟩
  let e := Equiv.swap idx.castSucc (Fin.last w)
  let original : Fin w → Tape := fun j => work (e j.castSucc)
  have hb := BinaryScaleBuffer.natural_hoareTime 1 idx v before input emitted (fun old => old = original)
  have hr := WorkPermutation.hoareTime e (BinaryScaleBuffer.machine 1 idx) _ _ _ hb
  have hcur : Cursor before input emitted inp (fun j => work (e j)) out :=
    ⟨hc.cells, hc.head, fun j => hc.works (e j), hc.tapePrefix, hc.zero⟩
  obtain ⟨d, t, ht, hd, hh, hdc, hds, hdsrc, hddst, hdold⟩ := hr inp work out
    ⟨hcur, (fun j => hs (e j)), by simpa only [e, Equiv.swap_apply_left] using hv,
      by simpa only [e, Equiv.swap_apply_right] using hp,
      by simpa only [e, Equiv.swap_apply_right] using hz, rfl⟩
  have hother : ∀ j, j ≠ idx.castSucc → d.work j = work j := by
    intro j hj
    have hjd : j ≠ CountSumAt.destination e := by simpa only [CountSumAt.destination, e, Equiv.swap_apply_right] using hj
    obtain ⟨k, hk⟩ := CountSumAt.preimage e j hjd
    have he := congrArg (fun f : Fin w → Tape => f k) hdold
    change d.work (e k.castSucc) = work (e k.castSucc) at he
    simpa only [hk] using he
  have hsafe : ∀ j, Parked (d.work j) := fun j => by
    simpa only [e.apply_symm_apply] using hds (e.symm j)
  have hdc' : Cursor before input emitted d.input d.work d.output :=
    ⟨hdc.cells, hdc.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩, hdc.tapePrefix, hdc.zero⟩
  have hx' : R (oldWork d.work) := hR (oldWork work) (oldWork d.work) (by
    intro j hj
    apply hother j.castSucc
    intro he
    apply hj
    apply Fin.ext
    exact congrArg (fun x : Fin (w + 1) => x.val) he) hx
  exact ⟨d, t, by omega, hd, hh, hdc', hsafe,
    by simpa only [e, Equiv.swap_apply_right, Nat.one_mul] using hddst,
    by simpa only [e, Equiv.swap_apply_left] using hdsrc, hx'⟩

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ idx → next j = work j) → R work → R next) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx.castSucc).HasBinaryPrefix [] ∧ (work idx.castSucc).cells 0 = Γ.start ∧
        Register v (work (Fin.last w)) ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (6 * v.bits.length + 22) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register v (work idx.castSucc) ∧ R (oldWork work)
  have hS : ∀ work next, (∀ j, j ≠ Fin.last w → next j = work j) → S work → S next := by
    rintro work next he ⟨hv, hx⟩
    have hold : oldWork next = oldWork work := funext (fun j => he j.castSucc (cast_ne_last j))
    exact ⟨by rw [he idx.castSucc (cast_ne_last idx)]; exact hv, by rw [hold]; exact hx⟩
  have hc := copy_hoareTime idx v before input emitted R hR
  have hr := BinaryBufferReset.hoareTime (Fin.last w) v.bits before input emitted S hS
  have hf := seqTM_hoareTime _ _ hc (by
    rintro inp work out ⟨hc, hs, hd, hv, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hv.1.2, hv.2, by rw [hv.1.1]; omega, hd, hx⟩) hr
  apply hf.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hs, hz, hv, hx⟩
    exact ⟨hc, hs, hv, CountTape.empty_prefix_of_zero hz, hz.cell0, hx⟩
  · omega

end JointThermoComplexity.Complexity.BinaryScratchRestore

#print axioms JointThermoComplexity.Complexity.BinaryScratchRestore.copyMachine
#print axioms JointThermoComplexity.Complexity.BinaryScratchRestore.copy_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryScratchRestore.hoareTime
