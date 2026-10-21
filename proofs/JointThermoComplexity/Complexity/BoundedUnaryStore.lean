module
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryEmit
public import proofs.JointThermoComplexity.Complexity.OutputRoute
public import proofs.JointThermoComplexity.Complexity.CountRewind

set_option autoImplicit false
@[expose] public section

/-! Store a structurally bounded binary count as a reusable unary register. -/

namespace JointThermoComplexity.Complexity.BoundedUnaryStore
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BoundedUnaryUnit (Ports)
variable {w : ℕ}

def oldWork (work : Fin (w + 1) → Tape) : Fin w → Tape := fun j => work j.castSucc

def Fields (d : Ports w) (N L : ℕ) (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop :=
  Register 0 (work d.idx) ∧ Register N (work d.value) ∧ (work d.flag).head = 1 ∧ IsReg L (work d.fuel) ∧ R work

def Pred (d : Ports w) (N L v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work (Fin.last w)) ∧
    Fields d N L R (oldWork work)

def machine (d : Ports w) : TM (w + 1) :=
  seqTM (BoundedUnaryEmit.payload d [true]).retargetOutput (rewindWorkTM (Fin.last w))

def bound (L B : ℕ) : ℕ := BoundedUnaryEmit.payloadBound L B [true] + 16 * L + 4

theorem routed_hoareTime (d : Ports w) (N L B : ℕ) (hN : N.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BoundedUnaryLoop.Stable d R) :
    (BoundedUnaryEmit.payload d [true]).retargetOutput.HoareTime (Pred d N L 0 before input emitted R)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (Fin.last w)).HasBinaryPrefix (List.replicate (min (16 * L) N) true) ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ Fields d N L R (oldWork work))
      (BoundedUnaryEmit.payloadBound L B [true]) := by
  rintro inp work out ⟨hc, hs, hz, hi, hn, hh, hf, hr⟩
  have hvirtual : Cursor before input [] inp (oldWork work) (work (Fin.last w)) :=
    ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, CountTape.empty_prefix_of_zero hz, hz.cell0⟩
  have hh' := BoundedUnaryEmit.payload_hoareTime d [true] N L B hN before input [] R hR
  have hroute := OutputRoute.hoareTime (BoundedUnaryEmit.payload d [true]) _ _ _ (fun t => t = out) hh'
  obtain ⟨c, t, ht, hreach, hhalt, _, hout, hcur, hsafe, hidx, hval, hflag, hfuel, hframe⟩ :=
    hroute inp work out ⟨hc.output_read, rfl, hvirtual, fun j => hs j.castSucc, hi, hn, hh, hf, hr⟩
  simp only [List.nil_append, RepeatedOutput.copies_singleton] at hcur
  have hpark : ∀ j, Parked (c.work j) := by
    intro j
    by_cases hj : j.val < w
    · let k : Fin w := ⟨j.val, hj⟩
      have he : k.castSucc = j := Fin.ext rfl
      simpa only [he] using hsafe k
    · have he : j = Fin.last w := by apply Fin.ext; simp only [Fin.val_last]; omega
      subst j
      exact ⟨by rw [hcur.tapePrefix.1]; omega,
        (show (c.work (Fin.last w)).HasBinaryContent (List.replicate (min (16 * L) N) true) from hcur.tapePrefix.2).cells_ne_start⟩
  have hmain : Cursor before input emitted c.input c.work c.output :=
    ⟨hcur.cells, hcur.head, fun j => ⟨(hpark j).read_ne_start, (hpark j).1⟩,
      by rw [hout]; exact hc.tapePrefix, by rw [hout]; exact hc.zero⟩
  exact ⟨c, t, ht, hreach, hhalt, hmain, hpark, hcur.tapePrefix, hcur.zero, hidx, hval, hflag, hfuel, hframe⟩

theorem hoareTime (d : Ports w) (N L B : ℕ) (hN : N.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BoundedUnaryLoop.Stable d R) :
    (machine d).HoareTime (Pred d N L 0 before input emitted R)
      (Pred d N L (min (16 * L) N) before input emitted R) (bound L B) := by
  let F : (Fin (w + 1) → Tape) → Prop := fun work => Fields d N L R (oldWork work)
  have hF : ∀ work next, (∀ j, j ≠ Fin.last w → next j = work j) → F work → F next := by
    intro work next he hf
    have hold : oldWork next = oldWork work := funext (fun j => he j.castSucc (Fin.castSucc_ne_last j))
    simpa only [F, hold] using hf
  have hr := CountRewind.hoareTime (Fin.last w) (min (16 * L) N) before input emitted F hF
  have he := routed_hoareTime d N L B hN before input emitted R hR
  have hall := seqTM_hoareTime _ _ he (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hr
  apply hall.consequence
  · exact fun _ _ _ hp => hp
  · rintro inp work out ⟨hv, hc, hs, hf⟩
    exact ⟨hc, hs, hv, hf⟩
  · have hm := Nat.min_le_left (16 * L) N
    unfold bound
    omega

theorem polynomial_bound (L B : ℕ) : bound L B = 1280 * L ^ 2 + (80 * B + 387) * L + 16 := by
  have hb := BoundedUnaryEmit.polynomial_bound L B
  unfold BoundedUnaryEmit.bound at hb
  unfold bound
  have he : (80 * B + 387) * L = (80 * B + 371) * L + 16 * L := by ring1
  rw [he]
  omega

end JointThermoComplexity.Complexity.BoundedUnaryStore

#print axioms JointThermoComplexity.Complexity.BoundedUnaryStore.hoareTime
#print axioms JointThermoComplexity.Complexity.BoundedUnaryStore.polynomial_bound
