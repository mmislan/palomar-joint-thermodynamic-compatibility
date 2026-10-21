module
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryPacket
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Exactly sixteen static units per structural input-length fuel unit. -/

namespace JointThermoComplexity.Complexity.BoundedUnaryLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt
open BoundedUnaryUnit (Ports Inv)
variable {w : ℕ}

def Stable (d : Ports w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ d.idx → j ≠ d.value → j ≠ d.flag → j ≠ d.fuel → next j = work j) → R work → R next

theorem reframe (d : Ports w) (N i : ℕ) (before input emitted word : List Bool)
    (R : (Fin w → Tape) → Prop) (work next : Fin w → Tape)
    (he : ∀ j, j ≠ d.fuel → next j = work j) (hs : Parked (next d.fuel))
    (hR : ∀ old new, (∀ j, j ≠ d.fuel → new j = old j) → R old → R new) :
    ∀ inp out, Inv d N before input emitted word R i inp work out → Inv d N before input emitted word R i inp next out := by
  rintro inp out ⟨hc, hsafe, hi, hn, hh, hr⟩
  have hsafe' : ∀ j, Parked (next j) := by
    intro j
    by_cases hj : j = d.fuel
    · subst j; exact hs
    · rw [he j hj]; exact hsafe j
  refine ⟨⟨hc.cells, hc.head, fun j => ⟨(hsafe' j).read_ne_start, (hsafe' j).1⟩, hc.tapePrefix, hc.zero⟩,
    hsafe', ?_, ?_, ?_, hR work next he hr⟩
  · rw [he d.idx d.fuel_idx.symm]; exact hi
  · rw [he d.value d.fuel_value.symm]; exact hn
  · rw [he d.flag d.fuel_flag.symm]; exact hh

def machine (d : Ports w) (word : List Bool) : TM w := forRegTM (BoundedUnaryPacket.machine d word 16) d.fuel

def bodyBound (L B : ℕ) (word : List Bool) : ℕ := BoundedUnaryPacket.bound 16 (16 * L + B) word

def timeBound (L B : ℕ) (word : List Bool) : ℕ := L * (bodyBound L B word + 2) + (L + 2)

theorem frame_body_hoareTime (d : Ports w) (word : List Bool) (N L B i : ℕ) (hi : i < L)
    (hN : N.bits.length ≤ B) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable d R) :
    (BoundedUnaryPacket.machine d word 16).HoareTime
      (InvariantLoop.Frame d.fuel L (i + 2) (Inv d N before input emitted word R (16 * i)))
      (InvariantLoop.Frame d.fuel L (i + 2) (Inv d N before input emitted word R (16 * (i + 1))))
      (bodyBound L B word) := by
  let ft : Tape := ⟨i + 2, regCells L⟩
  let RB : (Fin w → Tape) → Prop := fun work => R work ∧ work d.fuel = ft
  have hRB : BoundedUnaryUnit.Stable d RB := by
    rintro work next he ⟨hr, hf⟩
    exact ⟨hR work next (fun j hidx hval hflag _ => he j hidx hval hflag) hr,
      (he d.fuel d.fuel_idx d.fuel_value d.fuel_flag).trans hf⟩
  have hRf : ∀ work next, (∀ j, j ≠ d.fuel → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ _ _ hj => he j hj)
  have hb := BoundedUnaryPacket.hoareTime d word 16 (16 * i) N (16 * L) B (by omega) hN
    before input emitted RB hRB
  intro inp work out hf
  have hactual : Inv d N before input emitted word R (16 * i) inp work out := by
    apply reframe d N (16 * i) before input emitted word R (InvariantLoop.restore work d.fuel L) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      hRf inp out hf.invariant
  have hpre : Inv d N before input emitted word RB (16 * i) inp work out := by
    rcases hactual with ⟨hc, hs, hidx, hval, hh, hr⟩
    exact ⟨hc, hs, hidx, hval, hh, hr, hf.fuel⟩
  obtain ⟨c, t, ht, hd, hhalt, hc, hs, hidx, hval, hh, hr⟩ := hb inp work out hpre
  have hbase : Inv d N before input emitted word R (16 * i + 16) c.input c.work c.output :=
    ⟨hc, hs, hidx, hval, hh, hr.1⟩
  have hrestored : Inv d N before input emitted word R (16 * i + 16)
      c.input (InvariantLoop.restore c.work d.fuel L) c.output := by
    apply reframe d N (16 * i + 16) before input emitted word R c.work (InvariantLoop.restore c.work d.fuel L)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape L) hRf c.input c.output hbase
  refine ⟨c, t, ht, hd, hhalt, hr.2, hc.input_read, fun j _ => (hs j).read_ne_start, hc.output_read, ?_⟩
  simpa only [Nat.mul_add, Nat.mul_one] using hrestored

theorem framed_hoareTime (d : Ports w) (word : List Bool) (N L B : ℕ) (hN : N.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable d R) :
    (machine d word).HoareTime
      (InvariantLoop.Frame d.fuel L 1 (Inv d N before input emitted word R 0))
      (InvariantLoop.Frame d.fuel L 1 (Inv d N before input emitted word R (16 * L))) (timeBound L B word) := by
  exact InvariantLoop.hoareTime _ d.fuel (fun i => Inv d N before input emitted word R (16 * i))
    (bodyBound L B word) L (fun i hi => frame_body_hoareTime d word N L B i hi hN before input emitted R hR)

theorem hoareTime (d : Ports w) (word : List Bool) (N L B : ℕ) (hN : N.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable d R) :
    (machine d word).HoareTime
      (fun inp work out => Inv d N before input emitted word R 0 inp work out ∧ IsReg L (work d.fuel))
      (fun inp work out => Inv d N before input emitted word R (16 * L) inp work out ∧ IsReg L (work d.fuel))
      (timeBound L B word) := by
  have hb := framed_hoareTime d word N L B hN before input emitted R hR
  apply hb.consequence
  · rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work d.fuel L hf.eq_regT] using hi
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem polynomial_timeBound (L B : ℕ) (word : List Bool) :
    timeBound L B word = 1280 * L ^ 2 + (80 * B + 16 * word.length + 307) * L + 2 := by
  unfold timeBound bodyBound BoundedUnaryPacket.bound BoundedUnaryUnit.bound
  ring1

end JointThermoComplexity.Complexity.BoundedUnaryLoop

#print axioms JointThermoComplexity.Complexity.BoundedUnaryLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.BoundedUnaryLoop.polynomial_timeBound
