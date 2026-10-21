module
public import proofs.JointThermoComplexity.Complexity.PowerVectorUnit
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Structural unary fuel drives exact retained binary-reference catalyst-power cells. -/

namespace JointThermoComplexity.Complexity.PowerVectorLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

structure Layout (w : ℕ) where
  cell : PowerVectorControl.Layout w
  fuel : Fin (w + 1)
  fuel_idx : fuel ≠ cell.idx
  fuel_ref : ∀ p ∈ cell.comparisons, fuel ≠ p.constant
  fuel_flag : ∀ p ∈ cell.comparisons, fuel ≠ p.flag

def Stable (d : Layout w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ d.cell.idx → (∀ p ∈ d.cell.comparisons, j ≠ p.flag) → j ≠ d.fuel →
    next j = work j) → R work → R next

def Inv (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (start i : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  PowerVectorUnit.Pre d.cell values (start + i) before input (emitted ++ PowerVectorControl.words d.cell weights values start i) R

theorem reframe (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (start i : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (work next : Fin (w + 1) → Tape)
    (he : ∀ j, j ≠ d.fuel → next j = work j) (hs : Parked (next d.fuel))
    (hR : ∀ old new, (∀ j, j ≠ d.fuel → new j = old j) → R old → R new) :
    ∀ inp out, Inv d weights values start i before input emitted R inp work out →
      Inv d weights values start i before input emitted R inp next out := by
  rintro inp out ⟨hc, hsafe, hi, hr, hx⟩
  have hsafe' : ∀ j, Parked (next j) := by
    intro j
    by_cases hj : j = d.fuel
    · subst j; exact hs
    · rw [he j hj]; exact hsafe j
  refine ⟨⟨hc.cells, hc.head, fun j => ⟨(hsafe' j).read_ne_start, (hsafe' j).1⟩, hc.tapePrefix, hc.zero⟩,
    hsafe', ?_, ?_, hR work next he hx⟩
  · rw [he d.cell.idx d.fuel_idx.symm]; exact hi
  · intro p hp
    rw [he p.constant (d.fuel_ref p hp).symm, he p.flag (d.fuel_flag p hp).symm]
    exact hr p hp

def machine (d : Layout w) (weights : Ports w → ℕ) : TM (w + 1) :=
  forRegTM (PowerVectorUnit.machine d.cell weights) d.fuel

def timeBound (V T B : ℕ) : ℕ := V * (PowerVectorUnit.bound T B + 2) + (V + 2)

theorem frame_body_hoareTime (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (start V T B i : ℕ) (hi : i < V) (hT : start + V ≤ T)
    (hbits : ∀ p ∈ d.cell.comparisons, (values p.constant).bits.length ≤ B)
    (hcount : d.cell.comparisons.length ≤ 4)
    (hweight : PowerCellWord.weight (PowerCellEmit.items d.cell.comparisons weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (PowerVectorUnit.machine d.cell weights).HoareTime
      (InvariantLoop.Frame d.fuel V (i + 2) (Inv d weights values start i before input emitted R))
      (InvariantLoop.Frame d.fuel V (i + 2) (Inv d weights values start (i + 1) before input emitted R))
      (PowerVectorUnit.bound T B) := by
  let ft : Tape := ⟨i + 2, regCells V⟩
  let RB : (Fin (w + 1) → Tape) → Prop := fun work => R work ∧ work d.fuel = ft
  have hRB : PowerVectorUnit.Stable d.cell RB := by
    rintro work next he ⟨hr, hf⟩
    exact ⟨hR work next (fun j hidx hflags _ => he j hidx hflags) hr,
      (he d.fuel d.fuel_idx d.fuel_flag).trans hf⟩
  have hRf : ∀ work next, (∀ j, j ≠ d.fuel → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ _ hj => he j hj)
  have hb := PowerVectorUnit.hoareTime d.cell weights values (start + i) T B (by omega) hbits hcount hweight before input
    (emitted ++ PowerVectorControl.words d.cell weights values start i) RB hRB
  intro inp work out hf
  have hactual : Inv d weights values start i before input emitted R inp work out := by
    apply reframe d weights values start i before input emitted R (InvariantLoop.restore work d.fuel V) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      hRf inp out hf.invariant
  have hpre : PowerVectorUnit.Pre d.cell values (start + i) before input
      (emitted ++ PowerVectorControl.words d.cell weights values start i) RB inp work out := by
    obtain ⟨hc, hs, hi, hr, hx⟩ := hactual
    exact ⟨hc, hs, hi, hr, hx, hf.fuel⟩
  obtain ⟨c, t, ht, hd, hhalt, hc, hs, hidx, hr, hx⟩ := hb inp work out hpre
  have hbase : Inv d weights values start (i + 1) before input emitted R c.input c.work c.output := by
    exact ⟨by simpa only [PowerVectorControl.words_succ, List.append_assoc] using hc, hs, hidx, hr, hx.1⟩
  have hrestored : Inv d weights values start (i + 1) before input emitted R
      c.input (InvariantLoop.restore c.work d.fuel V) c.output := by
    apply reframe d weights values start (i + 1) before input emitted R c.work (InvariantLoop.restore c.work d.fuel V)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape V) hRf c.input c.output hbase
  exact ⟨c, t, ht, hd, hhalt, hx.2, hc.input_read, fun j _ => (hs j).read_ne_start, hc.output_read, hrestored⟩

theorem framed_hoareTime (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (start V T B : ℕ) (hT : start + V ≤ T)
    (hbits : ∀ p ∈ d.cell.comparisons, (values p.constant).bits.length ≤ B)
    (hcount : d.cell.comparisons.length ≤ 4)
    (hweight : PowerCellWord.weight (PowerCellEmit.items d.cell.comparisons weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d weights).HoareTime
      (InvariantLoop.Frame d.fuel V 1 (Inv d weights values start 0 before input emitted R))
      (InvariantLoop.Frame d.fuel V 1 (Inv d weights values start V before input emitted R)) (timeBound V T B) := by
  exact InvariantLoop.hoareTime _ d.fuel (fun i => Inv d weights values start i before input emitted R)
    (PowerVectorUnit.bound T B) V
    (fun i hi => frame_body_hoareTime d weights values start V T B i hi hT hbits hcount hweight before input emitted R hR)

theorem hoareTime (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (start V T B : ℕ) (hT : start + V ≤ T)
    (hbits : ∀ p ∈ d.cell.comparisons, (values p.constant).bits.length ≤ B)
    (hcount : d.cell.comparisons.length ≤ 4)
    (hweight : PowerCellWord.weight (PowerCellEmit.items d.cell.comparisons weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d weights).HoareTime
      (fun inp work out => Inv d weights values start 0 before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (fun inp work out => Inv d weights values start V before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (timeBound V T B) := by
  have hb := framed_hoareTime d weights values start V T B hT hbits hcount hweight before input emitted R hR
  apply hb.consequence
  · rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work d.fuel V hf.eq_regT] using hi
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem polynomial_timeBound (V T B : ℕ) : timeBound V T B = V * (98 * T + 96 * B + 114) + 2 := by
  unfold timeBound PowerVectorUnit.bound
  ring1

end JointThermoComplexity.Complexity.PowerVectorLoop

#print axioms JointThermoComplexity.Complexity.PowerVectorLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.PowerVectorLoop.polynomial_timeBound
