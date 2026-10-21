module
public import proofs.JointThermoComplexity.Complexity.IndicatorVectorControl
public import proofs.JointThermoComplexity.Complexity.IndicatorVectorUnit
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! A structural unary fuel register drives exact binary-index indicator cells. -/

namespace JointThermoComplexity.Complexity.IndicatorVectorLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
variable {w : ℕ}

structure Ports (w : ℕ) where
  comparison : SmallCoefficientMatch.Ports w
  fuel : Fin (w + 1)
  fuel_idx : fuel ≠ comparison.operand
  fuel_target : fuel ≠ comparison.constant
  fuel_flag : fuel ≠ comparison.flag

def Stable (d : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ d.comparison.operand → j ≠ d.comparison.constant → j ≠ d.comparison.flag →
    j ≠ d.fuel → next j = work j) → R work → R next

def Inv (d : Ports w) (k M start i : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  IndicatorVectorUnit.Pre d.comparison (start + i) M before input (emitted ++ IndicatorVectorControl.words k M start i) R

theorem reframe (d : Ports w) (k M start i : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (work next : Fin (w + 1) → Tape)
    (he : ∀ j, j ≠ d.fuel → next j = work j) (hs : Parked (next d.fuel))
    (hR : ∀ old new, (∀ j, j ≠ d.fuel → new j = old j) → R old → R new) :
    ∀ inp out, Inv d k M start i before input emitted R inp work out →
      Inv d k M start i before input emitted R inp next out := by
  rintro inp out ⟨hc, hsafe, hi, hm, hf, hr⟩
  have hsafe' : ∀ j, Parked (next j) := by
    intro j
    by_cases hj : j = d.fuel
    · subst j; exact hs
    · rw [he j hj]; exact hsafe j
  refine ⟨⟨hc.cells, hc.head, fun j => ⟨(hsafe' j).read_ne_start, (hsafe' j).1⟩, hc.tapePrefix, hc.zero⟩,
    hsafe', ?_, ?_, ?_, hR work next he hr⟩
  · rw [he d.comparison.operand d.fuel_idx.symm]; exact hi
  · rw [he d.comparison.constant d.fuel_target.symm]; exact hm
  · rw [he d.comparison.flag d.fuel_flag.symm]; exact hf

def machine (d : Ports w) (k : ℕ) : TM (w + 1) := forRegTM (IndicatorVectorUnit.machine d.comparison k) d.fuel
def timeBound (V T B k : ℕ) : ℕ := V * (IndicatorVectorUnit.bound T B k + 2) + (V + 2)

theorem frame_body_hoareTime (d : Ports w) (k M start V T B i : ℕ) (hi : i < V)
    (hT : start + V ≤ T) (hM : M.bits.length ≤ B) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (IndicatorVectorUnit.machine d.comparison k).HoareTime
      (InvariantLoop.Frame d.fuel V (i + 2) (Inv d k M start i before input emitted R))
      (InvariantLoop.Frame d.fuel V (i + 2) (Inv d k M start (i + 1) before input emitted R))
      (IndicatorVectorUnit.bound T B k) := by
  let ft : Tape := ⟨i + 2, regCells V⟩
  let RB : (Fin (w + 1) → Tape) → Prop := fun work => R work ∧ work d.fuel = ft
  have hRB : IndicatorVectorUnit.Stable d.comparison RB := by
    rintro work next he ⟨hr, hf⟩
    exact ⟨hR work next (fun j hidx htarget hflag _ => he j hidx htarget hflag) hr,
      (he d.fuel d.fuel_idx d.fuel_target d.fuel_flag).trans hf⟩
  have hRf : ∀ work next, (∀ j, j ≠ d.fuel → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ _ _ hj => he j hj)
  have hb := IndicatorVectorUnit.hoareTime d.comparison k (start + i) M T B (by omega) hM before input
    (emitted ++ IndicatorVectorControl.words k M start i) RB hRB
  intro inp work out hf
  have hactual : Inv d k M start i before input emitted R inp work out := by
    apply reframe d k M start i before input emitted R (InvariantLoop.restore work d.fuel V) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      hRf inp out hf.invariant
  have hpre : IndicatorVectorUnit.Pre d.comparison (start + i) M before input
      (emitted ++ IndicatorVectorControl.words k M start i) RB inp work out := by
    obtain ⟨hc, hs, hi, hm, hh, hr⟩ := hactual
    exact ⟨hc, hs, hi, hm, hh, hr, hf.fuel⟩
  obtain ⟨c, t, ht, hd, hhalt, hc, hs, hidx, hm, hh, hr⟩ := hb inp work out hpre
  have hbase : Inv d k M start (i + 1) before input emitted R c.input c.work c.output := by
    exact ⟨by simpa only [IndicatorVectorControl.words_succ, List.append_assoc] using hc, hs, hidx, hm, hh, hr.1⟩
  have hrestored : Inv d k M start (i + 1) before input emitted R
      c.input (InvariantLoop.restore c.work d.fuel V) c.output := by
    apply reframe d k M start (i + 1) before input emitted R c.work (InvariantLoop.restore c.work d.fuel V)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape V) hRf c.input c.output hbase
  exact ⟨c, t, ht, hd, hhalt, hr.2, hc.input_read, fun j _ => (hs j).read_ne_start, hc.output_read, hrestored⟩

theorem framed_hoareTime (d : Ports w) (k M start V T B : ℕ) (hT : start + V ≤ T) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d k).HoareTime
      (InvariantLoop.Frame d.fuel V 1 (Inv d k M start 0 before input emitted R))
      (InvariantLoop.Frame d.fuel V 1 (Inv d k M start V before input emitted R)) (timeBound V T B k) := by
  exact InvariantLoop.hoareTime _ d.fuel (fun i => Inv d k M start i before input emitted R)
    (IndicatorVectorUnit.bound T B k) V (fun i hi => frame_body_hoareTime d k M start V T B i hi hT hM before input emitted R hR)

theorem hoareTime (d : Ports w) (k M start V T B : ℕ) (hT : start + V ≤ T) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d k).HoareTime
      (fun inp work out => Inv d k M start 0 before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (fun inp work out => Inv d k M start V before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (timeBound V T B k) := by
  have hb := framed_hoareTime d k M start V T B hT hM before input emitted R hR
  apply hb.consequence
  · rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work d.fuel V hf.eq_regT] using hi
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem polynomial_timeBound (V T B k : ℕ) : timeBound V T B k =
    V * (26 * T + 24 * B + max (BitCodec.naturalCode k).length (BitCodec.naturalCode 0).length + 32) + 2 := by
  unfold timeBound IndicatorVectorUnit.bound
  ring1

end JointThermoComplexity.Complexity.IndicatorVectorLoop

#print axioms JointThermoComplexity.Complexity.IndicatorVectorLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.IndicatorVectorLoop.polynomial_timeBound
