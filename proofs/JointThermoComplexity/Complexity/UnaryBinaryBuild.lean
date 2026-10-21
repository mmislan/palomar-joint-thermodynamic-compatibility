module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun
public import proofs.JointThermoComplexity.Complexity.LoopCursor

set_option autoImplicit false
@[expose] public section

/-!
# Convert a bounded unary index into canonical binary work data

Only a dimension, position or gate-count register fuels this loop. Input numeric
payloads such as exponents and rational factors are not expanded into unary.
The source count is restored; the destination starts as an empty binary register.
-/

namespace JointThermoComplexity.Complexity.UnaryBinaryBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

def StateInv (dst : Fin w) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (i : ℕ) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input emitted inp work out ∧ Register i (work dst) ∧ R work

theorem body_hoareTime (fuel dst : Fin w) (hne : fuel ≠ dst) (v i : ℕ) (hi : i < v)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel → j ≠ dst → work' j = work j) → R work → R work') :
    (BinaryIncrementMachine.machine dst).HoareTime
      (InvariantLoop.Frame fuel v (i + 2) (StateInv dst before input emitted R i))
      (InvariantLoop.Frame fuel v (i + 2) (StateInv dst before input emitted R (i + 1))) (2 * v + 4) := by
  intro inp work out hf
  rcases hf.invariant with ⟨hc, hreg, hstate⟩
  have hphysical : Cursor before input emitted inp work out := by
    apply LoopCursor.physical fuel v hc
    rw [hf.fuel]
    refine ⟨?_, ?_⟩
    · change regCells v (i + 2) ≠ Γ.start
      exact regCells_ne_start (by omega)
    · change 1 ≤ i + 2
      omega
  have hdst : InvariantLoop.restore work fuel v dst = work dst := by
    rw [InvariantLoop.restore, Function.update_of_ne hne.symm]
  have hreg' : Register i (work dst) := by simpa only [hdst] using hreg
  obtain ⟨d, t, ht, hreach, hhalt, hinp, hout, hother, hdreg⟩ :=
    BinaryIncrementRun.run_nat dst i ⟨.carry, inp, work, out⟩ rfl hreg' hphysical.input_read hphysical.output_read
      (by rw [hphysical.tapePrefix.1]; omega) (fun j _ => hphysical.works j)
  have hfuel : d.work fuel = ⟨i + 2, regCells v⟩ := (hother fuel hne).trans hf.fuel
  have hcursor : Cursor before input emitted d.input d.work d.output := by
    refine ⟨by simpa only [hinp] using hphysical.cells, by simpa only [hinp] using hphysical.head, ?_,
      by simpa only [hout] using hphysical.tapePrefix, by simpa only [hout] using hphysical.zero⟩
    intro j
    by_cases hj : j = dst
    · subst j
      exact ⟨hdreg.read_ne_start, by rw [hdreg.1.1]⟩
    · rw [hother j hj]
      exact hphysical.works j
  have hdf : InvariantLoop.restore d.work fuel v dst = d.work dst := by
    rw [InvariantLoop.restore, Function.update_of_ne hne.symm]
  have hframe : ∀ j, j ≠ fuel → j ≠ dst →
      InvariantLoop.restore d.work fuel v j = InvariantLoop.restore work fuel v j := by
    intro j hjf hjd
    rw [InvariantLoop.restore, Function.update_of_ne hjf, InvariantLoop.restore, Function.update_of_ne hjf]
    exact hother j hjd
  have hbits := BinaryIncrementControl.bits_length_le i
  refine ⟨d, t, by omega, hreach, hhalt, hfuel, hcursor.input_read,
    fun j _ => (hcursor.works j).1, hcursor.output_read, ?_⟩
  exact ⟨LoopCursor.restore hcursor fuel v, by simpa only [hdf] using hdreg,
    hR (InvariantLoop.restore work fuel v) (InvariantLoop.restore d.work fuel v) hframe hstate⟩

def machine (fuel dst : Fin w) : TM w := forRegTM (BinaryIncrementMachine.machine dst) fuel

theorem hoareTime (fuel dst : Fin w) (hne : fuel ≠ dst) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel → j ≠ dst → work' j = work j) → R work → R work') :
    (machine fuel dst).HoareTime
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input emitted inp work out ∧ Register 0 (work dst) ∧ R work)
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input emitted inp work out ∧ Register v (work dst) ∧ R work)
      (v * (2 * v + 6) + (v + 2)) := by
  rintro inp work out ⟨hreg, hc, hd, hr⟩
  have hpre : InvariantLoop.Frame fuel v 1 (StateInv dst before input emitted R 0) inp work out := by
    refine ⟨hreg.eq_regT, hc.input_read, fun j _ => (hc.works j).1, hc.output_read, ?_⟩
    rw [InvariantLoop.restore_self work fuel v hreg.eq_regT]
    exact ⟨hc, hd, hr⟩
  have hbody : ∀ i, i < v → (BinaryIncrementMachine.machine dst).HoareTime
      (InvariantLoop.Frame fuel v (i + 2) (StateInv dst before input emitted R i))
      (InvariantLoop.Frame fuel v (i + 2) (StateInv dst before input emitted R (i + 1))) (2 * v + 4) :=
    fun i hi => body_hoareTime fuel dst hne v i hi before input emitted R hR
  obtain ⟨d, t, ht, hreach, hhalt, hf⟩ := InvariantLoop.hoareTime (BinaryIncrementMachine.machine dst) fuel
    (StateInv dst before input emitted R) (2 * v + 4) v hbody inp work out hpre
  exact ⟨d, t, ht, hreach, hhalt, hf.register, hf.on_work⟩

end JointThermoComplexity.Complexity.UnaryBinaryBuild

#print axioms JointThermoComplexity.Complexity.UnaryBinaryBuild.hoareTime
