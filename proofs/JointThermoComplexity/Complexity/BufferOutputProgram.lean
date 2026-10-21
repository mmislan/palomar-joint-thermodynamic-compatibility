module
public import proofs.JointThermoComplexity.Complexity.BufferOutputInstruction

set_option autoImplicit false
@[expose] public section

/-! Compose static syntax, runtime variable indices and reusable literal buffers. -/

namespace JointThermoComplexity.Complexity.BufferOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

def machine (scratch : Fin w) : List (Instruction w) → TM w
  | [] => emitBitsTM []
  | instruction :: rest => seqTM (instruction.machine scratch) (machine scratch rest)

def code (values : Fin w → ℕ) (buffers : Fin w → List Bool) : List (Instruction w) → List Bool
  | [] => []
  | instruction :: rest => instruction.code values buffers ++ code values buffers rest

def timeBound (values : Fin w → ℕ) (buffers : Fin w → List Bool) : List (Instruction w) → ℕ
  | [] => 0
  | instruction :: rest => instruction.timeBound values buffers + 1 + timeBound values buffers rest

def Ready (program : List (Instruction w)) (values : Fin w → ℕ) (buffers : Fin w → List Bool)
    (work : Fin w → Tape) : Prop := ∀ i, i ∈ program → i.Ready values buffers work

def Valid (program : List (Instruction w)) (scratch : Fin w) : Prop :=
  ∀ i, i ∈ program → i.Valid scratch

theorem run (scratch : Fin w) (program : List (Instruction w))
    (values : Fin w → ℕ) (buffers : Fin w → List Bool)
    (before input emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j))
    (hb : Register 0 (work scratch)) (hv : Valid program scratch) (hr : Ready program values buffers work) :
    ∃ d t, t ≤ timeBound values buffers program ∧
      (machine scratch program).reachesIn t ⟨(machine scratch program).qstart, inp, work, out⟩ d ∧
      (machine scratch program).halted d ∧
      Cursor before input (emitted ++ code values buffers program) d.input d.work d.output ∧ d.work = work := by
  induction program generalizing emitted inp work out with
  | nil =>
    exact ⟨⟨(machine scratch []).qhalt, inp, work, out⟩, 0, le_rfl, .zero, rfl,
      by simpa only [code, List.append_nil] using hc, rfl⟩
  | cons instruction rest ih =>
    obtain ⟨c, tc, htc, hcreach, hchalt, hccur, hcwork⟩ :=
      Instruction.run scratch instruction values buffers before input emitted inp work out hc hs hb
        (hv instruction (by simp)) (hr instruction (by simp))
    have hvrest : Valid rest scratch := fun i hi => hv i (List.mem_cons_of_mem _ hi)
    have hrrest : Ready rest values buffers c.work := by
      intro i hi
      rw [hcwork]
      exact hr i (List.mem_cons_of_mem _ hi)
    obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdwork⟩ :=
      ih (emitted := emitted ++ instruction.code values buffers) (inp := c.input) (work := c.work) (out := c.output)
        hccur (by simpa only [hcwork] using hs) (by simpa only [hcwork] using hb) hvrest hrrest
    obtain ⟨hi, hw, ho⟩ := hccur.phase
    have hrr : (machine scratch rest).reachesIn td
        ⟨(machine scratch rest).qstart, transitionInput c.input,
          (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
      rw [hi, hw, ho]
      exact hdreach
    have hreach := seqTM_reachesIn_of_reachesIn (instruction.machine scratch) (machine scratch rest)
      hcreach hchalt hrr
    refine ⟨phase2Wrap (instruction.machine scratch) (machine scratch rest) d, tc + 1 + td,
      by simp only [timeBound]; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, ?_, hdwork.trans hcwork⟩
    simpa only [phase2Wrap, code, List.append_assoc] using hdcur

theorem hoareTime (scratch : Fin w) (program : List (Instruction w))
    (values : Fin w → ℕ) (buffers : Fin w → List Bool) (hv : Valid program scratch)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine scratch program).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ Ready program values buffers work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ code values buffers program) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ Ready program values buffers work ∧ R work)
      (timeBound values buffers program) := by
  rintro inp work out ⟨hc, hs, hb, hp, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdwork⟩ :=
    run scratch program values buffers before input emitted inp work out hc hs hb hv hp
  exact ⟨d, t, ht, hreach, hhalt, hdcur, by simpa only [hdwork] using hs,
    by simpa only [hdwork] using hb, by simpa only [hdwork] using hp, by simpa only [hdwork] using hr⟩

end JointThermoComplexity.Complexity.BufferOutput

#print axioms JointThermoComplexity.Complexity.BufferOutput.hoareTime
