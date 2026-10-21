module
public import proofs.JointThermoComplexity.Complexity.OutputProgram
public import proofs.JointThermoComplexity.Complexity.RawReplay

set_option autoImplicit false
@[expose] public section

/-! Static output instructions extended by literal replay from a fixed work buffer. -/

namespace JointThermoComplexity.Complexity.BufferOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

inductive Instruction (w : ℕ) where
  | base : OutputProgram.Instruction w → Instruction w
  | raw : Fin w → Instruction w
  deriving DecidableEq

def Instruction.machine (scratch : Fin w) : Instruction w → TM w
  | .base i => i.machine scratch
  | .raw idx => RawReplay.machine idx

def Instruction.code (values : Fin w → ℕ) (buffers : Fin w → List Bool) : Instruction w → List Bool
  | .base i => i.code values
  | .raw idx => buffers idx

def Instruction.timeBound (values : Fin w → ℕ) (buffers : Fin w → List Bool) : Instruction w → ℕ
  | .base i => i.timeBound values
  | .raw idx => 2 * (buffers idx).length + 5

def Instruction.Ready (values : Fin w → ℕ) (buffers : Fin w → List Bool)
    (work : Fin w → Tape) : Instruction w → Prop
  | .base i => i.Ready values work
  | .raw idx => (work idx).HasBinaryPrefix (buffers idx) ∧ (work idx).cells 0 = Γ.start

def Instruction.Valid (scratch : Fin w) : Instruction w → Prop
  | .base i => i.Valid scratch
  | .raw _ => True

theorem Instruction.run (scratch : Fin w) (instruction : Instruction w)
    (values : Fin w → ℕ) (buffers : Fin w → List Bool)
    (before input emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j))
    (hb : Register 0 (work scratch)) (hv : instruction.Valid scratch) (hr : instruction.Ready values buffers work) :
    ∃ d t, t ≤ instruction.timeBound values buffers ∧
      (instruction.machine scratch).reachesIn t ⟨(instruction.machine scratch).qstart, inp, work, out⟩ d ∧
      (instruction.machine scratch).halted d ∧
      Cursor before input (emitted ++ instruction.code values buffers) d.input d.work d.output ∧ d.work = work := by
  cases instruction with
  | base i => exact OutputProgram.Instruction.run scratch i values before input emitted inp work out hc hs hb hv hr
  | raw idx =>
    obtain ⟨d, t, ht, hreach, hhalt, hdcur, _, _, hdwork⟩ :=
      RawReplay.hoareTime idx (buffers idx) before input emitted (fun work' => work' = work)
        inp work out ⟨hc, hr.1, hr.2, rfl⟩
    exact ⟨d, t, ht, hreach, hhalt, hdcur, hdwork⟩

end JointThermoComplexity.Complexity.BufferOutput

#print axioms JointThermoComplexity.Complexity.BufferOutput.Instruction.run
