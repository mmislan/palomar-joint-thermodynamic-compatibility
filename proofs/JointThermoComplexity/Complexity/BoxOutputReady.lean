module
public import proofs.JointThermoComplexity.Complexity.BoxOutputCode
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Exact box output from four binary buffers, preserving all retained resources. -/

namespace JointThermoComplexity.Complexity.BoxOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun NetworkData

variable {w : ℕ}

def Ready (loNum loDen hiNum hiDen source : Fin w) (values : Fin w → ℕ)
    (buffers : Fin w → List Bool) (work : Fin w → Tape) : Prop :=
  IsReg (values source) (work source) ∧
    ∀ j ∈ [loNum, loDen, hiNum, hiDen], (work j).HasBinaryPrefix (buffers j) ∧ (work j).cells 0 = Γ.start

theorem program_valid (scratch loNum loDen hiNum hiDen source : Fin w) (hne : source ≠ scratch) :
    BufferOutput.Valid (program loNum loDen hiNum hiDen source) scratch := by
  simp [BufferOutput.Valid, program, lessEqual, comparison, multTerm, natTerm, intTerm, word,
    BufferOutput.Instruction.Valid, OutputProgram.Instruction.Valid, hne]

theorem program_ready (loNum loDen hiNum hiDen source : Fin w) (values : Fin w → ℕ)
    (buffers : Fin w → List Bool) (work : Fin w → Tape) (hr : Ready loNum loDen hiNum hiDen source values buffers work) :
    BufferOutput.Ready (program loNum loDen hiNum hiDen source) values buffers work := by
  have hln := hr.2 loNum (by simp)
  have hld := hr.2 loDen (by simp)
  have hhn := hr.2 hiNum (by simp)
  have hhd := hr.2 hiDen (by simp)
  simp [BufferOutput.Ready, program, lessEqual, comparison, multTerm, natTerm, intTerm, word,
    BufferOutput.Instruction.Ready, OutputProgram.Instruction.Ready,
    hr.1, hln.1, hln.2, hld.1, hld.2, hhn.1, hhn.2, hhd.1, hhd.2]

def machine (scratch loNum loDen hiNum hiDen source : Fin w) : TM w :=
  BufferOutput.machine scratch (program loNum loDen hiNum hiDen source)

def timeBound (L : ℕ) : ℕ := 128 * L ^ 2 + 208 * L + 204

theorem runtime_bound (L : ℕ) (loNum loDen hiNum hiDen source : Fin w)
    (values : Fin w → ℕ) (buffers : Fin w → List Bool) (hv : values source ≤ 4 * L)
    (hl : (buffers loNum).length ≤ L) (hld : (buffers loDen).length ≤ L)
    (hh : (buffers hiNum).length ≤ L) (hhd : (buffers hiDen).length ≤ L) :
    BufferOutput.timeBound values buffers (program loNum loDen hiNum hiDen source) ≤ timeBound L := by
  rw [timeBound_eq]
  have hvar := TemplateRuntime.variable_bound hv
  unfold timeBound
  omega

theorem hoareTime {arity : ℕ} (L : ℕ) (scratch loNum loDen hiNum hiDen source : Fin w)
    (hne : source ≠ scratch) (values : Fin w → ℕ) (buffers : Fin w → List Bool) (b : ClosedBox) (idx : Fin arity)
    (hv : values source = idx.val) (hindex : values source ≤ 4 * L)
    (hln : buffers loNum = BitCodec.integerCode b.lower.numerator)
    (hld : buffers loDen = BitCodec.naturalCode b.lower.denominator)
    (hhn : buffers hiNum = BitCodec.integerCode b.upper.numerator)
    (hhd : buffers hiDen = BitCodec.naturalCode b.upper.denominator)
    (hsize : ∀ j ∈ [loNum, loDen, hiNum, hiDen], (buffers j).length ≤ L)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine scratch loNum loDen hiNum hiDen source).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ Ready loNum loDen hiNum hiDen source values buffers work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (NetworkFormula.boxFormula (some b) idx).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧
        Ready loNum loDen hiNum hiDen source values buffers work ∧ R work) (timeBound L) := by
  have hcode := code_eq loNum loDen hiNum hiDen source values buffers b idx hv hln hld hhn hhd
  have hs := BufferOutput.hoareTime scratch (program loNum loDen hiNum hiDen source) values buffers
    (program_valid scratch loNum loDen hiNum hiDen source hne) before input emitted
    (fun work => Ready loNum loDen hiNum hiDen source values buffers work ∧ R work)
  exact hs.consequence (by
    rintro inp work out ⟨hc, hsafe, hz, hr, hp⟩
    exact ⟨hc, hsafe, hz, program_ready loNum loDen hiNum hiDen source values buffers work hr, hr, hp⟩) (by
      rintro inp work out ⟨hc, hsafe, hz, _, hr, hp⟩
      exact ⟨by simpa only [hcode] using hc, hsafe, hz, hr, hp⟩)
    (runtime_bound L loNum loDen hiNum hiDen source values buffers hindex
      (hsize loNum (by simp)) (hsize loDen (by simp)) (hsize hiNum (by simp)) (hsize hiDen (by simp)))

end JointThermoComplexity.Complexity.BoxOutput

#print axioms JointThermoComplexity.Complexity.BoxOutput.hoareTime
