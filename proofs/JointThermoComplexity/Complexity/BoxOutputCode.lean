module
public import proofs.JointThermoComplexity.Complexity.BufferOutputProgram
public import proofs.JointThermoComplexity.Complexity.NetworkFormula
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! A fixed rational-box template reuses four literal buffers and one runtime activity index. -/

namespace JointThermoComplexity.Complexity.BoxOutput
open _root_.Complexity
open BufferOutput NetworkData

variable {w : ℕ}

def word (bits : List Bool) : Instruction w := .base (.word bits)

def intTerm (idx : Fin w) : List (Instruction w) := [word [false, false, false], .raw idx]

def natTerm (idx : Fin w) : List (Instruction w) := [word [false, false, false, false], .raw idx]

def multTerm (den source : Fin w) : List (Instruction w) :=
  [word [false, true, true]] ++ natTerm den ++ [.base (.var source)]

def comparison (tag : List Bool) (left right : List (Instruction w)) : List (Instruction w) :=
  [word tag] ++ left ++ right

def lessEqual (left right : List (Instruction w)) : List (Instruction w) :=
  [word [true, false, true]] ++ comparison [false, true, true] left right ++
    comparison [false, true, false] left right

def program (loNum loDen hiNum hiDen source : Fin w) : List (Instruction w) :=
  [word [true, false, false]] ++ lessEqual (intTerm loNum) (multTerm loDen source) ++
    lessEqual (multTerm hiDen source) (intTerm hiNum)

theorem code_eq {arity : ℕ} (loNum loDen hiNum hiDen source : Fin w)
    (values : Fin w → ℕ) (buffers : Fin w → List Bool) (b : ClosedBox) (idx : Fin arity)
    (hv : values source = idx.val)
    (hln : buffers loNum = BitCodec.integerCode b.lower.numerator)
    (hld : buffers loDen = BitCodec.naturalCode b.lower.denominator)
    (hhn : buffers hiNum = BitCodec.integerCode b.upper.numerator)
    (hhd : buffers hiDen = BitCodec.naturalCode b.upper.denominator) :
    BufferOutput.code values buffers (program loNum loDen hiNum hiDen source) =
      (NetworkFormula.boxFormula (some b) idx).code := by
  simp [program, lessEqual, comparison, multTerm, natTerm, intTerm, word, BufferOutput.code,
    Instruction.code, OutputProgram.Instruction.code, hv, hln, hld, hhn, hhd,
    NetworkFormula.boxFormula, NetworkFormula.lessEqual, RealSyntax.Formula.code, RealSyntax.Term.code,
    BitCodec.integerCode, List.append_assoc]

theorem timeBound_eq (loNum loDen hiNum hiDen source : Fin w)
    (values : Fin w → ℕ) (buffers : Fin w → List Bool) :
    BufferOutput.timeBound values buffers (program loNum loDen hiNum hiDen source) =
      4 * VariableOutput.timeBound (values source) +
        4 * ((buffers loNum).length + (buffers loDen).length + (buffers hiNum).length + (buffers hiDen).length) + 132 := by
  simp only [program, lessEqual, comparison, multTerm, natTerm, intTerm, word,
    List.cons_append, List.nil_append, BufferOutput.timeBound, Instruction.timeBound,
    OutputProgram.Instruction.timeBound, List.length_cons, List.length_nil]
  ring1

end JointThermoComplexity.Complexity.BoxOutput

#print axioms JointThermoComplexity.Complexity.BoxOutput.code_eq
#print axioms JointThermoComplexity.Complexity.BoxOutput.timeBound_eq
