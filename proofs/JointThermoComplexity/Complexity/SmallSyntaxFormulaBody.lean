module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxTermBody

set_option autoImplicit false
@[expose] public section

/-! Actual formula tags either introduce two pending terms or leave formula mode unchanged. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxFormulaBody
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters SmallSyntaxTermBody
open HeaderAt (Cursor)

def comparisonMachine (bits : List Bool) : TM 6 := seqTM (SourceTermCountReset.machine pending) (emitBitsTM bits)
def machine (bits : List Bool) : TM 6 := match SourceFormulaScan.classify bits with
  | .eq | .lt => comparisonMachine bits
  | .invalid => emitBitsTM []
  | _ => emitBitsTM bits

theorem comparison_hoareTime (bits : List Bool) (hbits : bits.length = 3) (before input emitted : List Bool)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (comparisonMachine bits).HoareTime (Inv R ⟨before, input, emitted, 0⟩)
      (Inv R ⟨before, input, emitted ++ bits, 2⟩) 25 := by
  have hc := SmallSyntaxCounter.reset_two_hoareTime 0 before input emitted R hR
  have he := emit_hoareTime bits R ⟨before, input, emitted, 2⟩
  have h := seq_inv_hoareTime _ _ R _ _ _ _ _ hc he
  exact h.mono_bound (by omega)

theorem hoareTime (bits : List Bool) (hbits : bits.length = 3) (before input emitted : List Bool)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (machine bits).HoareTime (Inv R ⟨before, input, emitted, 0⟩)
      (Inv R (after ⟨before, input, emitted, 0⟩ (SmallSyntaxToken.formulaBody bits input))) 25 := by
  cases hk : SourceFormulaScan.classify bits with
  | eq | lt =>
    simpa only [machine, after, SmallSyntaxToken.formulaBody, hk, List.append_nil] using
      comparison_hoareTime bits hbits before input emitted R hR
  | truth | falsity | conj | disj =>
    have h := emit_hoareTime bits R ⟨before, input, emitted, 0⟩
    simpa only [machine, after, SmallSyntaxToken.formulaBody, hk, List.append_nil] using
      h.mono_bound (by omega : bits.length ≤ 25)
  | invalid =>
    have h := emit_hoareTime [] R ⟨before, input, emitted, 0⟩
    simpa only [machine, after, SmallSyntaxToken.formulaBody, hk, List.append_nil] using
      h.mono_bound (by omega : 0 ≤ 25)

end JointThermoComplexity.Complexity.SmallSyntaxFormulaBody

#print axioms JointThermoComplexity.Complexity.SmallSyntaxFormulaBody.hoareTime
