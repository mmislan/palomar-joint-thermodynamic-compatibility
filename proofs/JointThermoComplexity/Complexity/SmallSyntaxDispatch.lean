module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxFormulaBody

set_option autoImplicit false
@[expose] public section

/-! Saved tags select finite branches after the pending register selects term or formula mode. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxDispatch
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters SmallSyntaxTermBody
open HeaderAt (Cursor)

def termMachine : TM 6 := SourceTagDispatch.machine (List.ofFn tags) SmallSyntaxTermBody.machine
def formulaMachine : TM 6 := SourceTagDispatch.machine (List.ofFn tags) SmallSyntaxFormulaBody.machine
def machine : TM 6 := FlagBranch.machine pending termMachine formulaMachine

theorem term_hoareTime (bits : List Bool) (hbits : bits.length = 3) (L v : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L) (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    termMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready (v + 1) R work ∧
        SourceTagDispatch.Reads (List.ofFn tags) bits work)
      (Inv R (after ⟨before, input, emitted, v + 1⟩ (SmallSyntaxToken.termBody v bits input))) (12 * L + 2 * v + 32) := by
  let s := after ⟨before, input, emitted, v + 1⟩ (SmallSyntaxToken.termBody v bits input)
  have hb := SmallSyntaxTermBody.hoareTime bits hbits L v before input emitted hlen R hR
  have h := SourceTagDispatch.hoareTime (List.ofFn tags) bits (by simpa only [List.length_ofFn] using hbits)
    SmallSyntaxTermBody.machine before input emitted s.before s.input s.emitted (Ready (v + 1) R) (Ready s.pending R)
    (12 * L + 2 * v + 26) hb
  exact h.mono_bound (by simp only [List.length_ofFn]; omega)

theorem formula_hoareTime (bits : List Bool) (hbits : bits.length = 3) (before input emitted : List Bool)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready 0 R work ∧
        SourceTagDispatch.Reads (List.ofFn tags) bits work)
      (Inv R (after ⟨before, input, emitted, 0⟩ (SmallSyntaxToken.formulaBody bits input))) 31 := by
  let s := after ⟨before, input, emitted, 0⟩ (SmallSyntaxToken.formulaBody bits input)
  have hb := SmallSyntaxFormulaBody.hoareTime bits hbits before input emitted R hR
  have h := SourceTagDispatch.hoareTime (List.ofFn tags) bits (by simpa only [List.length_ofFn] using hbits)
    SmallSyntaxFormulaBody.machine before input emitted s.before s.input s.emitted (Ready 0 R) (Ready s.pending R) 25 hb
  exact h.mono_bound (by simp only [List.length_ofFn]; omega)

theorem hoareTime (bits : List Bool) (hbits : bits.length = 3) (L count : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L) (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready count R work ∧
        SourceTagDispatch.Reads (List.ofFn tags) bits work)
      (Inv R (after ⟨before, input, emitted, count⟩ (SmallSyntaxToken.body count bits input))) (12 * L + 2 * count + 34) := by
  cases count with
  | zero =>
    let s := after ⟨before, input, emitted, 0⟩ (SmallSyntaxToken.formulaBody bits input)
    have hb := FlagBranchNonone.hoareTime pending termMachine formulaMachine before input emitted s.before s.input s.emitted
      (fun work => Ready 0 R work ∧ SourceTagDispatch.Reads (List.ofFn tags) bits work) (Ready s.pending R) 31
      (formula_hoareTime bits hbits before input emitted R hR)
    exact hb.consequence (by
      rintro inp work out h
      refine ⟨h, ?_⟩
      have hv := h.2.1.counter.read_eq
      change (work pending).read = Γ.blank at hv
      rw [hv]
      decide) (fun _ _ _ h => h) (by omega)
  | succ v =>
    let s := after ⟨before, input, emitted, v + 1⟩ (SmallSyntaxToken.termBody v bits input)
    have hb := FlagBranchRun.yes_hoareTime pending termMachine formulaMachine before input emitted s.before s.input s.emitted
      (fun work => Ready (v + 1) R work ∧ SourceTagDispatch.Reads (List.ofFn tags) bits work) (Ready s.pending R)
      (12 * L + 2 * v + 32) (term_hoareTime bits hbits L v before input emitted hlen R hR)
    exact hb.consequence (by
      rintro inp work out h
      refine ⟨h, ?_⟩
      have hv := h.2.1.counter.read_eq
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv)
      (fun _ _ _ h => h) (by omega)

end JointThermoComplexity.Complexity.SmallSyntaxDispatch

#print axioms JointThermoComplexity.Complexity.SmallSyntaxDispatch.hoareTime
