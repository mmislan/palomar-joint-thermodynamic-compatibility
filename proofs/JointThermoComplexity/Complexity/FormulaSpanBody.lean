module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanCounter

set_option autoImplicit false
@[expose] public section

/-! Finite formula-tag branches allocate exact coordinates and update the two pending registers. -/

namespace JointThermoComplexity.Complexity.FormulaSpanBody
open _root_.Complexity _root_.Complexity.TM FormulaSpanRegisters FormulaSpanCounter
open HeaderAt (Cursor)
variable {n : ℕ}

def after (bits : List Bool) (v coordinates : ℕ) (before input : List Bool) : FormulaSpanControl.State :=
  ⟨before, input, FormulaSpanControl.termCount bits, v + (SourceFormulaScan.classify bits).children,
    coordinates + FormulaSpanControl.allocation bits⟩

def simpleMachine (n : ℕ) (up : Bool) : TM (n + 8) := seqTM (formulaMachine n up) (incrementMachine n)
def atomicMachine (n : ℕ) : TM (n + 8) := seqTM (SourceTermCountReset.machine (TermSpanRegisters.pending (n + 1)))
  (seqTM (formulaMachine n false) (fourMachine n))
def branchMachine (n : ℕ) (bits : List Bool) : TM (n + 8) := match SourceFormulaScan.classify bits with
  | .eq | .lt => atomicMachine n
  | .conj | .disj => simpleMachine n true
  | _ => simpleMachine n false
def machine (n : ℕ) : TM (n + 8) := SourceTagDispatch.machine (List.ofFn (TermSpanRegisters.tags (n + 1))) (branchMachine n)

theorem simple_hoareTime (up : Bool) (v coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (simpleMachine n up).HoareTime (Inv emitted R ⟨before, input, 0, v + 1, coordinates⟩)
      (Inv emitted R ⟨before, input, 0, nextFormula up v, coordinates + 1⟩) (2 * v + 2 * coordinates + 19) := by
  have hf := formula_hoareTime up v 0 coordinates before input emitted R hR
  have hc := increment_hoareTime emitted R hR ⟨before, input, 0, nextFormula up v, coordinates⟩
  have h := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ hf hc
  exact h.mono_bound (by
    change 2 * v + 12 + 1 + (2 * coordinates + 6) ≤ 2 * v + 2 * coordinates + 19
    omega)

theorem atomic_hoareTime (v coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (atomicMachine n).HoareTime (Inv emitted R ⟨before, input, 0, v + 1, coordinates⟩)
      (Inv emitted R ⟨before, input, 2, v, coordinates + 4⟩) (2 * v + 8 * coordinates + 74) := by
  have ht := pending_two_hoareTime (v + 1) coordinates before input emitted R hR
  have hf := formula_hoareTime false v 2 coordinates before input emitted R hR
  have hc := four_hoareTime emitted R hR ⟨before, input, 2, v, coordinates⟩
  have hfc := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ hf hc
  have h := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ ht hfc
  exact h.mono_bound (by
    change 21 + 1 + (2 * v + 12 + 1 + (8 * coordinates + 39)) ≤ 2 * v + 8 * coordinates + 74
    omega)

theorem branch_hoareTime (bits : List Bool) (v coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (branchMachine n bits).HoareTime (Inv emitted R ⟨before, input, 0, v + 1, coordinates⟩)
      (Inv emitted R (after bits v coordinates before input)) (2 * v + 8 * coordinates + 74) := by
  cases hk : SourceFormulaScan.classify bits with
  | eq | lt =>
    simpa only [branchMachine, after, FormulaSpanControl.termCount, FormulaSpanControl.allocation,
      hk, SourceFormulaScan.Kind.children, Nat.add_zero] using atomic_hoareTime v coordinates before input emitted R hR
  | conj | disj =>
    have h := simple_hoareTime true v coordinates before input emitted R hR
    simpa only [branchMachine, after, FormulaSpanControl.termCount, FormulaSpanControl.allocation,
      hk, SourceFormulaScan.Kind.children, nextFormula, ↓reduceIte] using
      h.mono_bound (by omega : 2 * v + 2 * coordinates + 19 ≤ 2 * v + 8 * coordinates + 74)
  | truth | falsity | invalid =>
    have h := simple_hoareTime false v coordinates before input emitted R hR
    simpa only [branchMachine, after, FormulaSpanControl.termCount, FormulaSpanControl.allocation,
      hk, SourceFormulaScan.Kind.children, nextFormula, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
      h.mono_bound (by omega : 2 * v + 2 * coordinates + 19 ≤ 2 * v + 8 * coordinates + 74)

theorem hoareTime (bits : List Bool) (hbits : bits.length = 3) (v coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (machine n).HoareTime
      (fun inp work out => Inv emitted R ⟨before, input, 0, v + 1, coordinates⟩ inp work out ∧
        SourceTagDispatch.Reads (List.ofFn (TermSpanRegisters.tags (n + 1))) bits work)
      (Inv emitted R (after bits v coordinates before input)) (2 * v + 8 * coordinates + 80) := by
  let next := after bits v coordinates before input
  have h := SourceTagDispatch.hoareTime (List.ofFn (TermSpanRegisters.tags (n + 1))) bits
    (by simpa only [List.length_ofFn] using hbits) (branchMachine n)
    before input emitted before input emitted
    (TermSpanRegisters.Ready 0 coordinates (Frame (v + 1) R))
    (TermSpanRegisters.Ready next.terms next.coordinates (Frame next.formulas R)) (2 * v + 8 * coordinates + 74)
    (branch_hoareTime bits v coordinates before input emitted R hR)
  exact h.consequence (by rintro inp work out ⟨⟨hc, hr⟩, ht⟩; exact ⟨hc, hr, ht⟩)
    (fun _ _ _ h => h) (by simp only [List.length_ofFn]; omega)

end JointThermoComplexity.Complexity.FormulaSpanBody

#print axioms JointThermoComplexity.Complexity.FormulaSpanBody.atomic_hoareTime
#print axioms JointThermoComplexity.Complexity.FormulaSpanBody.hoareTime
