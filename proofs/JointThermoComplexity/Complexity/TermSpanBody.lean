module
public import proofs.JointThermoComplexity.Complexity.TermSpanTagRead

set_option autoImplicit false
@[expose] public section

/-! Saved-tag branches skip fields and update only the pending count; they emit no syntax bits. -/

namespace JointThermoComplexity.Complexity.TermSpanBody
open _root_.Complexity _root_.Complexity.TM TermSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

def after (bits : List Bool) (v nodes : ℕ) (before input : List Bool) : TermSpanControl.State :=
  ⟨before ++ SourceTermToken.branchTaken bits input, SourceTermToken.branchRest bits input,
    v + SourceTermToken.children (SourceTermToken.classify bits), nodes⟩

def branchMachine (n : ℕ) (bits : List Bool) : TM (n + 7) := match SourceTermToken.classify bits with
  | .integer => seqTM IntegerSkipRaw.machine (SourcePendingUpdate.branchMachine (pending n) bits)
  | .variable => seqTM NaturalSkip.machine (SourcePendingUpdate.branchMachine (pending n) bits)
  | _ => SourcePendingUpdate.branchMachine (pending n) bits

def machine (n : ℕ) : TM (n + 7) := SourceTagDispatch.machine (List.ofFn (tags n)) (branchMachine n)

theorem branch_hoareTime (bits : List Bool) (L v nodes : ℕ) (before input emitted : List Bool)
    (hlen : input.length ≤ L) (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (branchMachine n bits).HoareTime (Inv emitted R ⟨before, input, v + 1, nodes⟩)
      (Inv emitted R (after bits v nodes before input)) (L + 2 * v + 16) := by
  cases hk : SourceTermToken.classify bits with
  | integer =>
    have hf := integer_hoareTime emitted R (⟨before, input, v + 1, nodes⟩ : TermSpanControl.State)
    have hc := TermSpanCounter.branch_hoareTime bits v nodes (before ++ IntegerMachineRun.copied input)
      (NumericCursor.integerRest input) emitted R hR
    have h := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ hf hc
    simpa only [branchMachine, after, SourceTermToken.branchTaken, SourceTermToken.branchRest, hk] using
      h.mono_bound (by omega : input.length + 3 + 1 + (2 * v + 12) ≤ L + 2 * v + 16)
  | «variable» =>
    have hf := natural_hoareTime emitted R (⟨before, input, v + 1, nodes⟩ : TermSpanControl.State)
    have hc := TermSpanCounter.branch_hoareTime bits v nodes (before ++ PayloadControl.copied .empty input)
      (NumericCursor.naturalRest input) emitted R hR
    have h := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ hf hc
    simpa only [branchMachine, after, SourceTermToken.branchTaken, SourceTermToken.branchRest, hk] using
      h.mono_bound (by omega : input.length + 1 + 1 + (2 * v + 12) ≤ L + 2 * v + 16)
  | add | mul | neg | invalid =>
    have h := TermSpanCounter.branch_hoareTime bits v nodes before input emitted R hR
    simpa only [branchMachine, after, SourceTermToken.branchTaken, SourceTermToken.branchRest, hk, List.append_nil] using
      h.mono_bound (by omega : 2 * v + 12 ≤ L + 2 * v + 16)

theorem hoareTime (bits : List Bool) (hbits : bits.length = 3) (L v nodes : ℕ) (before input emitted : List Bool)
    (hlen : input.length ≤ L) (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (machine n).HoareTime
      (fun inp work out => Inv emitted R ⟨before, input, v + 1, nodes⟩ inp work out ∧
        SourceTagDispatch.Reads (List.ofFn (tags n)) bits work)
      (Inv emitted R (after bits v nodes before input)) (L + 2 * v + 22) := by
  have h := SourceTagDispatch.hoareTime (List.ofFn (tags n)) bits (by simpa only [List.length_ofFn] using hbits)
    (branchMachine n) before input emitted (after bits v nodes before input).before (after bits v nodes before input).input emitted
    (Ready (v + 1) nodes R) (Ready (after bits v nodes before input).pending nodes R) (L + 2 * v + 16)
    (branch_hoareTime bits L v nodes before input emitted hlen R hR)
  exact h.consequence (by rintro inp work out ⟨⟨hc, hr⟩, hreads⟩; exact ⟨hc, hr, hreads⟩)
    (fun _ _ _ h => h) (by simp only [List.length_ofFn]; omega)

end JointThermoComplexity.Complexity.TermSpanBody

#print axioms JointThermoComplexity.Complexity.TermSpanBody.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.TermSpanBody.hoareTime
