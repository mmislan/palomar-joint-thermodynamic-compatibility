module
public import proofs.JointThermoComplexity.Complexity.SourcePendingUpdate
public import proofs.JointThermoComplexity.Complexity.SourceTermQueueComplete

set_option autoImplicit false
@[expose] public section

/-! The actual token interface drives the independent pending-term parser.
These control equations do not assert a composed loop runtime. -/

namespace JointThermoComplexity.Complexity.SourceTermControl
open RealSyntax SourceTermToken

def scan (arity : ℕ) : ℕ → ℕ → List Bool → Option (List Bool)
  | _, 0, input => some input
  | 0, _ + 1, _ => none
  | fuel + 1, pending + 1, input =>
      if accepted arity input then scan arity fuel (pending + children (classify (tagBits input))) (rest input)
      else none

theorem scan_eq (arity fuel pending : ℕ) (input : List Bool) :
    scan arity fuel pending input = SourceTermScan.scan arity fuel pending input := by
  induction fuel generalizing pending input with
  | zero => cases pending <;> rfl
  | succ fuel ih =>
    cases pending with
    | zero => rfl
    | succ pending =>
      cases hp : SourceTermScan.parseHead arity input with
      | none =>
        have ha : accepted arity input ≠ true := by
          intro h
          obtain ⟨head, suffix, he⟩ := (accepted_iff arity input).mp h
          rw [hp] at he
          contradiction
        simp [scan, SourceTermScan.scan, hp, ha]
      | some pair =>
        obtain ⟨head, suffix⟩ := pair
        have ha : accepted arity input = true := (accepted_iff arity input).mpr ⟨head, suffix, hp⟩
        have hr : rest input = suffix := by rw [SourceTermScan.parseHead_sound hp, rest_code]
        have hc : children (classify (tagBits input)) = head.children := by
          rw [SourceTermScan.parseHead_sound hp, children_code]
        simp [scan, SourceTermScan.scan, hp, ha, hr, hc, ih]

theorem scan_some_iff (arity fuel pending : ℕ) (input suffix : List Bool) :
    scan arity fuel pending input = some suffix ↔
      ∃ ts : List (Term arity), ts.length = pending ∧ SourceTermScan.forestNodes ts ≤ fuel ∧
        input = SourceTermScan.forestCode ts ++ suffix := by
  rw [scan_eq]
  exact SourceTermScan.scan_some_iff fuel pending input suffix

theorem scan_forest_input_length {arity : ℕ} (ts : List (Term arity)) (suffix : List Bool) :
    scan arity (SourceTermScan.forestCode ts ++ suffix).length ts.length
      (SourceTermScan.forestCode ts ++ suffix) = some suffix := by
  rw [scan_eq]
  exact SourceTermScan.scan_forest_input_length ts suffix

inductive Steps (arity : ℕ) : ℕ → ℕ → List Bool → ℕ → List Bool → Prop
  | zero (pending : ℕ) (input : List Bool) : Steps arity 0 pending input pending input
  | next {count pending final : ℕ} {input suffix : List Bool} (h : accepted arity input = true)
      (tail : Steps arity count (pending + children (classify (tagBits input))) (rest input) final suffix) :
      Steps arity (count + 1) (pending + 1) input final suffix

theorem steps_bounds {arity count pending final : ℕ} {input suffix : List Bool}
    (h : Steps arity count pending input final suffix) :
    final ≤ pending + count ∧ suffix.length + 3 * count ≤ input.length := by
  induction h with
  | zero pending input => simp
  | @next count pending final input suffix h ht ih =>
    have hchild := SourcePendingUpdate.children_bound (tagBits input)
    have hlen := success_consumes arity input h
    obtain ⟨hp, hi⟩ := ih
    constructor <;> omega

end JointThermoComplexity.Complexity.SourceTermControl

#print axioms JointThermoComplexity.Complexity.SourceTermControl.scan_eq
#print axioms JointThermoComplexity.Complexity.SourceTermControl.scan_some_iff
#print axioms JointThermoComplexity.Complexity.SourceTermControl.steps_bounds
