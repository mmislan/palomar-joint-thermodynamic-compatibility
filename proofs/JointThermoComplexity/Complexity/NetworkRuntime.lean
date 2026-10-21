module
public import proofs.JointThermoComplexity.Complexity.NetworkParser
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! A closed cubic bound for the concrete fresh-input network parser. -/

namespace JointThermoComplexity.Complexity.NetworkRuntime
open _root_.Complexity
open _root_.Complexity.TM

theorem timeBound_eq (L : ℕ) : NetworkParser.timeBound L = 2 * L ^ 3 + 28 * L ^ 2 + 65 * L + 40 := by
  unfold NetworkParser.timeBound
  ring1

theorem computesInTime (n : ℕ) : (NetworkParser.machine n).ComputesInTime NetworkInputControl.copied
    (fun L => 2 * L ^ 3 + 28 * L ^ 2 + 65 * L + 40) := by
  intro input
  obtain ⟨d, t, ht, hreach, hhalt, hout⟩ := NetworkParser.computesInTime n input
  exact ⟨d, t, by simpa only [timeBound_eq] using ht, hreach, hhalt, hout⟩

end JointThermoComplexity.Complexity.NetworkRuntime

#print axioms JointThermoComplexity.Complexity.NetworkRuntime.computesInTime
