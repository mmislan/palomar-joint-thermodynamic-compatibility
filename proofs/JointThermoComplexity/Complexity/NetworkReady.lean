module
public import proofs.JointThermoComplexity.Complexity.RoutedNetworkParser
public import proofs.JointThermoComplexity.Complexity.InputRewind
public import proofs.JointThermoComplexity.Complexity.NetworkRuntime

set_option autoImplicit false
@[expose] public section

/-!
# Prepare formula generation from fresh input

Canonical parsing keeps its master validity bit and dimension registers. Its
copied prefix goes to a work tape. The input is then rewound and the real output
is blank, ready for a validity-dependent formula generator.
-/

namespace JointThermoComplexity.Complexity.NetworkReady
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (n : ℕ) : TM (n + 6) := seqTM (RoutedNetworkParser.machine n) rewindInputTM

def timeBound (L : ℕ) : ℕ := NetworkParser.timeBound L + L + 4

theorem timeBound_eq (L : ℕ) : timeBound L = 2 * L ^ 3 + 28 * L ^ 2 + 66 * L + 44 := by
  rw [timeBound, NetworkRuntime.timeBound_eq]
  ring1

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine n).reachesIn t ((machine n).initCfg input) d ∧
      (machine n).halted d ∧ Cursor [] input [] d.input d.work d.output ∧
      RoutedNetworkParser.Retained n input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hret⟩ := RoutedNetworkParser.run n input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdret⟩ :=
    InputRewind.hoareTime (NetworkInputControl.copied input) (NetworkInputControl.rest input) []
      (RoutedNetworkParser.Retained n input) c.input c.work c.output ⟨hc, hret⟩
  obtain ⟨hi, hw, ho⟩ := hc.phase
  have hr : (rewindInputTM (n := n + 6)).reachesIn td
      ⟨(rewindInputTM (n := n + 6)).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (RoutedNetworkParser.machine n) rewindInputTM hcreach hchalt hr
  have hs : phase1Wrap (RoutedNetworkParser.machine n) rewindInputTM
      ((RoutedNetworkParser.machine n).initCfg input) = (machine n).initCfg input := rfl
  rw [hs] at hreach
  have hlen := congrArg List.length (NetworkInputControl.consumed_split input)
  simp only [List.length_append] at hlen
  refine ⟨phase2Wrap (RoutedNetworkParser.machine n) rewindInputTM d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, ?_, hdret⟩
  simpa only [phase2Wrap, NetworkInputControl.consumed_split] using hdcur

end JointThermoComplexity.Complexity.NetworkReady

#print axioms JointThermoComplexity.Complexity.NetworkReady.run
