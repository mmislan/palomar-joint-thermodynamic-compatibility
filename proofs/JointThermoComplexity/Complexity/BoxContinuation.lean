module
public import proofs.JointThermoComplexity.Complexity.BoxStart
public import proofs.JointThermoComplexity.Complexity.BoxSeed
public import proofs.JointThermoComplexity.Complexity.BoxAccess

set_option autoImplicit false
@[expose] public section

/-! Connect post-positivity resources, read-only box access, cursor reset and complete allFin box output. -/

namespace JointThermoComplexity.Complexity.BoxContinuation
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxState CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (BoxAccess.machine m) (BoxStart.machine m)

def timeBound (L : ℕ) : ℕ := BoxAccess.timeBound L + BoxStart.timeBound L + 1

theorem timeBound_eq (L : ℕ) : timeBound L = 128 * L ^ 3 + 272 * L ^ 2 + 285 * L + 22 := by
  unfold timeBound BoxAccess.timeBound BoxStart.timeBound
  ring1

def word (Q : NetworkCodec.Input) : List Bool :=
  conjunctionTag ++ (BoxDenseCode.formula Q.network.boxes (NetworkMembership.activityIndex Q.network)).code

def tableBefore (Q : NetworkCodec.Input) (before : List Bool) : List Bool :=
  (before ++ FixedWordsSkip.code (BoxTraversalData.motifs Q)) ++ BoxTraversalData.forward Q

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor before (NetworkTallyData.tail Q) emitted inp work out ∧
        CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) Q.speciesCount Q.speciesCount
          (CurrentResources.State m input) work)
      (fun inp work out => Cursor (before ++ NetworkTallyData.tail Q) [] (emitted ++ word Q) inp work out ∧
        Ready m input.length Q.speciesCount (fun work => CurrentPins.Kept m input work ∧ BoxRegisters.State m input work) work)
      (timeBound input.length) := by
  let C : (Fin (m + 15) → Tape) → Prop := CurrentReady.Ready m input.length (NetworkMembership.arity Q.network)
    Q.speciesCount Q.speciesCount (CurrentResources.State m input)
  have ha := BoxAccess.hoareTime m input Q hd before emitted (fun work _ => C work)
  have hs := BoxStart.hoareTime m Q.speciesCount input Q hd (BoxDecodedBounds.species input Q hd)
    (tableBefore Q before) [] emitted (BoxRegisters.State m input) (BoxRegisters.frame m input)
  have hseq := seqTM_hoareTime (BoxAccess.machine m) (BoxStart.machine m) ha (by
    rintro inp work out ⟨hc, _, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [tableBefore, List.append_nil] using hc, BoxSeed.of_current m input Q hd work hr⟩) hs
  exact hseq.consequence (by
    rintro inp work out ⟨hc, hr⟩
    have hk : CurrentPins.Kept m input work := by
      rcases hr with ⟨_, _, _, _, _, _, hk, _⟩
      exact hk
    exact ⟨hc, hk, hr⟩) (by
      rintro inp work out ⟨hc, hr⟩
      exact ⟨by simpa only [word, tableBefore, BoxTraversalData.tail_split, List.append_assoc] using hc, hr⟩)
    (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.BoxContinuation

#print axioms JointThermoComplexity.Complexity.BoxContinuation.timeBound_eq
#print axioms JointThermoComplexity.Complexity.BoxContinuation.hoareTime
