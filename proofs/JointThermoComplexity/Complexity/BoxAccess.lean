module
public import proofs.JointThermoComplexity.Complexity.BoxTraversal
public import proofs.JointThermoComplexity.Complexity.CurrentPins
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Use the retained validated dimensions to reach the box array in quadratic time. -/

namespace JointThermoComplexity.Complexity.BoxAccess
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxTraversalData

def coreSlot (m : ℕ) : Fin (m + 15) := RoutedNetworkParser.count (m + 9) 2

def machine (m : ℕ) : TM (m + 15) :=
  BoxTraversal.machine (CountLayout.offset (m + 7)) (coreSlot m) (ReactionFuel.slot m)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 2 + 9 * L + 5

theorem runtime_bound (n r c L : ℕ) (hnr : n + r ≤ L) (hc : c ≤ L) :
    BoxTraversal.timeBound n r c ≤ timeBound L := by
  have hr : r ≤ L := by omega
  unfold BoxTraversal.timeBound FixedWordsSkip.timeBound
  calc
    c * (4 * (n + r) + 4) + (c + 2) + 4 * r + 3 ≤
        L * (4 * L + 4) + (L + 2) + 4 * L + 3 := by
      have hm := Nat.mul_le_mul hc (show 4 * (n + r) + 4 ≤ 4 * L + 4 by omega)
      omega
    _ = _ := by unfold timeBound; ring1

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input)
    (hd : NetworkCodec.decode input = some Q) (before emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Tape → Prop) :
    (machine m).HoareTime
      (fun inp work out => Cursor before (NetworkTallyData.tail Q) emitted inp work out ∧
        CurrentPins.Kept m input work ∧ R work out)
      (fun inp work out => Cursor ((before ++ FixedWordsSkip.code (motifs Q)) ++ forward Q) (boxes Q) emitted inp work out ∧
        CurrentPins.Kept m input work ∧ R work out) (timeBound input.length) := by
  have hne : CountLayout.offset (m + 7) ≠ coreSlot m := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = m + 9 + 1 + 2 at hv
    omega
  have hdim := DecodedDimensions.decode_counts hd
  have hoff : ArityValue.offset input = Q.speciesCount + Q.reactionCount := by
    simp only [ArityValue.offset, hdim.1, hdim.2.1]
  have hsum := DimensionHeaders.count_sum_bound input
  rw [hdim.1, hdim.2.1, hdim.2.2] at hsum
  have hs := BoxTraversal.hoareTime (CountLayout.offset (m + 7)) (coreSlot m) (ReactionFuel.slot m) hne Q
    before emitted (fun work out => CurrentPins.Kept m input work ∧ R work out)
  exact hs.consequence (by
    rintro inp work out ⟨hc, hk, hr⟩
    have hcounts := ParserRegisters.decoded_counts (m + 9) input (CountAppend.oldWork work) hk.2.2 hd
    exact ⟨hc, hcounts.2.2, by simpa only [hoff] using hk.1, hcounts.2.1, hk, hr⟩) (by
      rintro inp work out ⟨hc, _, _, _, hk, hr⟩
      exact ⟨hc, hk, hr⟩) (runtime_bound _ _ _ _ (by omega) (by omega))

theorem run (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input)
    (hd : NetworkCodec.decode input = some Q) (before emitted : List Bool)
    (inp : Tape) (work : Fin (m + 15) → Tape) (out : Tape)
    (hc : Cursor before (NetworkTallyData.tail Q) emitted inp work out) (hk : CurrentPins.Kept m input work) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ⟨(machine m).qstart, inp, work, out⟩ d ∧
      (machine m).halted d ∧
      Cursor ((before ++ FixedWordsSkip.code (motifs Q)) ++ forward Q) (boxes Q) emitted d.input d.work d.output ∧
      d.work = work ∧ d.output = out := by
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, _, hdwork, hdout⟩ :=
    hoareTime m input Q hd before emitted (fun work' out' => work' = work ∧ out' = out)
      inp work out ⟨hc, hk, rfl, rfl⟩
  exact ⟨d, t, ht, hreach, hhalt, hdcur, hdwork, hdout⟩

end JointThermoComplexity.Complexity.BoxAccess

#print axioms JointThermoComplexity.Complexity.BoxAccess.runtime_bound
#print axioms JointThermoComplexity.Complexity.BoxAccess.hoareTime
#print axioms JointThermoComplexity.Complexity.BoxAccess.run
