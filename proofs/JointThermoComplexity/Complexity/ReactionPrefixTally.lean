module
public import proofs.JointThermoComplexity.Complexity.ReactionTally
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Count the entire reaction circuit while stopping immediately before its denominator field. -/

namespace JointThermoComplexity.Complexity.ReactionPrefixTally
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend TallySpec ReactionTallyData ExponentArrayData

variable {w n : ℕ}

def word (q : ReactionCircuit.Reaction n) : List Bool :=
  (code (reactants q) ++ code (products q)) ++ BitCodec.naturalCode q.numerator

theorem record_split (q : ReactionCircuit.Reaction n) :
    (DataCodec.reaction n).code q = word q ++ BitCodec.naturalCode q.denominator := by
  rw [reaction_code]
  exact List.append_assoc _ _ _ |>.symm

def machine (species : Fin w) : TM (w + 1) := seqTM (CountOffset.machine 6)
  (seqTM (seqTM (ExponentArrayTally.machine species) (ExponentArrayTally.machine species)) NaturalSkip.machine)

def timeBound (v L : ℕ) : ℕ := 6 + 1 + (((v * (L + 6) + (v + 2)) + 1 + (v * (L + 6) + (v + 2))) + 1 + L)

theorem runs (species : Fin w) (q : ReactionCircuit.Reaction n) :
    Runs (machine species) (fun work => IsReg n (work species)) (word q)
      (ExactGateCount.reactionCost q) (timeBound n ((DataCodec.reaction n).code q).length) := by
  let L := ((DataCodec.reaction n).code q).length
  let A := n * (L + 6) + (n + 2)
  let Env : (Fin w → Tape) → Prop := fun work => IsReg n (work species)
  obtain ⟨hra, hpa, hnu, _⟩ := component_lengths q
  have haraw := TallyComponents.array_runs species (reactants q)
  have hbraw := TallyComponents.array_runs species (products q)
  have ha : Runs (ExponentArrayTally.machine species) Env (code (reactants q)) (cost (reactants q)) A := by
    intro count before tail emitted R
    have ht := haraw count before tail emitted R
    have hb : (reactants q).length * ((code (reactants q)).length + 6) + ((reactants q).length + 2) ≤ A := by
      rw [(array_lengths q).1]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.add_le_add_right hra 6)) (n + 2)
    simpa only [(array_lengths q).1, Env] using ht.mono_bound hb
  have hb : Runs (ExponentArrayTally.machine species) Env (code (products q)) (cost (products q)) A := by
    intro count before tail emitted R
    have ht := hbraw count before tail emitted R
    have hbound : (products q).length * ((code (products q)).length + 6) + ((products q).length + 2) ≤ A := by
      rw [(array_lengths q).2]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.add_le_add_right hpa 6)) (n + 2)
    simpa only [(array_lengths q).2, Env] using ht.mono_bound hbound
  have hn : Runs (NaturalSkip.machine (w := w + 1)) Env (BitCodec.naturalCode q.numerator) 0 L := by
    intro count before tail emitted R
    exact (TallyComponents.skip_runs q.numerator Env count before tail emitted R).mono_bound hnu
  have hraw := seq_runs (offset_runs 6 Env) (seq_runs (seq_runs ha hb) hn)
  simpa only [machine, timeBound, A, L, Env, word, List.nil_append, Nat.add_zero,
    reaction_cost, Nat.add_assoc] using hraw

theorem decoded_bound (L n v : ℕ) (hn : n ≤ L) (hv : v ≤ L) : timeBound n v ≤ 2 * L ^ 2 + 15 * L + 13 := by
  have hm := Nat.mul_le_mul hn (Nat.add_le_add_right hv 7)
  calc
    timeBound n v = 2 * (n * (v + 7)) + v + 13 := by unfold timeBound; ring1
    _ ≤ 2 * (L * (L + 7)) + L + 13 :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 hm) hv) 13
    _ = _ := by ring1

end JointThermoComplexity.Complexity.ReactionPrefixTally

#print axioms JointThermoComplexity.Complexity.ReactionPrefixTally.runs
#print axioms JointThermoComplexity.Complexity.ReactionPrefixTally.decoded_bound
