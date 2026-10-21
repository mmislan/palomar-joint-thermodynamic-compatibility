module
public import proofs.JointThermoComplexity.Complexity.TallyComponents
public import proofs.JointThermoComplexity.Complexity.ReactionTallyData

set_option autoImplicit false
@[expose] public section

/-! An actual reaction-record gate tally: two exponent arrays, six fixed gates, two read-only factors. -/

namespace JointThermoComplexity.Complexity.ReactionTally
open _root_.Complexity
open _root_.Complexity.TM
open CountAppend TallySpec ReactionTallyData ExponentArrayData

variable {w n : ℕ}

def machine (species : Fin w) : TM (w + 1) := seqTM (CountOffset.machine 6)
  (seqTM (seqTM (ExponentArrayTally.machine species) (ExponentArrayTally.machine species))
    (seqTM NaturalSkip.machine NaturalSkip.machine))

def timeBound (v L : ℕ) : ℕ :=
  6 + 1 + (((v * (L + 6) + (v + 2)) + 1 + (v * (L + 6) + (v + 2))) + 1 + (L + 1 + L))

theorem runs (species : Fin w) (r : ReactionCircuit.Reaction n) :
    Runs (machine species) (fun work => IsReg n (work species)) ((DataCodec.reaction n).code r)
      (ExactGateCount.reactionCost r) (timeBound n ((DataCodec.reaction n).code r).length) := by
  let L := ((DataCodec.reaction n).code r).length
  let A := n * (L + 6) + (n + 2)
  let Env : (Fin w → Tape) → Prop := fun work => IsReg n (work species)
  obtain ⟨hra, hpa, hnu, hde⟩ := component_lengths r
  have haraw := TallyComponents.array_runs species (reactants r)
  have hbraw := TallyComponents.array_runs species (products r)
  have ha : Runs (ExponentArrayTally.machine species) Env (code (reactants r)) (cost (reactants r)) A := by
    intro count before tail emitted R
    have h := haraw count before tail emitted R
    have hbound : (reactants r).length * ((code (reactants r)).length + 6) + ((reactants r).length + 2) ≤ A := by
      rw [(array_lengths r).1]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.add_le_add_right hra 6)) (n + 2)
    simpa only [(array_lengths r).1, Env] using h.mono_bound hbound
  have hb : Runs (ExponentArrayTally.machine species) Env (code (products r)) (cost (products r)) A := by
    intro count before tail emitted R
    have h := hbraw count before tail emitted R
    have hbound : (products r).length * ((code (products r)).length + 6) + ((products r).length + 2) ≤ A := by
      rw [(array_lengths r).2]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.add_le_add_right hpa 6)) (n + 2)
    simpa only [(array_lengths r).2, Env] using h.mono_bound hbound
  have hn : Runs (NaturalSkip.machine (w := w + 1)) Env (BitCodec.naturalCode r.numerator) 0 L := by
    intro count before tail emitted R
    exact (TallyComponents.skip_runs r.numerator Env count before tail emitted R).mono_bound hnu
  have hd : Runs (NaturalSkip.machine (w := w + 1)) Env (BitCodec.naturalCode r.denominator) 0 L := by
    intro count before tail emitted R
    exact (TallyComponents.skip_runs r.denominator Env count before tail emitted R).mono_bound hde
  have hraw := seq_runs (offset_runs 6 Env) (seq_runs (seq_runs ha hb) (seq_runs hn hd))
  simpa only [machine, timeBound, A, L, Env, List.nil_append, Nat.add_zero,
    reaction_code, reaction_cost, Nat.add_assoc] using hraw

end JointThermoComplexity.Complexity.ReactionTally

#print axioms JointThermoComplexity.Complexity.ReactionTally.runs
