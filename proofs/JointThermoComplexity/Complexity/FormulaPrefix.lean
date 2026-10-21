module
public import proofs.JointThermoComplexity.Complexity.FreshArity
public import proofs.JointThermoComplexity.Complexity.BinderOutput
public import proofs.JointThermoComplexity.Complexity.CircuitPrefixOutput

set_option autoImplicit false
@[expose] public section

/-! Exact initial sentence syntax: binders, outer conjunction, circuit conjunctions and truth. -/

namespace JointThermoComplexity.Complexity.FormulaPrefix
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountLayout CircuitSerialization

def word (arity gates : ℕ) : List Bool := RealSyntax.binderCode arity ++ conjunctionTag ++
  (RepeatedOutput.copies conjunctionTag gates ++ [false, false, false])

def suffix (Q : NetworkCodec.Input) : List Bool :=
  equationStream (NetworkCircuit.dense Q.network.reactions).circuit
    (NetworkMembership.activityIndex Q.network) (NetworkMembership.auxiliaryIndex Q.network) ++
  (RealSyntax.Formula.conj (NetworkMembership.equationsFormula Q.network)
    (NetworkFormula.constraintsFormula Q.network (NetworkMembership.activityIndex Q.network) (NetworkMembership.currentIndex Q.network))).code

theorem sentence_code (Q : NetworkCodec.Input) :
    (NetworkMembership.sentence Q.network).code = word (NetworkMembership.arity Q.network) (NetworkMembership.gates Q.network) ++ suffix Q := by
  simp only [NetworkMembership.sentence, RealSyntax.Sentence.code, NetworkMembership.formula,
    RealSyntax.Formula.code, network_circuit_code, word, suffix, conjunctionTag, List.append_assoc]

def machine (m : ℕ) : TM (m + 8) := seqTM (BinderOutput.machine (binder m))
  (seqTM (emitBitsTM conjunctionTag) (CircuitPrefixOutput.machine (raw m)))

theorem hoareTime (m : ℕ) (input before remaining emitted : List Bool) (R : (Fin (m + 8) → Tape) → Prop) :
    (machine m).HoareTime
      (fun inp work out => IsReg (ArityValue.arity input) (work (binder m)) ∧ IsReg (GateCountValue.count input) (work (raw m)) ∧
        Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => IsReg (ArityValue.arity input) (work (binder m)) ∧ IsReg (GateCountValue.count input) (work (raw m)) ∧
        Cursor before remaining (emitted ++ word (ArityValue.arity input) (GateCountValue.count input)) inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (34 * input.length + 15) := by
  let a := ArityValue.arity input
  let g := GateCountValue.count input
  have hbind := BinderOutput.hoareTime (binder m) a before remaining emitted
    (fun work => IsReg g (work (raw m)) ∧ R work)
  have htag := FixedOutput.hoareTime conjunctionTag before remaining (emitted ++ RealSyntax.binderCode a)
    (fun work => IsReg a (work (binder m)) ∧ IsReg g (work (raw m)) ∧ R work)
  have hcirc := CircuitPrefixOutput.hoareTime (raw m) g before remaining
    ((emitted ++ RealSyntax.binderCode a) ++ conjunctionTag) (fun work => IsReg a (work (binder m)) ∧ R work)
  have hrest := seqTM_hoareTime (emitBitsTM conjunctionTag) (CircuitPrefixOutput.machine (raw m)) htag (by
    rintro inp work out ⟨hc, hs, ha, hg, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hg, hc, hs, ha, hr⟩) hcirc
  have hfull := seqTM_hoareTime (BinderOutput.machine (binder m))
    (seqTM (emitBitsTM conjunctionTag) (CircuitPrefixOutput.machine (raw m))) hbind (by
      rintro inp work out ⟨ha, hc, hs, hg, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, ha, hg, hr⟩) hrest
  refine hfull.consequence
    (fun _ _ _ ⟨ha, hg, hc, hs, hr⟩ => ⟨ha, hc, hs, hg, hr⟩) ?_ ?_
  · rintro inp work out ⟨hg, hc, hs, ha, hr⟩
    exact ⟨ha, hg, by simpa only [word, List.append_assoc] using hc, hs, hr⟩
  · have ha := ArityValue.arity_bound input
    have hg := GateCountValue.bound input
    simp only [conjunctionTag, List.length_cons, List.length_nil]
    change (4 * a + 4) + 1 + (3 + 1 + (6 * g + 6)) ≤ _
    omega

end JointThermoComplexity.Complexity.FormulaPrefix

#print axioms JointThermoComplexity.Complexity.FormulaPrefix.sentence_code
#print axioms JointThermoComplexity.Complexity.FormulaPrefix.hoareTime
