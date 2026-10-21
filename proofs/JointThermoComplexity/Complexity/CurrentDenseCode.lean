module
public import proofs.JointThermoComplexity.Complexity.CurrentRecord
public import proofs.JointThermoComplexity.Complexity.CurrentTraversal
public import proofs.JointThermoComplexity.Complexity.NetworkOutputAddress

set_option autoImplicit false
@[expose] public section

/-! The counted current clauses use exactly the dense network's actual current and retained output addresses. -/

namespace JointThermoComplexity.Complexity.CurrentDenseCode
open CircuitSerialization CurrentTraversal

variable {n r c : ℕ}

def ofIndex (qs : Fin r → ReactionCircuit.Reaction n) (i : Fin (List.ofFn qs).length) : Fin r :=
  ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

def current (Q : NetworkData.Network n r c) (i : Fin (List.ofFn Q.reactions).length) : Fin (NetworkMembership.arity Q) :=
  NetworkMembership.currentIndex Q (ofIndex Q.reactions i)

def result (Q : NetworkData.Network n r c) (i : Fin (List.ofFn Q.reactions).length) : Fin (NetworkMembership.arity Q) :=
  NetworkMembership.auxiliaryIndex Q (NetworkCircuit.output Q.reactions (ofIndex Q.reactions i))

def clauses (Q : NetworkData.Network n r c) : List (List Bool) := List.ofFn (fun i : Fin r =>
  CurrentRecord.word (Q.reactions i) (NetworkMembership.currentIndex Q i)
    (NetworkMembership.auxiliaryIndex Q (NetworkCircuit.output Q.reactions i)))

theorem clauses_length (Q : NetworkData.Network n r c) : (clauses Q).length = (List.ofFn Q.reactions).length := by
  simp only [clauses, List.length_ofFn]

theorem current_value (Q : NetworkData.Network n r c) (i : Fin (List.ofFn Q.reactions).length) :
    (current Q i).val = n + i.val := rfl

theorem result_value (Q : NetworkData.Network n r c) (i : Fin (List.ofFn Q.reactions).length) :
    (result Q i).val + 1 = accum (n + r) (List.ofFn Q.reactions) i.val +
      ExactGateCount.reactionCost (List.ofFn Q.reactions)[i.val] := by
  have ho := NetworkOutputAddress.dense_output Q.reactions (ofIndex Q.reactions i)
  have ht := ReactionArrayData.take_cost_succ (List.ofFn Q.reactions) i.val i.isLt
  have hp : 0 < ExactGateCount.networkCost ((List.ofFn Q.reactions).take (i.val + 1)) := by
    rw [ht]
    unfold ExactGateCount.reactionCost
    omega
  change (n + r) + (NetworkCircuit.output Q.reactions (ofIndex Q.reactions i)).val + 1 = _
  rw [ho]
  change (n + r) + (ExactGateCount.networkCost ((List.ofFn Q.reactions).take (i.val + 1)) - 1) + 1 = _
  unfold accum
  omega

theorem clause_at (Q : NetworkData.Network n r c) (i : Fin (List.ofFn Q.reactions).length) :
    (clauses Q)[i.val]'(by rw [clauses_length]; exact i.isLt) =
      CurrentRecord.word (List.ofFn Q.reactions)[i.val] (current Q i) (result Q i) := by
  simp only [clauses, List.getElem_ofFn, current, result, ofIndex]

theorem conjoin_code {arity : ℕ} (ps : List (RealSyntax.Formula arity)) :
    (NetworkFormula.conjoin ps).code = output (ps.map (fun p => conjunctionTag ++ p.code)) ++ [false, false, false] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [NetworkFormula.conjoin, RealSyntax.Formula.code, ih, output, List.map_cons,
      List.flatMap_cons, id_eq, conjunctionTag, List.append_assoc]

theorem output_eq (Q : NetworkData.Network n r c) :
    output (clauses Q) ++ [false, false, false] = (NetworkMembership.equationsFormula Q).code := by
  have ht := conjoin_code (List.ofFn (fun i : Fin r => CurrentEquationOutput.equation (Q.reactions i).denominator
    (NetworkMembership.currentIndex Q i) (NetworkMembership.auxiliaryIndex Q (NetworkCircuit.output Q.reactions i))))
  simpa only [NetworkMembership.equationsFormula, NetworkFormula.allFin, clauses, CurrentRecord.word,
    CurrentEquationOutput.equation, List.map_ofFn, Function.comp_def] using ht.symm

end JointThermoComplexity.Complexity.CurrentDenseCode

#print axioms JointThermoComplexity.Complexity.CurrentDenseCode.result_value
#print axioms JointThermoComplexity.Complexity.CurrentDenseCode.output_eq
