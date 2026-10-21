module
public import proofs.JointThermoComplexity.Complexity.CurrentLoopEntry
public import proofs.JointThermoComplexity.Complexity.CurrentDenseCode
public import proofs.JointThermoComplexity.Complexity.NetworkBuild

set_option autoImplicit false
@[expose] public section

/-! A complete actual finite reaction-table rescan emits exactly the network's current-equation formula. -/

namespace JointThermoComplexity.Complexity.CurrentDenseBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady CurrentTraversal CircuitSerialization FiniteCodec

def machine (m : ℕ) : TM (m + 15) :=
  seqTM (CurrentLoop.machine m (ReactionFuel.slot m)) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := 66 * L ^ 3 + 164 * L ^ 2 + 123 * L + 6

theorem hoareTime {n r c : ℕ} (m L : ℕ) (Q : NetworkData.Network n r c)
    (ha : NetworkMembership.arity Q ≤ 4 * L) (hn : n ≤ L) (hr : r ≤ L)
    (hlen : ∀ i, ((DataCodec.reaction n).code (Q.reactions i)).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) →
      work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (functionCode (DataCodec.reaction n) Q.reactions ++ tail) emitted inp work out ∧
        Ready m L (n + r) n n R work ∧ IsReg r (work (ReactionFuel.slot m)))
      (fun inp work out => Cursor (before ++ functionCode (DataCodec.reaction n) Q.reactions) tail
        (emitted ++ (NetworkMembership.equationsFormula Q).code) inp work out ∧
        Ready m L (NetworkMembership.arity Q) (n + r) n R work ∧ IsReg r (work (ReactionFuel.slot m)))
      (timeBound L) := by
  have hfields : ∀ q ∈ List.ofFn Q.reactions, ((DataCodec.reaction n).code q).length ≤ L := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact hlen i
  have hloop := CurrentLoopEntry.hoareTime m L (n + r) n ha hn (ReactionFuel.slot m) (ReactionFuel.slot_separate m)
    (raw_ne_reactionFuel m).symm (List.ofFn Q.reactions) (CurrentDenseCode.clauses Q)
    (CurrentDenseCode.clauses_length Q) (CurrentDenseCode.current Q) (CurrentDenseCode.result Q)
    (CurrentDenseCode.current_value Q) (CurrentDenseCode.result_value Q) (CurrentDenseCode.clause_at Q)
    (by simpa only [List.length_ofFn] using hr) hfields before tail emitted R hR
  let S : (Fin (m + 15) → Tape) → Prop := fun work =>
    Ready m L (NetworkMembership.arity Q) (n + r) n R work ∧ IsReg r (work (ReactionFuel.slot m))
  have htruth := FixedOutput.hoareTime [false, false, false]
    (before ++ functionCode (DataCodec.reaction n) Q.reactions) tail
    (emitted ++ output (CurrentDenseCode.clauses Q)) S
  have hseq := seqTM_hoareTime (CurrentLoop.machine m (ReactionFuel.slot m)) (emitBitsTM [false, false, false]) hloop (by
    rintro inp work out ⟨hc, hr, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    refine ⟨?_, hr.1, ?_, ?_⟩
    · simpa only [NetworkBuild.table_code] using hc
    · simpa only [List.length_ofFn, NetworkMembership.arity, ExactGateCount.gates_eq_cost] using hr
    · simpa only [List.length_ofFn] using hf) htruth
  exact hseq.consequence (by
    intro inp work out hp
    simpa only [NetworkBuild.table_code, List.length_ofFn] using hp) (by
      rintro inp work out ⟨hc, _, hr, hf⟩
      refine ⟨?_, hr, hf⟩
      rw [← CurrentDenseCode.output_eq]
      simpa only [List.append_assoc] using hc) (by
        unfold timeBound CurrentLoopEntry.timeBound
        simp only [List.length_cons, List.length_nil]
        omega)

end JointThermoComplexity.Complexity.CurrentDenseBuild

#print axioms JointThermoComplexity.Complexity.CurrentDenseBuild.hoareTime
