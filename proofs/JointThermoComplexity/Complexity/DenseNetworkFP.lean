module
public import proofs.JointThermoComplexity.Complexity.DenseTimeBounds
public import proofs.Complexitylib.Classes.P.Defs
public import proofs.Complexitylib.Asymptotics

set_option autoImplicit false
@[expose] public section

/-! Unconditional binary-Turing-machine FP for the complete actual raw word
emitter. Canonical network identity is proved separately from running time. -/

namespace JointThermoComplexity.Complexity.DenseNetworkFP
open _root_.Complexity _root_.Complexity.TM HeaderAt

theorem computesInTime (boxed : Bool) :
    (DenseNetworkEmitter.machine boxed).ComputesInTime (DenseNetworkEmitter.word boxed) (DenseTimeBounds.lengthBound boxed) := by
  intro input
  have h := (DenseNetworkEmitter.hoareTime boxed input).mono_bound (DenseTimeBounds.emitter_le boxed input)
  obtain ⟨d, t, ht, hr, hh, hp⟩ := h (Tape.init (input.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    ⟨rfl, fun _ => rfl, rfl⟩
  change (DenseNetworkEmitter.machine boxed).reachesIn t ((DenseNetworkEmitter.machine boxed).initCfg input) d at hr
  have hc := hp.1.1
  exact ⟨d, t, ht, hr, hh, hc.tapePrefix.2.1, hc.tapePrefix.2.2 _ le_rfl⟩

theorem word_mem_FP (boxed : Bool) : DenseNetworkEmitter.word boxed ∈ _root_.Complexity.FP := by
  refine ⟨(DenseTimeBounds.runtimePolynomial boxed).natDegree, 64, DenseNetworkEmitter.machine boxed,
    DenseTimeBounds.lengthBound boxed, computesInTime boxed, ?_⟩
  exact _root_.Complexity.BigO.of_polynomial_bound (DenseTimeBounds.runtimePolynomial boxed)
    (fun L => (DenseTimeBounds.polynomial_eval boxed L).symm.le)

end JointThermoComplexity.Complexity.DenseNetworkFP

#print axioms JointThermoComplexity.Complexity.DenseNetworkFP.computesInTime
#print axioms JointThermoComplexity.Complexity.DenseNetworkFP.word_mem_FP
