module
public import proofs.JointThermoComplexity.Complexity.DenseFixedPacket
public import proofs.JointThermoComplexity.Complexity.DenseSourceFrame

set_option autoImplicit false
@[expose] public section

/-! Both initial records return the complete source-pass state at current2,
including all four reference flags and the reusable parser buffers. -/

namespace JointThermoComplexity.Complexity.DenseFixedSourceBank
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseComplexOriginal DenseFixedComplexOriginal

def Pre (L n N U current : ℕ) (values : Fin 64 → ℕ) (before input emitted : List Bool)
    (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => DenseSourceFrame.Pre L n N current before input emitted R inp work out ∧ Register U (work 13) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout 4 (by decide)) values work

theorem hoareTime (boxed right : Bool) (L n N U B : ℕ) (values : Fin 64 → ℕ)
    (hU : U.bits.length ≤ B) (hbase : N + 2 ≤ B) (R : (Fin 64 → Tape) → Prop) (hR : DenseSourceFrame.Stable R)
    (before input emitted : List Bool) :
    (DenseFixedPacket.machine boxed right).HoareTime (Pre L n N U 0 values before input emitted R)
      (Pre L n N U 2 values before input (emitted ++ DenseFixedPacket.word boxed right n N U) R)
      (DenseFixedPacket.timeBound boxed right n N B) := by
  intro inp work out hp
  rcases hp with ⟨⟨hc, hs, hparser, hcore⟩, hreg, href⟩
  obtain ⟨u, hu, hn⟩ := hcore.next
  have hpre : DenseFixedRawStep.At 0 u 4 (by decide) values n N U before input emitted (DenseSourceFrame.PacketR L R) inp work out :=
    ⟨hc, hs, hcore.position, hn,
      ⟨hcore.cell, hcore.comparison, hcore.total, hcore.branch, href, hcore.arity, hreg, hcore.adjusted, hparser, hcore.frame⟩,
      hcore.ending, hcore.lastHead, hcore.scratch⟩
  obtain ⟨d, t, ht, hd, hh, hpost⟩ := DenseFixedPacket.hoareTime boxed right 4 (by decide) values n N U B u hU hbase hu
    (DenseSourceFrame.PacketR L R) (DenseSourceFrame.packet_stable L R hR) before input emitted inp work out hpre
  rcases hpost with ⟨hc', hs', hi', hn', ⟨hz, hcomp, hN, hb, href', ha, hreg', hadj, hparser', hr⟩, hend, hhead, hscratch⟩
  have hnext : (vertex true (initialVertex true N)).val ≤ N + 1 := by
    have hv := (vertex true (initialVertex true N)).isLt
    omega
  refine ⟨d, t, ht, hd, hh, ⟨hc', hs', hparser', ?_⟩, hreg', href'⟩
  refine ⟨hadj, ha, hN, hb, hi', ⟨_, hnext, hn'⟩, hz, hcomp, hend, hhead, ?_, hscratch, hr⟩
  intro i
  exact (href' (DensePowerPorts.comparison 4 (by decide) i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).2

end JointThermoComplexity.Complexity.DenseFixedSourceBank

#print axioms JointThermoComplexity.Complexity.DenseFixedSourceBank.hoareTime
