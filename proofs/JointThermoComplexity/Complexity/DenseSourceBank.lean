module
public import proofs.JointThermoComplexity.Complexity.DenseSourceFrame

set_option autoImplicit false
@[expose] public section

/-! Actual unused-buffer preparation turns a loaded source term into the full
four-reference packet precondition, retaining the surrounding source state. -/

namespace JointThermoComplexity.Complexity.DenseSourceBank
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseSourceFrame

def Frame (L n N current v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Keep L v negative work ∧ Core n N current R work

theorem frame_stable (m L n N current v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    DenseReferenceClear.Stable (DenseReferenceBank.unused m) (Frame L n N current v negative R) := by
  rintro work next he ⟨hk, hc⟩
  exact ⟨keep_bank_stable m L v negative work next he hk, core_bank_stable m n N current R hR work next he hc⟩

theorem hoareTime (L n N current v : ℕ) (negative : Bool) (vs : List ℕ) (hm : vs.length ≤ 4)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (before input emitted : List Bool) :
    (DenseReferenceBank.machine vs.length).HoareTime
      (fun inp work out => Pre L n N current before input emitted R inp work out ∧ Register v (work 0) ∧
        (work 1).read = Γ.ofBool negative ∧
        BoundedOccurrenceRun.Encoded DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc vs work)
      (DensePacketControl.Pre current 4 (by decide) (DenseRawReady.values vs) n N v negative before input emitted (PacketR L R))
      (4 * (12 * L + 10)) := by
  have hh := DenseReferenceBank.hoareTime L vs hm before input emitted (Frame L n N current v negative R)
    (frame_stable vs.length L n N current v negative R hR)
  apply hh.consequence
  · rintro inp work out ⟨⟨hc, hs, hp, hcore⟩, hv, hn, he⟩
    exact ⟨hc, hs, ref_ready L work hp, DenseReferenceBank.present_of_encoded vs hm work he,
      keep_of_parser L v negative work hp hv hn, hcore⟩
  · rintro inp work out ⟨hc, hs, hb, hk, hcore⟩
    exact packet_pre L n N current v negative vs R before input emitted inp work out hc hs hb hk hcore
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseSourceBank

#print axioms JointThermoComplexity.Complexity.DenseSourceBank.hoareTime
