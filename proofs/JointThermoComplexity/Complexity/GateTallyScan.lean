module
public import proofs.JointThermoComplexity.Complexity.GateTallyFrame
public import proofs.JointThermoComplexity.Complexity.ExactGateCount

set_option autoImplicit false
@[expose] public section

/-! Exact encoded-payload gate tally with preserved real output and other work tapes. -/

namespace JointThermoComplexity.Complexity.GateTallyScan
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt GateTallyMachine

variable {w : ℕ}

theorem scan (bits : List Bool) : ∀ (before tail emitted : List Bool) (count : ℕ) (idx : Fin w) (c : Cfg w (machine idx).Q),
    c.state = some false → Cursor before (BitCodec.encodeBits bits ++ tail) emitted c.input c.work c.output →
    (c.work idx).HasBinaryPrefix (List.replicate count true) → (c.work idx).cells 0 = Γ.start →
    ∃ e t, t ≤ 2 * bits.length + 1 ∧ (machine idx).reachesIn t c e ∧ (machine idx).halted e ∧
      Cursor (before ++ BitCodec.encodeBits bits) tail emitted e.input e.work e.output ∧
      (e.work idx).HasBinaryPrefix (List.replicate (count + ExactGateCount.bitsCost bits) true) ∧
      (e.work idx).cells 0 = Γ.start ∧ (∀ j, j ≠ idx → e.work j = c.work j) := by
  induction bits with
  | nil =>
    intro before tail emitted count idx c hs hc hp hz
    let e : Cfg w (machine idx).Q := ⟨none, c.input.move .right, c.work, c.output⟩
    have hstep : (machine idx).step c = some e := zero_step idx false c hs (InputCursor.read_bit false hc)
      (fun j => (hc.works j).1) hc.output_read
    exact ⟨e, 1, by simp, .step hstep .zero, rfl, InputCursor.consume false hc, hp, hz, fun _ _ => rfl⟩
  | cons bit rest ih =>
    intro before tail emitted count idx c hs hc hp hz
    let c₁ : Cfg w (machine idx).Q := ⟨some true, c.input.move .right, changedWork idx true c.work, c.output⟩
    have hstep₁ : (machine idx).step c = some c₁ := one_step idx false c hs (InputCursor.read_bit true hc)
      (fun j => (hc.works j).1) hc.output_read
    have hc₁ : Cursor (before ++ [true]) (bit :: (BitCodec.encodeBits rest ++ tail)) emitted c₁.input c₁.work c₁.output :=
      GateTallyFrame.consume_one idx count before _ emitted c.input c.work c.output hc hp
    have hp₁ : (c₁.work idx).HasBinaryPrefix (List.replicate (count + 1) true) := GateTallyFrame.append_count idx count c.work hp
    have hz₁ : (c₁.work idx).cells 0 = Γ.start := GateTallyFrame.append_zero idx count c.work hp hz
    let c₂ : Cfg w (machine idx).Q := ⟨some false, c₁.input.move .right, changedWork idx bit c₁.work, c₁.output⟩
    have hstep₂ : (machine idx).step c₁ = some c₂ := GateTallyFrame.bit_step idx bit c₁ rfl (InputCursor.read_bit bit hc₁)
      (fun j => (hc₁.works j).1) hc₁.output_read
    obtain ⟨hc₂, hp₂, hz₂⟩ := GateTallyFrame.consume_bit idx bit (count + 1) (before ++ [true])
      (BitCodec.encodeBits rest ++ tail) emitted c₁.input c₁.work c₁.output hc₁ hp₁ hz₁
    obtain ⟨e, t, ht, hreach, hhalt, hecur, hep, hez, heother⟩ :=
      ih ((before ++ [true]) ++ [bit]) tail emitted (count + 1 + bit.toNat) idx c₂ rfl hc₂ hp₂ hz₂
    have hcost : (count + 1 + bit.toNat) + ExactGateCount.bitsCost rest =
        count + ExactGateCount.bitsCost (bit :: rest) := by
      cases bit <;> simp [ExactGateCount.bitsCost] <;> omega
    refine ⟨e, t + 1 + 1, by simp only [List.length_cons]; omega,
      .step hstep₁ (.step hstep₂ hreach), hhalt, ?_, ?_, hez, ?_⟩
    · simpa only [BitCodec.encodeBits, List.append_assoc, List.cons_append, List.nil_append] using hecur
    · simpa only [hcost] using hep
    · intro j hj
      exact (heother j hj).trans ((GateTallyFrame.other idx j bit c₁.work hj).trans (GateTallyFrame.other idx j true c.work hj))

end JointThermoComplexity.Complexity.GateTallyScan

#print axioms JointThermoComplexity.Complexity.GateTallyScan.scan
