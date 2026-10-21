module
public import proofs.JointThermoComplexity.Complexity.PayloadLoopSteps
public import proofs.JointThermoComplexity.Complexity.PowerAddressStep

set_option autoImplicit false
@[expose] public section

/-! The finite controller processes an entire self-delimiting exponent payload. -/

namespace JointThermoComplexity.Complexity.PowerPayloadRun
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts PowerAddressState

def machine (m : ℕ) : TM (m + 13) := PayloadLoopMachine.machine (PowerBitStep.machine m)

def timeBound (L count : ℕ) : ℕ := count * (PowerBitStep.timeBound L + 2) + 1

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L)
    (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m →
      j ≠ PowerBitState.flag m → work' j = work j) → R work → R work')
    (bits : List Bool) (s : State) (before tail emitted : List Bool) (hf : Fits arity bits s) :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.encodeBits bits ++ tail) emitted inp work out ∧
        PowerAddressFrame.Ready m s R work)
      (fun inp work out => Cursor (before ++ BitCodec.encodeBits bits) tail
        (emitted ++ PowerAddressCode.stream s bits) inp work out ∧
        PowerAddressFrame.Ready m (s.run bits) R work) (timeBound L bits.length) := by
  induction bits generalizing s before emitted with
  | nil =>
    intro inp work out hp
    have hc : Cursor before (false :: tail) emitted inp work out := hp.1
    have hstep := PayloadLoopSteps.test_zero (PowerBitStep.machine m) before tail emitted inp work out hc
    refine ⟨⟨(machine m).qhalt, inp.move .right, work, out⟩, 1, by simp [timeBound],
      .step hstep .zero, rfl, ?_, hp.2⟩
    simpa only [BitCodec.encodeBits, PowerAddressCode.stream, List.append_nil] using InputCursor.consume false hc
  | cons bit bits ih =>
    intro inp work out hp
    have hc : Cursor before (true :: bit :: (BitCodec.encodeBits bits ++ tail)) emitted inp work out := hp.1
    have htest := PayloadLoopSteps.test_one (PowerBitStep.machine m) before
      (bit :: (BitCodec.encodeBits bits ++ tail)) emitted inp work out hc
    have hconsume := InputCursor.consume true hc
    obtain ⟨cb, tb, htb, hb, hhalt, hcb, hready⟩ :=
      PowerAddressStep.hoareTime m arity L ha s bit bits hf (before ++ [true])
        (BitCodec.encodeBits bits ++ tail) emitted R hR (inp.move .right) work out ⟨hconsume, hp.2⟩
    have hlift := PayloadLoopMachine.body_reaches (PowerBitStep.machine m) hb
    have hback := PayloadLoopSteps.loopback (PowerBitStep.machine m) ((before ++ [true]) ++ [bit])
      (BitCodec.encodeBits bits ++ tail) (emitted ++ PowerAddressCode.word s bit) cb hhalt hcb
    obtain ⟨d, t, ht, hr, hd, hdc, hdr⟩ := ih (s.advance bit) ((before ++ [true]) ++ [bit])
      (emitted ++ PowerAddressCode.word s bit) (step_fresh arity bit bits s hf).2.2
      cb.input cb.work cb.output ⟨hcb, hready⟩
    refine ⟨d, tb + (t + 1) + 1, ?_, .step htest (reachesIn_trans _ hlift (.step hback hr)), hd, ?_, hdr⟩
    · have hm : (bits.length + 1) * (PowerBitStep.timeBound L + 2) =
          bits.length * (PowerBitStep.timeBound L + 2) + (PowerBitStep.timeBound L + 2) := Nat.succ_mul ..
      simp only [timeBound, List.length_cons] at ht ⊢
      omega
    · simpa only [BitCodec.encodeBits, PowerAddressCode.stream, List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append] using hdc

end JointThermoComplexity.Complexity.PowerPayloadRun

#print axioms JointThermoComplexity.Complexity.PowerPayloadRun.hoareTime
