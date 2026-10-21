module
public import proofs.JointThermoComplexity.Complexity.HeaderMachineRun

set_option autoImplicit false
@[expose] public section

/-! Exact codec agreement and suffix-independent execution of dimension headers. -/

namespace JointThermoComplexity.Complexity.HeaderMachineParser
open _root_.Complexity
open _root_.Complexity.TM
open HeaderMachine

variable {n : ℕ}

theorem codec_status_iff (input : List Bool) {value : Γ}
    (h : value = Γ.ofBool (HeaderControl.valid input)) :
    value = Γ.one ↔ ∃ k suffix, NetworkCodec.dimension.parse input = some (k, suffix) := by
  rw [h, ← HeaderControl.valid_iff_parse]
  cases HeaderControl.valid input <;> simp [Γ.ofBool]

theorem decoded_count {input suffix : List Bool} {k : ℕ}
    (h : NetworkCodec.dimension.parse input = some (k, suffix)) :
    HeaderControl.count input = k ∧ HeaderControl.copied input = RealSyntax.binderCode k ∧
      HeaderControl.suffix input = suffix ∧ HeaderControl.valid input = true := by
  rw [NetworkCodec.dimension.sound h]
  exact ⟨HeaderControl.count_code k suffix, HeaderControl.copied_code k suffix,
    HeaderControl.suffix_code k suffix, HeaderControl.valid_code k suffix⟩

theorem encoded_frame (k : ℕ) (before emitted suffix : List Bool)
    (c : Cfg (n + 2) (machine n).Q) (hs : c.state = .start)
    (hcells : c.input.cells =
      (Tape.init ((before ++ (RealSyntax.binderCode k ++ suffix)).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (hc : IsReg 0 (c.work (counterIndex n))) (hf : (c.work (flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hz : c.output.cells 0 = Γ.start) :
    ∃ e t, t ≤ 2 * k + 5 ∧ (machine n).reachesIn t c e ∧ (machine n).halted e ∧
      e.input.cells = c.input.cells ∧ e.input.head = before.length + (k + 1) + 1 ∧
      (∀ i, i ≠ counterIndex n → i ≠ flagIndex n → e.work i = c.work i) ∧
      IsReg k (e.work (counterIndex n)) ∧ (e.work (flagIndex n)).head = 1 ∧
      (e.work (flagIndex n)).read = Γ.one ∧ e.output.cells 0 = Γ.start ∧
      e.output.HasBinaryPrefix (emitted ++ RealSyntax.binderCode k) := by
  have hlen : (RealSyntax.binderCode k).length = k + 1 := by
    simp [RealSyntax.binderCode]
  simpa only [HeaderControl.count_code, HeaderControl.copied_code, HeaderControl.valid_code,
    hlen, Γ.ofBool] using HeaderMachineRun.run_count_bound before emitted
      (RealSyntax.binderCode k ++ suffix) c hs hcells hhead hw hc hf hp hz

end JointThermoComplexity.Complexity.HeaderMachineParser

#print axioms JointThermoComplexity.Complexity.HeaderMachineParser.codec_status_iff
#print axioms JointThermoComplexity.Complexity.HeaderMachineParser.decoded_count
#print axioms JointThermoComplexity.Complexity.HeaderMachineParser.encoded_frame
