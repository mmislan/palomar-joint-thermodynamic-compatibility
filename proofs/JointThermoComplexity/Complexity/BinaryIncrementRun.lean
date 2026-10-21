module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementScan
public import proofs.JointThermoComplexity.Complexity.BinaryRewind

set_option autoImplicit false
@[expose] public section

/-! A complete framed binary-register increment, including return to cell one. -/

namespace JointThermoComplexity.Complexity.BinaryIncrementRun
open _root_.Complexity
open _root_.Complexity.TM
open BinaryIncrementMachine BinaryIncrementControl

variable {w : ℕ}

def Register (value : ℕ) (t : Tape) : Prop := t.HasBinaryString value.bits ∧ t.cells 0 = Γ.start

theorem Register.read_ne_start {value : ℕ} {t : Tape} (h : Register value t) : t.read ≠ Γ.start := by
  rw [Tape.read, h.1.1]
  exact h.1.hasBinaryContent.cells_ne_start 1 le_rfl

theorem run (idx : Fin w) (bits : List Bool) (c : Cfg w State)
    (hs : c.state = .carry) (hbits : (c.work idx).HasBinaryString bits) (hz : (c.work idx).cells 0 = Γ.start)
    (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) (hohead : 1 ≤ c.output.head)
    (hw : ∀ j, j ≠ idx → (c.work j).read ≠ Γ.start ∧ 1 ≤ (c.work j).head) :
    ∃ d t, t ≤ 2 * bits.length + 4 ∧ (machine idx).reachesIn t c d ∧ (machine idx).halted d ∧
      d.input = c.input ∧ d.output = c.output ∧ (∀ j, j ≠ idx → d.work j = c.work j) ∧
      (d.work idx).HasBinaryString (increment bits) ∧ (d.work idx).cells 0 = Γ.start := by
  obtain ⟨d, td, htd, hreachd, hsd, hid, hod, hwd, hbd, hzd, _, hhd⟩ :=
    BinaryIncrementScan.scan bits [] idx c hs hbits.2 hbits.1 hz hi ho (fun j hj => (hw j hj).1)
  have hbound : (d.work idx).head ≤ bits.length + 1 := by simpa using hhd
  obtain ⟨e, te, hte, hreache, hhalte, hie, hoe, hwe, hbe, hze⟩ :=
    BinaryRewind.run idx (increment bits) (bits.length + 1) d hsd hbd hzd hbound
      (by simpa only [hid] using hi) (by simpa only [hod] using ho)
      (by simpa only [hod] using hohead)
      (fun j hj => by simpa only [hwd j hj] using hw j hj)
  refine ⟨e, td + te, by omega, reachesIn_trans _ hreachd hreache, hhalte, hie.trans hid, hoe.trans hod,
    ?_, hbe, hze⟩
  intro j hj
  exact (hwe j hj).trans (hwd j hj)

theorem run_nat (idx : Fin w) (value : ℕ) (c : Cfg w State) (hs : c.state = .carry)
    (hreg : Register value (c.work idx))
    (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) (hohead : 1 ≤ c.output.head)
    (hw : ∀ j, j ≠ idx → (c.work j).read ≠ Γ.start ∧ 1 ≤ (c.work j).head) :
    ∃ d t, t ≤ 2 * value.bits.length + 4 ∧ (machine idx).reachesIn t c d ∧ (machine idx).halted d ∧
      d.input = c.input ∧ d.output = c.output ∧ (∀ j, j ≠ idx → d.work j = c.work j) ∧ Register (value + 1) (d.work idx) := by
  simpa only [Register, increment_bits] using run idx value.bits c hs hreg.1 hreg.2 hi ho hohead hw

end JointThermoComplexity.Complexity.BinaryIncrementRun

#print axioms JointThermoComplexity.Complexity.BinaryIncrementRun.run
#print axioms JointThermoComplexity.Complexity.BinaryIncrementRun.run_nat
