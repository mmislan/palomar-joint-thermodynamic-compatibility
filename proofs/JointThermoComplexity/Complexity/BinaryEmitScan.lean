module
public import proofs.JointThermoComplexity.Complexity.BinaryEmitMachine

set_option autoImplicit false
@[expose] public section

/-! Exact payload serialization and the frame for the final source-register rewind. -/

namespace JointThermoComplexity.Complexity.BinaryEmitScan
open _root_.Complexity
open _root_.Complexity.TM
open BinaryEmitMachine

variable {w : ℕ}

theorem scan (remaining : List Bool) : ∀ (before emitted : List Bool) (idx : Fin w) (c : Cfg w State),
    c.state = .read → (c.work idx).HasBinaryContent (before ++ remaining) →
    (c.work idx).head = before.length + 1 → c.input.read ≠ Γ.start →
    (∀ j, j ≠ idx → (c.work j).read ≠ Γ.start) →
    c.output.HasBinaryPrefix emitted → c.output.cells 0 = Γ.start →
    ∃ d t, t ≤ 2 * remaining.length + 1 ∧ (machine idx).reachesIn t c d ∧ (machine idx).halted d ∧
      d.input = c.input ∧ (d.work idx).cells = (c.work idx).cells ∧
      (d.work idx).head = before.length + remaining.length + 1 ∧
      (∀ j, j ≠ idx → d.work j = c.work j) ∧
      d.output.HasBinaryPrefix (emitted ++ BitCodec.encodeBits remaining) ∧ d.output.cells 0 = Γ.start := by
  induction remaining with
  | nil =>
    intro before emitted idx c hs hc hh hi hw hp hz
    have hsource : (c.work idx).HasBinaryContent before := by simpa only [List.append_nil] using hc
    have hr := BinaryTape.read_end before hsource hh
    have hwork : (fun j => transitionTape (c.work j)) = c.work := by
      funext j
      apply transitionTape_eq_self
      by_cases hj : j = idx
      · subst j
        simp [hr]
      · exact hw j hj
    let d : Cfg w State := ⟨.done, transitionInput c.input,
      (fun j => transitionTape (c.work j)), c.output.writeAndMove Γ.zero .right⟩
    have hdin : d.input = c.input := transitionInput_eq_self hi
    have hdwork : d.work = c.work := hwork
    refine ⟨d, 1, by simp, .step (end_step idx c hs hr) .zero, rfl, hdin, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdwork]
    · simpa only [hdwork, List.length_nil, Nat.add_zero] using hh
    · intro j _
      exact congrFun hdwork j
    · exact Tape.hasBinaryPrefix_write_bit false hp
    · exact Tape.hasBinaryPrefix_write_bit_cell0 false hp hz
  | cons bit rest ih =>
    intro before emitted idx c hs hc hh hi hw hp hz
    have hr := BinaryTape.read_cons before rest bit hc hh
    have hsource : (c.work idx).read ≠ Γ.start := by rw [hr]; exact Γ.ofBool_ne_start bit
    let c₁ : Cfg w State := ⟨.bit bit, transitionInput c.input,
      (fun j => transitionTape (c.work j)), c.output.writeAndMove Γ.one .right⟩
    have hstep₁ : (machine idx).step c = some c₁ := prefix_step idx c bit hs hr
    have hi₁ : c₁.input = c.input := transitionInput_eq_self hi
    have hw₁ : c₁.work = c.work := by
      funext j
      apply transitionTape_eq_self
      by_cases hj : j = idx
      · subst j
        exact hsource
      · exact hw j hj
    have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [true]) := Tape.hasBinaryPrefix_write_bit true hp
    have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 true hp hz
    let c₂ : Cfg w State := ⟨.read, transitionInput c₁.input, readWork idx c₁.work,
      c₁.output.writeAndMove (Γ.ofBool bit) .right⟩
    have hstep₂ : (machine idx).step c₁ = some c₂ := bit_step idx c₁ bit rfl
    have hi₂ : c₂.input = c.input := (transitionInput_eq_self (by simpa only [hi₁] using hi)).trans hi₁
    have hw₂ : c₂.work = Function.update c.work idx ((c.work idx).move .right) := by
      funext j
      change readWork idx c₁.work j = _
      rw [hw₁]
      by_cases hj : j = idx
      · subst j
        simp only [readWork, ↓reduceIte, Function.update_self]
        exact writeAndMove_readBack (c.work idx) hsource .right
      · rw [readWork, ite_eq_right hj, Function.update_of_ne hj]
        exact transitionTape_eq_self (hw j hj)
    have hc₂ : (c₂.work idx).HasBinaryContent ((before ++ [bit]) ++ rest) := by
      rw [hw₂, Function.update_self]
      simpa only [List.append_assoc, List.singleton_append] using hc.move .right
    have hh₂ : (c₂.work idx).head = (before ++ [bit]).length + 1 := by
      simp [hw₂, Tape.move, hh, Nat.add_assoc]
    have hp₂ : c₂.output.HasBinaryPrefix ((emitted ++ [true]) ++ [bit]) := Tape.hasBinaryPrefix_write_bit bit hp₁
    have hz₂ : c₂.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 bit hp₁ hz₁
    have hother₂ : ∀ j, j ≠ idx → c₂.work j = c.work j := by
      intro j hj
      rw [hw₂, Function.update_of_ne hj]
    obtain ⟨d, t, ht, hreach, hhalt, hinp, hcells, hhead, hother, hprefix, hzero⟩ :=
      ih (before ++ [bit]) ((emitted ++ [true]) ++ [bit]) idx c₂ rfl hc₂ hh₂
        (by simpa only [hi₂] using hi) (fun j hj => by simpa only [hother₂ j hj] using hw j hj) hp₂ hz₂
    refine ⟨d, t + 1 + 1, by simp only [List.length_cons]; omega,
      .step hstep₁ (.step hstep₂ hreach), hhalt, hinp.trans hi₂, ?_, ?_, ?_, ?_, hzero⟩
    · simpa only [hw₂, Function.update_self, Tape.move_cells] using hcells
    · simp only [List.length_append, List.length_singleton] at hhead
      simp only [List.length_cons]
      omega
    · intro j hj
      exact (hother j hj).trans (hother₂ j hj)
    · simpa only [BitCodec.encodeBits, List.append_assoc, List.cons_append, List.nil_append] using hprefix

end JointThermoComplexity.Complexity.BinaryEmitScan

#print axioms JointThermoComplexity.Complexity.BinaryEmitScan.scan
