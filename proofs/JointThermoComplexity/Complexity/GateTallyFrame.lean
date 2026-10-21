module
public import proofs.JointThermoComplexity.Complexity.GateTallyMachine

set_option autoImplicit false
@[expose] public section

/-! Framed input-bit consumption and unary gate-count increments. -/

namespace JointThermoComplexity.Complexity.GateTallyFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt GateTallyMachine

variable {w : ℕ}

theorem other (idx j : Fin w) (add : Bool) (work : Fin w → Tape) (hj : j ≠ idx) :
    changedWork idx add work j = work j := by
  cases add <;> simp [changedWork, hj]

theorem append_count (idx : Fin w) (d : ℕ) (work : Fin w → Tape)
    (hp : (work idx).HasBinaryPrefix (List.replicate d true)) :
    (changedWork idx true work idx).HasBinaryPrefix (List.replicate (d + 1) true) := by
  simp only [changedWork, ↓reduceIte, Function.update_self]
  have h := Tape.hasBinaryPrefix_write_bit true hp
  simpa only [Γ.ofBool, List.replicate_add, List.replicate_one] using h

theorem append_zero (idx : Fin w) (d : ℕ) (work : Fin w → Tape)
    (hp : (work idx).HasBinaryPrefix (List.replicate d true)) (hz : (work idx).cells 0 = Γ.start) :
    (changedWork idx true work idx).cells 0 = Γ.start := by
  simp only [changedWork, ↓reduceIte, Function.update_self]
  exact Tape.hasBinaryPrefix_write_bit_cell0 true hp hz

theorem consume_one (idx : Fin w) (d : ℕ) (before remaining emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before (true :: remaining) emitted inp work out)
    (hp : (work idx).HasBinaryPrefix (List.replicate d true)) :
    Cursor (before ++ [true]) remaining emitted (inp.move .right) (changedWork idx true work) out := by
  have hm := InputCursor.consume true hc
  have hp' := append_count idx d work hp
  refine ⟨hm.cells, hm.head, ?_, hm.tapePrefix, hm.zero⟩
  intro j
  by_cases hj : j = idx
  · subst j
    exact ⟨by rw [hp'.read_blank]; simp, by rw [hp'.1]; omega⟩
  · rw [other idx j true work hj]
    exact hm.works j

theorem consume_bit (idx : Fin w) (bit : Bool) (d : ℕ) (before remaining emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before (bit :: remaining) emitted inp work out)
    (hp : (work idx).HasBinaryPrefix (List.replicate d true)) (hz : (work idx).cells 0 = Γ.start) :
    Cursor (before ++ [bit]) remaining emitted (inp.move .right) (changedWork idx bit work) out ∧
      (changedWork idx bit work idx).HasBinaryPrefix (List.replicate (d + bit.toNat) true) ∧
      (changedWork idx bit work idx).cells 0 = Γ.start := by
  cases bit with
  | false =>
    exact ⟨InputCursor.consume false hc, hp, hz⟩
  | true =>
    exact ⟨consume_one idx d before remaining emitted inp work out hc hp,
      append_count idx d work hp, append_zero idx d work hp hz⟩

theorem bit_step (idx : Fin w) (bit : Bool) (c : Cfg w (machine idx).Q)
    (hs : c.state = some true) (hr : c.input.read = Γ.ofBool bit)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨some false, c.input.move .right, changedWork idx bit c.work, c.output⟩ := by
  cases bit with
  | false => exact zero_step idx true c hs hr hw ho
  | true => exact one_step idx true c hs hr hw ho

end JointThermoComplexity.Complexity.GateTallyFrame

#print axioms JointThermoComplexity.Complexity.GateTallyFrame.consume_bit
