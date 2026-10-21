module
public import proofs.JointThermoComplexity.Complexity.BinaryAddMachine

set_option autoImplicit false
@[expose] public section

/-! Every active transition consumes at least one source bit. Source contents
and the input tape are retained, and each source stops at its own payload end. -/

namespace JointThermoComplexity.Complexity.BinaryAddScan
open _root_.Complexity _root_.Complexity.TM BinaryAddMachine
variable {w : ℕ}

theorem finish (left right : Fin w) (carry : Bool) (c : Cfg w State) (emitted : List Bool)
    (hs : c.state = .scan carry) (hl : (c.work left).read = Γ.blank) (hr : (c.work right).read = Γ.blank)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start)
    (hp : c.output.HasBinaryPrefix emitted) (hz : c.output.cells 0 = Γ.start) :
    ∃ d, (machine left right).reachesIn 1 c d ∧ (machine left right).halted d ∧
      d.input = c.input ∧ d.work = c.work ∧
      d.output.HasBinaryPrefix (emitted ++ (if carry then [true] else [])) ∧ d.output.cells 0 = Γ.start := by
  have hinput := transitionInput_eq_self hi
  have hwork : (fun j => transitionTape (c.work j)) = c.work := funext (fun j => transitionTape_eq_self (hw j))
  have hread : readWork left right c.work = c.work := by
    funext j
    by_cases hjl : j = left
    · subst j
      rw [readWork_hit left right left c.work (Or.inl rfl) (hw left), hl]
      rfl
    · by_cases hjr : j = right
      · subst j
        rw [readWork_hit left right right c.work (Or.inr rfl) (hw right), hr]
        rfl
      · exact readWork_other left right j c.work hjl hjr (hw j)
  cases carry with
  | false =>
    have hout := transitionTape_eq_self (by rw [hp.read_blank]; decide)
    let d : Cfg w State := ⟨.done, c.input, c.work, c.output⟩
    have hstep : (machine left right).step c = some d := by
      rw [finish_false_step left right c hs hl hr, hinput, hwork, hout]
      rfl
    exact ⟨d, .step hstep .zero, rfl, rfl, rfl, by simpa only [Bool.false_eq_true, ↓reduceIte, List.append_nil] using hp, hz⟩
  | true =>
    let d : Cfg w State := ⟨.done, c.input, c.work, c.output.writeAndMove Γ.one .right⟩
    have hstep : (machine left right).step c = some d := by
      rw [finish_true_step left right c hs hl hr, hinput, hread]
      rfl
    exact ⟨d, .step hstep .zero, rfl, rfl, rfl,
      Tape.hasBinaryPrefix_write_bit true hp, Tape.hasBinaryPrefix_write_bit_cell0 true hp hz⟩

theorem scan (xs ys : List Bool) : ∀ (beforeLeft beforeRight emitted : List Bool) (left right : Fin w)
    (carry : Bool) (c : Cfg w State), left ≠ right → c.state = .scan carry →
    (c.work left).HasBinaryContent (beforeLeft ++ xs) → (c.work left).head = beforeLeft.length + 1 →
    (c.work right).HasBinaryContent (beforeRight ++ ys) → (c.work right).head = beforeRight.length + 1 →
    c.input.read ≠ Γ.start → (∀ j, j ≠ left → j ≠ right → (c.work j).read ≠ Γ.start) →
    c.output.HasBinaryPrefix emitted → c.output.cells 0 = Γ.start →
    ∃ d t, t ≤ xs.length + ys.length + 1 ∧ (machine left right).reachesIn t c d ∧
      (machine left right).halted d ∧ d.input = c.input ∧
      (d.work left).cells = (c.work left).cells ∧ (d.work left).head = beforeLeft.length + xs.length + 1 ∧
      (d.work right).cells = (c.work right).cells ∧ (d.work right).head = beforeRight.length + ys.length + 1 ∧
      (∀ j, j ≠ left → j ≠ right → d.work j = c.work j) ∧
      d.output.HasBinaryPrefix (emitted ++ BinaryAddControl.add carry xs ys) ∧ d.output.cells 0 = Γ.start := by
  generalize hN : xs.length + ys.length = N
  induction N using Nat.strong_induction_on generalizing xs ys with
  | h N ih =>
    intro beforeLeft beforeRight emitted left right carry c hne hs hl hhl hr hhr hi hw hp hz
    have hxl := source_read beforeLeft xs (c.work left) hl hhl
    have hyr := source_read beforeRight ys (c.work right) hr hhr
    by_cases hnil : xs = [] ∧ ys = []
    · obtain ⟨rfl, rfl⟩ := hnil
      have hlread : (c.work left).read = Γ.blank :=
        BinaryTape.read_end beforeLeft (by simpa only [List.append_nil] using hl) hhl
      have hrread : (c.work right).read = Γ.blank :=
        BinaryTape.read_end beforeRight (by simpa only [List.append_nil] using hr) hhr
      have hwork : ∀ j, (c.work j).read ≠ Γ.start := by
        intro j
        by_cases hjl : j = left
        · simpa only [hjl] using hxl.2.2
        · by_cases hjr : j = right
          · simpa only [hjr] using hyr.2.2
          · exact hw j hjl hjr
      obtain ⟨d, hd, hh, hinp, hworks, hprefix, hzero⟩ := finish left right carry c emitted hs hlread hrread hi hwork hp hz
      refine ⟨d, 1, by simp, hd, hh, hinp, ?_, ?_, ?_, ?_, ?_, ?_, hzero⟩
      · rw [hworks]
      · simpa only [hworks, List.length_nil, Nat.add_zero] using hhl
      · rw [hworks]
      · simpa only [hworks, List.length_nil, Nat.add_zero] using hhr
      · intro j _ _; exact congrFun hworks j
      · cases carry <;> simpa only [BinaryAddControl.add, Bool.false_eq_true, ↓reduceIte] using hprefix
    · have hn : xs ≠ [] ∨ ys ≠ [] := by
        by_cases hx : xs = []
        · exact Or.inr (fun hy => hnil ⟨hx, hy⟩)
        · exact Or.inl hx
      have hdec : (xs.drop 1).length + (ys.drop 1).length < N := by
        have hpos : 0 < xs.length ∨ 0 < ys.length := by
          rcases hn with hx | hy
          · have hx0 : xs.length ≠ 0 := fun he => hx (List.eq_nil_of_length_eq_zero he)
            exact Or.inl (Nat.pos_of_ne_zero hx0)
          · have hy0 : ys.length ≠ 0 := fun he => hy (List.eq_nil_of_length_eq_zero he)
            exact Or.inr (Nat.pos_of_ne_zero hy0)
        simp only [List.length_drop]
        omega
      have ha : (present (c.work left).read || present (c.work right).read) = true := by
        rw [hxl.1, hyr.1]
        rcases hn with hx | hy
        · simp [hx]
        · simp [hy]
      let c₁ : Cfg w State := ⟨.scan (BinaryAddControl.next carry (head xs) (head ys)), c.input,
        readWork left right c.work,
        c.output.writeAndMove (Γ.ofBool (BinaryAddControl.digit carry (head xs) (head ys))) .right⟩
      have hstep : (machine left right).step c = some c₁ := by
        rw [emit_step left right carry c hs ha, hxl.2.1, hyr.2.1, transitionInput_eq_self hi]
        rfl
      have hla := source_advance left right left c.work (Or.inl rfl) beforeLeft xs hl hhl
      have hra := source_advance left right right c.work (Or.inr rfl) beforeRight ys hr hhr
      have hother : ∀ j, j ≠ left → j ≠ right → c₁.work j = c.work j := by
        intro j hjl hjr
        exact readWork_other left right j c.work hjl hjr (hw j hjl hjr)
      have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [BinaryAddControl.digit carry (head xs) (head ys)]) :=
        Tape.hasBinaryPrefix_write_bit _ hp
      have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 _ hp hz
      obtain ⟨d, t, ht, hd, hh, hinp, hcl, hdl, hcr, hdr, hwo, hprefix, hzero⟩ :=
        ih ((xs.drop 1).length + (ys.drop 1).length) hdec (xs.drop 1) (ys.drop 1) rfl
          (beforeLeft ++ xs.take 1) (beforeRight ++ ys.take 1)
          (emitted ++ [BinaryAddControl.digit carry (head xs) (head ys)]) left right
          (BinaryAddControl.next carry (head xs) (head ys)) c₁ hne rfl hla.1 hla.2.1 hra.1 hra.2.1 hi
          (fun j hjl hjr => by rw [hother j hjl hjr]; exact hw j hjl hjr) hp₁ hz₁
      have hlenx := congrArg List.length (List.take_append_drop 1 xs)
      have hleny := congrArg List.length (List.take_append_drop 1 ys)
      simp only [List.length_append] at hlenx hleny hdl hdr
      refine ⟨d, t + 1, by omega, .step hstep hd, hh, hinp, hcl.trans hla.2.2, by omega,
        hcr.trans hra.2.2, by omega, ?_, ?_, hzero⟩
      · intro j hjl hjr
        exact (hwo j hjl hjr).trans (hother j hjl hjr)
      · rw [add_step carry xs ys hn]
        simpa only [List.append_assoc, List.singleton_append] using hprefix

end JointThermoComplexity.Complexity.BinaryAddScan

#print axioms JointThermoComplexity.Complexity.BinaryAddScan.finish
#print axioms JointThermoComplexity.Complexity.BinaryAddScan.scan
