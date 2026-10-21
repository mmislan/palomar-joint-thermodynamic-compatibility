module
public import proofs.JointThermoComplexity.Complexity.SourceBinderReady
public import proofs.JointThermoComplexity.Complexity.UnaryBinaryBuild

set_option autoImplicit false
@[expose] public section

/-! Build the runtime binary arity from the bounded binder count while retaining parser state. -/

namespace JointThermoComplexity.Complexity.SourceArityBuild
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
variable {n : ℕ}

def machine (d : Layout n) : TM (n + 2) := UnaryBinaryBuild.machine d.formulaPending.castSucc d.right.castSucc
def timeBound (v : ℕ) : ℕ := v * (2 * v + 6) + (v + 2)

theorem hoareTime (d : Layout n) (L v : ℕ) (valid : Bool) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d).HoareTime (Inv d L 0 emitted R ⟨before, input, v, valid⟩)
      (Inv d L v emitted R ⟨before, input, v, valid⟩) (timeBound v) := by
  rintro inp work out ⟨hc, hr, hp, hf⟩
  let C : (Fin (n + 2) → Tape) → Prop := fun work' =>
    ∀ j, j ≠ d.formulaPending.castSucc → j ≠ d.right.castSucc → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ d.formulaPending.castSucc → j ≠ d.right.castSucc → work'' j = work' j) →
      C work' → C work'' := by
    intro work' work'' he hp j hjp hjr
    exact (he j hjp hjr).trans (hp j hjp hjr)
  have hne := SourcePendingFrame.cast_ne d.formulaSep.right
  obtain ⟨c, t, ht, hd, hh, hp', hc', hb', hother⟩ :=
    UnaryBinaryBuild.hoareTime d.formulaPending.castSucc d.right.castSucc hne v before input emitted C hC
      inp work out ⟨hp, hc, ⟨hr.base.arityBits, hr.base.arityZero⟩, fun _ _ _ => rfl⟩
  have hs' : ∀ j, Parked (c.work j) := by
    intro j
    by_cases hjp : j = d.formulaPending.castSucc
    · subst j
      exact hp'.parked
    · by_cases hjr : j = d.right.castSucc
      · subst j
        exact ⟨by rw [hb'.1.1], hb'.1.hasBinaryContent.cells_ne_start⟩
      · rw [hother j hjp hjr]
        exact hr.base.safe j
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.base.markers j, (hr.base.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hbuf := hother (NaturalScanBuffer.buffer n) (SourcePendingFrame.buffer_ne d.formulaPending) (SourcePendingFrame.buffer_ne d.right)
  have hleft := hother d.left.castSucc (SourcePendingFrame.cast_ne d.formulaSep.left.symm)
    (SourcePendingFrame.cast_ne d.operandSep.operands)
  have hflag := hother (NaturalScanBuffer.flag n) (SourcePendingFrame.cast_ne d.formulaSep.flag.symm)
    (SourcePendingFrame.cast_ne d.operandSep.flagRight)
  have hFuel := hother d.termFuel.castSucc (SourcePendingFrame.cast_ne d.fuelFormula) (SourcePendingFrame.cast_ne d.fuelSep.right)
  have hPending := hother d.termPending.castSucc (SourcePendingFrame.cast_ne d.pendingDistinct) (SourcePendingFrame.cast_ne d.termSep.right)
  have htags (i : Fin 3) := hother (d.tags i).castSucc (SourcePendingFrame.cast_ne (d.formulaSep.tags i).symm)
    (SourcePendingFrame.cast_ne (d.tagSep.right i))
  have hr' : Ready d L v R c.work :=
    ⟨⟨hs', fun j => (hm.2.1 j).1, by simpa only [hbuf] using hr.base.encoded,
      by simpa only [hleft] using hr.base.candidate, hb'.1, hb'.2, by simpa only [hflag] using hr.base.flagHead,
      hR _ _ (fun j hj => hother j.castSucc (SourcePendingFrame.cast_ne hj.formulaPending)
        (SourcePendingFrame.cast_ne hj.right)) hr.base.frame⟩,
      by simpa only [hFuel] using hr.termFuel, by simpa only [hPending] using hr.termPending,
      fun i => by simpa only [htags i] using hr.tagHeads i⟩
  exact ⟨c, t, ht, hd, hh, hc', hr', hp', by simpa only [hflag] using hf⟩

theorem timeBound_le (L v : ℕ) (hv : v ≤ L) : timeBound v ≤ 2 * L ^ 2 + 7 * L + 2 := by
  calc timeBound v ≤ L * (2 * L + 6) + (L + 2) :=
         Nat.add_le_add (Nat.mul_le_mul hv (by omega)) (by omega)
       _ = 2 * L ^ 2 + 7 * L + 2 := by ring1

end JointThermoComplexity.Complexity.SourceArityBuild

#print axioms JointThermoComplexity.Complexity.SourceArityBuild.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceArityBuild.timeBound_le
