module
public import proofs.JointThermoComplexity.Complexity.BoxStoredWords

set_option autoImplicit false
@[expose] public section

/-! The actual present-box routine consumes four encoded fields and emits exactly one rational-box formula. -/

namespace JointThermoComplexity.Complexity.SomeBoxBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun BoxBufferState NetworkData

variable {w : ℕ}

def machine (scratch loNum loDen hiNum hiDen source : Fin (w + 1)) : TM (w + 1) :=
  seqTM (BoxLoad.machine loNum loDen hiNum hiDen) (BoxOutput.machine scratch loNum loDen hiNum hiDen source)

def timeBound (L : ℕ) : ℕ := 128 * L ^ 2 + 260 * L + 258

theorem hoareTime {arity : ℕ} (L : ℕ) (scratch loNum loDen hiNum hiDen source : Fin (w + 1))
    (sep : BoxLoad.Separate loNum loDen hiNum hiDen) (hne : source ≠ scratch)
    (hsource : ∀ j ∈ [loNum, loDen, hiNum, hiDen], source ≠ j)
    (hzero : ∀ j ∈ [loNum, loDen, hiNum, hiDen], scratch ≠ j)
    (b : ClosedBox) (idx : Fin arity) (hindex : idx.val ≤ 4 * L)
    (hln : (BitCodec.integerCode b.lower.numerator).length ≤ L)
    (hld : (BitCodec.naturalCode b.lower.denominator).length ≤ L)
    (hhn : (BitCodec.integerCode b.upper.numerator).length ≤ L)
    (hhd : (BitCodec.naturalCode b.upper.denominator).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work',
      (∀ j, j ≠ loNum → j ≠ loDen → j ≠ hiNum → j ≠ hiDen → work' j = work j) → R work → R work') :
    (machine scratch loNum loDen hiNum hiDen source).HoareTime
      (fun inp work out => Cursor before (DataCodec.box.code b ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work loNum) ∧ Reusable L (work loDen) ∧
        Reusable L (work hiNum) ∧ Reusable L (work hiDen) ∧ IsReg idx.val (work source) ∧
        Register 0 (work scratch) ∧ R work)
      (fun inp work out => Cursor (before ++ DataCodec.box.code b) tail
        (emitted ++ (NetworkFormula.boxFormula (some b) idx).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work loNum) ∧ Reusable L (work loDen) ∧
        Reusable L (work hiNum) ∧ Reusable L (work hiDen) ∧ IsReg idx.val (work source) ∧
        Register 0 (work scratch) ∧ R work) (timeBound L) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work => IsReg idx.val (work source) ∧ Register 0 (work scratch) ∧ R work
  have hP : ∀ work work',
      (∀ j, j ≠ loNum → j ≠ loDen → j ≠ hiNum → j ≠ hiDen → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hi, hz, hr⟩
    have hs := hw source (hsource loNum (by simp)) (hsource loDen (by simp))
      (hsource hiNum (by simp)) (hsource hiDen (by simp))
    have hz' := hw scratch (hzero loNum (by simp)) (hzero loDen (by simp))
      (hzero hiNum (by simp)) (hzero hiDen (by simp))
    exact ⟨by simpa only [hs] using hi, by simpa only [hz'] using hz, hR work work' hw hr⟩
  let T : (Fin (w + 1) → Tape) → Prop := fun work => Reusable L (work loNum) ∧ Reusable L (work loDen) ∧
    Reusable L (work hiNum) ∧ Reusable L (work hiDen) ∧ IsReg idx.val (work source) ∧ R work
  have hl := BoxLoad.hoareTime L loNum loDen hiNum hiDen sep b hln hld hhn hhd before tail emitted P hP
  have ho := BoxOutput.hoareTime L scratch loNum loDen hiNum hiDen source hne
    (fun _ => idx.val) (BoxStoredWords.buffers loNum loDen hiNum hiDen b) b idx rfl hindex
    (BoxStoredWords.lo_num loNum loDen hiNum hiDen b) (BoxStoredWords.lo_den loNum loDen hiNum hiDen sep b)
    (BoxStoredWords.hi_num loNum loDen hiNum hiDen sep b) (BoxStoredWords.hi_den loNum loDen hiNum hiDen sep b)
    (BoxStoredWords.sizes L loNum loDen hiNum hiDen sep b hln hld hhn hhd)
    (before ++ BoxLoad.code b) tail emitted T
  have hs := seqTM_hoareTime (BoxLoad.machine loNum loDen hiNum hiDen)
    (BoxOutput.machine scratch loNum loDen hiNum hiDen source) hl (by
      rintro inp work out ⟨hc, hsafe, hln, hld, hhn, hhd, hrln, hrld, hrhn, hrhd, hi, hz, hr⟩
      obtain ⟨hip, hw, hop⟩ := hc.phase
      rw [hip, hw, hop]
      exact ⟨hc, hsafe, hz, BoxStoredWords.ready loNum loDen hiNum hiDen source sep b idx work hi hln hld hhn hhd,
        hrln, hrld, hrhn, hrhd, hi, hr⟩) ho
  exact hs.consequence (by
    rintro inp work out ⟨hc, hsafe, hrln, hrld, hrhn, hrhd, hi, hz, hr⟩
    exact ⟨by simpa only [BoxLoad.code_eq] using hc, hsafe, hrln, hrld, hrhn, hrhd, hi, hz, hr⟩) (by
      rintro inp work out ⟨hc, hsafe, hz, _, hrln, hrld, hrhn, hrhd, hi, hr⟩
      exact ⟨by simpa only [BoxLoad.code_eq] using hc, hsafe, hrln, hrld, hrhn, hrhd, hi, hz, hr⟩)
    (by unfold BoxOutput.timeBound timeBound; omega)

end JointThermoComplexity.Complexity.SomeBoxBuild

#print axioms JointThermoComplexity.Complexity.SomeBoxBuild.hoareTime
