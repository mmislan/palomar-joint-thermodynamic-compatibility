module
public import proofs.JointThermoComplexity.Complexity.LiteralCopy
public import proofs.JointThermoComplexity.Complexity.CountAppend

set_option autoImplicit false
@[expose] public section

/-! Route literal input fields into a binary work buffer while preserving the real formula output. -/

namespace JointThermoComplexity.Complexity.LiteralBuffer
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend

variable {w : ℕ}

theorem route_hoareTime (tm : TM w) (word before tail emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (bound : ℕ)
    (hcopy : tm.HoareTime
      (fun inp work out => Cursor before (word ++ tail) [] inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ word) tail word inp work out ∧ R work) bound) :
    tm.retargetOutput.HoareTime
      (fun inp work out => Cursor before (word ++ tail) emitted inp work out ∧
        (work destination).HasBinaryPrefix [] ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor (before ++ word) tail emitted inp work out ∧
        (work destination).HasBinaryPrefix word ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work)) bound := by
  rintro inp work out ⟨hc, hp, hz, hr⟩
  have hvcur : Cursor before (word ++ tail) [] inp (oldWork work) (work destination) :=
    ⟨hc.cells, hc.head, (fun j => hc.works j.castSucc), hp, hz⟩
  have hroute := OutputRoute.hoareTime tm _ _ bound (fun out' => out' = out) hcopy
  obtain ⟨e, t, ht, hreach, hhalt, _, heout, hecur, her⟩ :=
    hroute inp work out ⟨hc.output_read, rfl, hvcur, hr⟩
  have hePrefix : (e.work destination).HasBinaryPrefix word := hecur.tapePrefix
  have hecontent : (e.work destination).HasBinaryContent word := hePrefix.2
  have heworks : ∀ j, (e.work j).read ≠ Γ.start ∧ 1 ≤ (e.work j).head := by
    intro j
    by_cases hj : j.val < w
    · let k : Fin w := ⟨j.val, hj⟩
      have hk : j = k.castSucc := rfl
      rw [hk]
      exact hecur.works k
    · have hjlast : j = destination := by apply Fin.ext; change j.val = w; have hv := j.isLt; omega
      subst j
      exact ⟨by rw [Tape.read, hePrefix.1]; exact hecontent.cells_ne_start _ (by omega),
        by rw [hePrefix.1]; omega⟩
  refine ⟨e, t, ht, hreach, hhalt,
    ⟨hecur.cells, hecur.head, heworks, ?_, ?_⟩, hePrefix, hecur.zero, her⟩
  · simpa only [heout] using hc.tapePrefix
  · simpa only [heout] using hc.zero

def integerMachine : TM (w + 1) := (LiteralCopy.machine (w := w)).retargetOutput

def naturalMachine : TM (w + 1) := (PayloadFrame.machine w).retargetOutput

theorem integer_hoareTime (value : ℤ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (integerMachine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode value ++ tail) emitted inp work out ∧
        (work destination).HasBinaryPrefix [] ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor (before ++ BitCodec.integerCode value) tail emitted inp work out ∧
        (work destination).HasBinaryPrefix (BitCodec.integerCode value) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work)) ((BitCodec.integerCode value).length + 3) := by
  apply route_hoareTime (LiteralCopy.machine (w := w)) (BitCodec.integerCode value) before tail emitted R
  simpa only [List.nil_append] using LiteralCopy.integer_hoareTime value before tail [] R

theorem natural_hoareTime (value : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (naturalMachine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        (work destination).HasBinaryPrefix [] ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧
        (work destination).HasBinaryPrefix (BitCodec.naturalCode value) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work)) ((BitCodec.naturalCode value).length + 2) := by
  apply route_hoareTime (PayloadFrame.machine w) (BitCodec.naturalCode value) before tail emitted R
  simpa only [BitCodec.naturalCode, List.nil_append] using PayloadCopy.hoareTime w value.bits before tail [] R

end JointThermoComplexity.Complexity.LiteralBuffer

#print axioms JointThermoComplexity.Complexity.LiteralBuffer.integer_hoareTime
#print axioms JointThermoComplexity.Complexity.LiteralBuffer.natural_hoareTime
