module
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset
public import proofs.JointThermoComplexity.Complexity.LiteralBufferAt

set_option autoImplicit false
@[expose] public section

/-! Reuse bounded binary buffers for successive signed/positive rational input fields. -/

namespace JointThermoComplexity.Complexity.BinaryBufferLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (tm : TM w) : TM (w + 1) :=
  seqTM (BinaryBufferReset.machine (CountSumAt.destination e)) (LiteralBufferAt.machine e tm)

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (tm : TM w)
    (old word before tail emitted : List Bool) (bound : ℕ)
    (hcopy : ∀ C : (Fin w → Tape) → Prop, tm.HoareTime
      (fun inp work out => Cursor before (word ++ tail) [] inp work out ∧ C work)
      (fun inp work out => Cursor (before ++ word) tail word inp work out ∧ C work) bound)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e tm).HoareTime
      (fun inp work out => Cursor before (word ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (CountSumAt.destination e)).HasBinaryContent old ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧
        (work (CountSumAt.destination e)).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ word) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix word ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work) (3 * old.length + bound + 10) := by
  have hc := BinaryBufferReset.hoareTime (CountSumAt.destination e) old before (word ++ tail) emitted R hR
  have hb := LiteralBufferAt.hoareTime e tm word before tail emitted bound hcopy R hR
  have hs := SafeExecution.hoareTime (LiteralBufferAt.machine e tm) _ _ bound hb (by
    rintro inp work out ⟨hcur, _, _, _⟩ j
    exact (hcur.works j).2)
  have hseq := seqTM_hoareTime (BinaryBufferReset.machine (CountSumAt.destination e))
    (LiteralBufferAt.machine e tm) hc (by
      rintro inp work out ⟨hcur, hsafe, hz, hr⟩
      obtain ⟨hi, hw, ho⟩ := hcur.phase
      rw [hi, hw, ho]
      exact ⟨⟨hcur, CountTape.empty_prefix_of_zero hz, hz.cell0, hr⟩, hsafe⟩) hs
  exact hseq.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨⟨hcur, hp, hz, hr⟩, hsafe⟩
    exact ⟨hcur, hsafe, hp, hz, hr⟩) (by omega)

def integerMachine (e : Fin (w + 1) ≃ Fin (w + 1)) : TM (w + 1) := machine e LiteralCopy.machine

def naturalMachine (e : Fin (w + 1) ≃ Fin (w + 1)) : TM (w + 1) := machine e (PayloadFrame.machine w)

theorem integer_hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (old : List Bool) (value : ℤ)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (integerMachine e).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work (CountSumAt.destination e)).HasBinaryContent old ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧
        (work (CountSumAt.destination e)).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode value) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work (CountSumAt.destination e)).HasBinaryPrefix (BitCodec.integerCode value) ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work)
      (3 * old.length + (BitCodec.integerCode value).length + 13) := by
  have hs := hoareTime e LiteralCopy.machine old (BitCodec.integerCode value) before tail emitted
    ((BitCodec.integerCode value).length + 3) (fun C => by
      simpa only [List.nil_append] using LiteralCopy.integer_hoareTime value before tail [] C) R hR
  exact hs.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by omega)

theorem natural_hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (old : List Bool) (value : ℕ)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (naturalMachine e).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work (CountSumAt.destination e)).HasBinaryContent old ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧
        (work (CountSumAt.destination e)).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work (CountSumAt.destination e)).HasBinaryPrefix (BitCodec.naturalCode value) ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work)
      (3 * old.length + (BitCodec.naturalCode value).length + 12) := by
  have hs := hoareTime e (PayloadFrame.machine w) old (BitCodec.naturalCode value) before tail emitted
    ((BitCodec.naturalCode value).length + 2) (fun C => by
      simpa only [BitCodec.naturalCode, List.nil_append] using PayloadCopy.hoareTime w value.bits before tail [] C) R hR
  exact hs.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by omega)

end JointThermoComplexity.Complexity.BinaryBufferLoad

#print axioms JointThermoComplexity.Complexity.BinaryBufferLoad.integer_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryBufferLoad.natural_hoareTime
