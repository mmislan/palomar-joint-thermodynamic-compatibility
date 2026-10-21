module
public import proofs.JointThermoComplexity.Complexity.DensePacketChoice

set_option autoImplicit false
@[expose] public section

/-! Actual occurrence markers select a precompiled padding/template program.
Source numeric values affect tapes and output words, never machine construction. -/

namespace JointThermoComplexity.Complexity.DenseBankSelect
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseSourceFrame

def programs (boxed right : Bool) (m : ℕ) : TM 64 :=
  if hm : m ≤ 4 then seqTM (DenseReferenceBank.machine m) (DensePacketChoice.machine boxed right m hm) else emitBitsTM []
def machine (boxed right : Bool) : TM 64 :=
  OccurrenceTemplateDispatch.machine DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc
    DenseParserPorts.layout.flag.castSucc (programs boxed right) (emitBitsTM [])
def count (raw : List Bool) : ℕ := match OccurrenceDispatchControl.choice 4 raw with
  | none => 0
  | some m => 2 ^ m
def word (boxed right : Bool) (n N current v : ℕ) (negative : Bool) (raw : List Bool) : List Bool :=
  match OccurrenceDispatchControl.choice 4 raw with
  | none => []
  | some m => if hm : m ≤ 4 then DensePacketChoice.words boxed right m hm (DenseRawReady.values (DenseRawReady.rawValues raw))
      n N v negative current else []
def Payload (L n N current v : ℕ) (negative : Bool) (raw : List Bool) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Work L n N current R work ∧ Register v (work 0) ∧ (work 1).read = Γ.ofBool negative ∧
    BoundedOccurrenceMachine.Loaded DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc
      DenseParserPorts.layout.flag.castSucc raw work
def Pre (L n N current v : ℕ) (negative : Bool) (raw before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out => Cursor before input emitted inp work out ∧ Payload L n N current v negative raw R work
def timeBound (boxed right : Bool) (L n N B : ℕ) : ℕ := 4 * (12 * L + 10) + DensePacketChoice.timeBound boxed right n N B + 1

theorem count_le (raw : List Bool) : count raw ≤ 16 := by
  cases hc : OccurrenceDispatchControl.choice 4 raw with
  | none => simp only [count, hc]; omega
  | some m =>
    have hm := OffsetTemplateDispatch.choice_le 4 raw m hc
    simpa only [count, hc] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm

theorem selected_hoareTime (boxed right : Bool) (L n N B current v : ℕ) (negative : Bool) (raw : List Bool)
    (hlen : raw.length ≤ L) (hV : v.bits.length ≤ B) (hLB : L ≤ B) (hbase : N + 2 ≤ B)
    (hfit : current + count raw ≤ N + 2) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (before input emitted : List Bool) :
    (OccurrenceTemplateDispatch.selected (programs boxed right) (emitBitsTM []) (OccurrenceDispatchControl.choice 4 raw)).HoareTime
      (Pre L n N current v negative raw before input emitted R)
      (DenseSourceFrame.Pre L n N (current + count raw) before input (emitted ++ word boxed right n N current v negative raw) R)
      (timeBound boxed right L n N B) := by
  cases hc : OccurrenceDispatchControl.choice 4 raw with
  | none =>
    have hh := FixedOutput.hoareTime [] before input emitted (fun work => Work L n N current R work ∧ Register v (work 0) ∧
      (work 1).read = Γ.ofBool negative ∧ BoundedOccurrenceMachine.Loaded DenseParserPorts.layout.Physical
        DenseParserPorts.layout.ending.castSucc DenseParserPorts.layout.flag.castSucc raw work)
    apply hh.consequence (fun _ _ _ h => h)
    · rintro inp work out ⟨hcur, hs, hw, _hv, _hn, _hl⟩
      have hp : DenseSourceFrame.Pre L n N current before input (emitted ++ []) R inp work out := ⟨hcur, hs, hw⟩
      simpa only [count, word, hc, Nat.add_zero] using hp
    · exact Nat.zero_le _
  | some m =>
    have hm := OffsetTemplateDispatch.choice_le 4 raw m hc
    have hmlen : m = (DenseRawReady.rawValues raw).length := (DenseRawLoaded.choice_data 4 raw m hc).2
    have hpad : (DenseReferenceBank.machine m).HoareTime (Pre L n N current v negative raw before input emitted R)
        (DensePacketControl.Pre current 4 (by decide) (DenseRawReady.values (DenseRawReady.rawValues raw)) n N v negative
          before input emitted (PacketR L R)) (4 * (12 * L + 10)) := by
      rw [hmlen]
      have hh := DenseSourceBank.hoareTime L n N current v negative (DenseRawReady.rawValues raw) (DenseRawReady.raw_cap raw) R hR before input emitted
      apply hh.consequence
      · rintro inp work out ⟨hcur, hs, hw, hv, hn, hl⟩
        have he := DenseRawLoaded.encoded_of_choice DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc
          DenseParserPorts.layout.flag.castSucc raw work m (by simpa only [SparseOffsetLayout.physical_length] using hc) hl
        exact ⟨⟨hcur, hs, hw⟩, hv, hn, he⟩
      · exact fun _ _ _ h => h
      · exact le_rfl
    have hbits : ∀ p ∈ (DensePowerPorts.cellLayout 4 (by decide)).comparisons,
        ((DenseRawReady.values (DenseRawReady.rawValues raw)) p.constant).bits.length ≤ B :=
      DenseReferenceBank.bits (DenseRawReady.rawValues raw) B
        (fun x hx => ((BoundedOccurrenceControl.bits_length 4 raw x hx).trans hlen).trans hLB)
    have hp := DensePacketChoice.hoareTime boxed right m hm (DenseRawReady.values (DenseRawReady.rawValues raw)) L n N B v negative
      hV hbase hbits R hR before input current (by simpa only [count, hc] using hfit) emitted
    have hh := seqTM_hoareTime _ _ hpad (by
      intro inp work out h
      obtain ⟨hi, hw, ho⟩ := h.1.phase
      rw [hi, hw, ho]
      exact h) hp
    change (programs boxed right m).HoareTime (Pre L n N current v negative raw before input emitted R)
      (DenseSourceFrame.Pre L n N (current + count raw) before input
        (emitted ++ word boxed right n N current v negative raw) R) (timeBound boxed right L n N B)
    rw [programs, dite_eq_left hm]
    intro inp work out hpre
    obtain ⟨d, t, ht, hreach, hhalt, hpost⟩ := hh inp work out hpre
    refine ⟨d, t, by unfold timeBound; omega, hreach, hhalt, ?_⟩
    simpa only [count, word, hc, dite_eq_left hm] using hpost

theorem hoareTime (boxed right : Bool) (L n N B current v : ℕ) (negative : Bool) (raw : List Bool)
    (hlen : raw.length ≤ L) (hV : v.bits.length ≤ B) (hLB : L ≤ B) (hbase : N + 2 ≤ B)
    (hfit : current + count raw ≤ N + 2) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (before input emitted : List Bool) :
    (machine boxed right).HoareTime (Pre L n N current v negative raw before input emitted R)
      (DenseSourceFrame.Pre L n N (current + count raw) before input (emitted ++ word boxed right n N current v negative raw) R)
      (timeBound boxed right L n N B + 7) := by
  have hs := selected_hoareTime boxed right L n N B current v negative raw hlen hV hLB hbase hfit R hR before input emitted
  have hh := OccurrenceTemplateDispatch.loaded_hoareTime DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc
    DenseParserPorts.layout.flag.castSucc (programs boxed right) (emitBitsTM []) raw before input emitted before input
    (emitted ++ word boxed right n N current v negative raw) (Payload L n N current v negative raw R)
    (fun work => (∀ j, Parked (work j)) ∧ Work L n N (current + count raw) R work) (timeBound boxed right L n N B) (by
      rw [SparseOffsetLayout.physical_length]
      intro inp work out hpre
      exact hs inp work out hpre)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hw, hv, hn, hl⟩
    exact ⟨hc, ⟨hs, hw, hv, hn, hl⟩, hl⟩
  · exact fun _ _ _ h => h
  · rw [SparseOffsetLayout.physical_length]

end JointThermoComplexity.Complexity.DenseBankSelect

#print axioms JointThermoComplexity.Complexity.DenseBankSelect.hoareTime
