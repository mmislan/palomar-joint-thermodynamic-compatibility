module
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Read-only canonical natural-field scan; no numeric value is expanded. -/

namespace JointThermoComplexity.Complexity.NaturalSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def advance (next : Option Bool) (_si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (next, (fun j => readBackWrite (sw j)), readBackWrite so, .right, (fun j => idleDir (sw j)), idleDir so)

def next (phase bit : Bool) : Option Bool := if phase then some false else if bit then some true else none

def machine : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ q si sw so := match q, si with
    | some phase, .one => advance (next phase true) si sw so
    | some phase, .zero => advance (next phase false) si sw so
    | _, _ => allReadBack none si sw so
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some phase =>
      cases si <;> first
        | exact rightOfStart_allReadBack _ sw so
        | exact ⟨fun _ => rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

theorem bit_step (phase bit : Bool) (c : Cfg w (machine (w := w)).Q)
    (hs : c.state = some phase) (hr : c.input.read = Γ.ofBool bit)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    machine.step c = some ⟨next phase bit, c.input.move .right, c.work, c.output⟩ := by
  have hδ : machine.δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      advance (next phase bit) c.input.read (fun j => (c.work j).read) c.output.read := by
    cases bit <;> simp [machine, hs, hr, Γ.ofBool]
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem scan (bits : List Bool) : ∀ (before tail emitted : List Bool) (c : Cfg w (machine (w := w)).Q),
    c.state = some false → Cursor before (BitCodec.encodeBits bits ++ tail) emitted c.input c.work c.output →
    ∃ e t, t ≤ 2 * bits.length + 1 ∧ machine.reachesIn t c e ∧ machine.halted e ∧
      Cursor (before ++ BitCodec.encodeBits bits) tail emitted e.input e.work e.output ∧
      e.work = c.work ∧ e.output = c.output := by
  induction bits with
  | nil =>
    intro before tail emitted c hs hc
    let e : Cfg w (machine (w := w)).Q := ⟨none, c.input.move .right, c.work, c.output⟩
    have hstep : machine.step c = some e := bit_step false false c hs (InputCursor.read_bit false hc)
      (fun j => (hc.works j).1) hc.output_read
    exact ⟨e, 1, by simp, .step hstep .zero, rfl, InputCursor.consume false hc, rfl, rfl⟩
  | cons bit rest ih =>
    intro before tail emitted c hs hc
    let c₁ : Cfg w (machine (w := w)).Q := ⟨some true, c.input.move .right, c.work, c.output⟩
    have hstep₁ : machine.step c = some c₁ := bit_step false true c hs (InputCursor.read_bit true hc)
      (fun j => (hc.works j).1) hc.output_read
    have hc₁ : Cursor (before ++ [true]) (bit :: (BitCodec.encodeBits rest ++ tail)) emitted c₁.input c₁.work c₁.output :=
      InputCursor.consume true hc
    let c₂ : Cfg w (machine (w := w)).Q := ⟨some false, c₁.input.move .right, c₁.work, c₁.output⟩
    have hstep₂ : machine.step c₁ = some c₂ := by
      simpa only [next, ↓reduceIte] using bit_step true bit c₁ rfl (InputCursor.read_bit bit hc₁)
        (fun j => (hc₁.works j).1) hc₁.output_read
    have hc₂ := InputCursor.consume bit hc₁
    obtain ⟨e, t, ht, hreach, hhalt, hecur, hework, heout⟩ :=
      ih ((before ++ [true]) ++ [bit]) tail emitted c₂ rfl hc₂
    refine ⟨e, t + 1 + 1, by simp only [List.length_cons]; omega,
      .step hstep₁ (.step hstep₂ hreach), hhalt, ?_, hework, heout⟩
    simpa only [BitCodec.encodeBits, List.append_assoc, List.cons_append, List.nil_append] using hecur

theorem hoareTime (value : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (BitCodec.naturalCode value).length := by
  rintro inp work out ⟨hc, hs, hr⟩
  obtain ⟨e, t, ht, hreach, hhalt, hecur, hework, _⟩ :=
    scan value.bits before tail emitted ⟨some false, inp, work, out⟩ rfl hc
  exact ⟨e, t, by simpa only [BitCodec.naturalCode, BitCodec.encodeBits_length] using ht,
    hreach, hhalt, hecur, by simpa only [hework] using hs, by simpa only [hework] using hr⟩

end JointThermoComplexity.Complexity.NaturalSkip

#print axioms JointThermoComplexity.Complexity.NaturalSkip.hoareTime
