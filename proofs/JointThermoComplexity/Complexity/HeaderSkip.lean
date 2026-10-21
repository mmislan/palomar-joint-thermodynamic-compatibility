module
public import proofs.JointThermoComplexity.Complexity.NaturalSkip
public import proofs.JointThermoComplexity.Complexity.RealSyntax

set_option autoImplicit false
@[expose] public section

/-! Read-only unary dimension-header traversal with exact bit-length runtime. -/

namespace JointThermoComplexity.Complexity.HeaderSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ q si sw so := match q, si with
    | some _, .one => NaturalSkip.advance (some false) si sw so
    | some _, .zero => NaturalSkip.advance none si sw so
    | _, _ => allReadBack none si sw so
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some phase =>
      cases si <;> first
        | exact rightOfStart_allReadBack _ sw so
        | exact ⟨fun _ => rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

theorem bit_step (bit : Bool) (c : Cfg w (machine (w := w)).Q)
    (hs : c.state = some false) (hr : c.input.read = Γ.ofBool bit)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    machine.step c = some ⟨(if bit then some false else none), c.input.move .right, c.work, c.output⟩ := by
  have hδ : machine.δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      NaturalSkip.advance (if bit then some false else none) c.input.read (fun j => (c.work j).read) c.output.read := by
    cases bit <;> simp [machine, hs, hr, Γ.ofBool]
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem scan (v : ℕ) : ∀ (before tail emitted : List Bool) (c : Cfg w (machine (w := w)).Q),
    c.state = some false → Cursor before (RealSyntax.binderCode v ++ tail) emitted c.input c.work c.output →
    ∃ e t, t ≤ v + 1 ∧ machine.reachesIn t c e ∧ machine.halted e ∧
      Cursor (before ++ RealSyntax.binderCode v) tail emitted e.input e.work e.output ∧ e.work = c.work := by
  induction v with
  | zero =>
    intro before tail emitted c hs hc
    let e : Cfg w (machine (w := w)).Q := ⟨none, c.input.move .right, c.work, c.output⟩
    have hstep : machine.step c = some e := bit_step false c hs (InputCursor.read_bit false hc)
      (fun j => (hc.works j).1) hc.output_read
    exact ⟨e, 1, by omega, .step hstep .zero, rfl, InputCursor.consume false hc, rfl⟩
  | succ v ih =>
    intro before tail emitted c hs hc
    have hc' : Cursor before (true :: (RealSyntax.binderCode v ++ tail)) emitted c.input c.work c.output := by
      simpa only [RealSyntax.binderCode, List.replicate_succ, List.cons_append] using hc
    let c₁ : Cfg w (machine (w := w)).Q := ⟨some false, c.input.move .right, c.work, c.output⟩
    have hstep : machine.step c = some c₁ := bit_step true c hs (InputCursor.read_bit true hc')
      (fun j => (hc.works j).1) hc.output_read
    obtain ⟨e, t, ht, hreach, hhalt, hecur, hework⟩ :=
      ih (before ++ [true]) tail emitted c₁ rfl (InputCursor.consume true hc')
    refine ⟨e, t + 1, by omega, .step hstep hreach, hhalt, ?_, hework⟩
    simpa only [RealSyntax.binderCode, List.replicate_succ, List.append_assoc, List.cons_append, List.nil_append] using hecur

theorem hoareTime (v : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (RealSyntax.binderCode v ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ RealSyntax.binderCode v) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (v + 1) := by
  rintro inp work out ⟨hc, hs, hr⟩
  obtain ⟨e, t, ht, hreach, hhalt, hecur, hework⟩ :=
    scan v before tail emitted ⟨some false, inp, work, out⟩ rfl hc
  exact ⟨e, t, ht, hreach, hhalt, hecur, by simpa only [hework] using hs, by simpa only [hework] using hr⟩

end JointThermoComplexity.Complexity.HeaderSkip

#print axioms JointThermoComplexity.Complexity.HeaderSkip.hoareTime
