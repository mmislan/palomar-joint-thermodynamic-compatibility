module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxCorrect

set_option autoImplicit false
@[expose] public section

/-! Six fixed work tapes for syntax streaming; the outside frame permits a displaced fuel head. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxRegisters
open _root_.Complexity _root_.Complexity.TM HeaderAt

def tags (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩
def pending : Fin 6 := 3
def fuel : Fin 6 := 4
def flag : Fin 6 := 5

theorem tags_injective : Function.Injective tags := by decide
theorem tags_flag : ∀ i, tags i ≠ flag := by decide
theorem tags_pending : ∀ i, tags i ≠ pending := by decide
theorem fuel_tags : ∀ i, fuel ≠ tags i := by decide

def Stable (R : (Fin 6 → Tape) → Prop) : Prop :=
  ∀ work work', work' fuel = work fuel → R work → R work'

structure Ready (count : ℕ) (R : (Fin 6 → Tape) → Prop) (work : Fin 6 → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  markers : ∀ j, (work j).cells 0 = Γ.start
  counter : IsReg count (work pending)
  tagHeads : ∀ i, (work (tags i)).head = 1
  flagHead : (work flag).head = 1
  frame : R work

def Inv (R : (Fin 6 → Tape) → Prop) (s : SmallSyntaxControl.State) : _root_.Complexity.TM.TapePred 6 :=
  fun inp work out => Cursor s.before s.input s.emitted inp work out ∧ Ready s.pending R work

theorem reframe (old count : ℕ) (R : (Fin 6 → Tape) → Prop) (hR : Stable R)
    (work work' : Fin 6 → Tape) (hr : Ready old R work) (hf : work' fuel = work fuel)
    (hs : ∀ j, Parked (work' j)) (hz : ∀ j, (work' j).cells 0 = Γ.start)
    (hp : IsReg count (work' pending)) (ht : ∀ i, (work' (tags i)).head = 1)
    (hflag : (work' flag).head = 1) : Ready count R work' :=
  ⟨hs, hz, hp, ht, hflag, hR work work' hf hr.frame⟩

theorem emit_hoareTime (bits : List Bool) (R : (Fin 6 → Tape) → Prop) (s : SmallSyntaxControl.State) :
    (emitBitsTM (n := 6) bits).HoareTime (Inv R s)
      (Inv R {s with emitted := s.emitted ++ bits}) bits.length := by
  have h := FixedOutput.hoareTime bits s.before s.input s.emitted (Ready s.pending R)
  exact h.consequence (by rintro inp work out ⟨hc, hr⟩; exact ⟨hc, hr.safe, hr⟩)
    (fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl

theorem status_hoareTime (value : Bool) (R : (Fin 6 → Tape) → Prop) (hR : Stable R) (s : SmallSyntaxControl.State) :
    (SourceTermToken.setStatus flag value).HoareTime (Inv R s)
      (fun inp work out => Inv R s inp work out ∧ (work flag).read = Γ.ofBool value) 1 := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin 6 → Tape) → Prop := fun work' => ∀ j, j ≠ flag → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ flag → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨c, t, ht, hd, hh, hc', hs', hfh, hfv, hother⟩ :=
    SourceTermToken.setStatus_hoareTime flag value s.before s.input s.emitted C hC
      inp work out ⟨hc, hr.safe, hr.flagHead, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hp : IsReg s.pending (c.work pending) := by simpa only [hother pending (by decide)] using hr.counter
  have htags : ∀ i, (c.work (tags i)).head = 1 := fun i => by simpa only [hother (tags i) (tags_flag i)] using hr.tagHeads i
  have hr' := reframe s.pending s.pending R hR work c.work hr (hother fuel (by decide)) hs'
    (fun j => (hm.2.1 j).1) hp htags hfh
  exact ⟨c, t, ht, hd, hh, ⟨hc', hr'⟩, hfv⟩

end JointThermoComplexity.Complexity.SmallSyntaxRegisters

#print axioms JointThermoComplexity.Complexity.SmallSyntaxRegisters.status_hoareTime
