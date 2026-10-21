module
public import proofs.JointThermoComplexity.Complexity.ReadBitFlagMachine
public import proofs.JointThermoComplexity.Complexity.TapeSafety

set_option autoImplicit false
@[expose] public section

/-! A one-transition framed bit reader, valid at any positive work-flag head. -/

namespace JointThermoComplexity.Complexity.ReadBitFlag
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (flag : Fin w) : TM w := ReadBitFlagMachine.machine flag

theorem hoareTime (flag : Fin w) (bit : Bool) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag → work' j = work j) → R work → R work') :
    (machine flag).HoareTime
      (fun inp work out => Cursor before (bit :: tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ [bit]) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work flag).read = Γ.ofBool bit ∧ R work) 1 := by
  rintro inp work out ⟨hc, hs, hr⟩
  let e : Cfg w (machine flag).Q := ⟨true, inp.move .right, Function.update work flag ((work flag).write (Γ.ofBool bit)), out⟩
  have hstep : (machine flag).step ⟨false, inp, work, out⟩ = some e :=
    ReadBitFlagMachine.bit_step flag bit ⟨false, inp, work, out⟩ rfl (InputCursor.read_bit bit hc)
      (fun j => (hc.works j).1) hc.output_read
  have hreach : (machine flag).reachesIn 1 ⟨false, inp, work, out⟩ e := .step hstep .zero
  have hpos : (work flag).head ≠ 0 := by have h := (hc.works flag).2; omega
  have hread : ((work flag).write (Γ.ofBool bit)).read = Γ.ofBool bit := by
    simp only [Tape.read, Tape.write, hpos, ↓reduceIte, Function.update_self]
  have heSafe : ∀ j, Parked (e.work j) := by
    intro j
    refine ⟨?_, TapeSafety.work_reaches j hreach (hs j).2⟩
    by_cases hj : j = flag
    · subst j
      simpa only [e, Function.update_self, Tape.write_head] using (hc.works flag).2
    · simpa only [e, Function.update_of_ne hj] using (hs j).1
  have hnew : ((work flag).write (Γ.ofBool bit)).read ≠ Γ.start ∧ 1 ≤ ((work flag).write (Γ.ofBool bit)).head :=
    ⟨by rw [hread]; exact Γ.ofBool_ne_start bit, by simpa only [Tape.write_head] using (hc.works flag).2⟩
  have heCur := InputCursor.update_work (InputCursor.consume bit hc) flag ((work flag).write (Γ.ofBool bit)) hnew
  exact ⟨e, 1, le_rfl, hreach, rfl, heCur, heSafe,
    by simpa only [e, Function.update_self] using hread,
    hR work e.work (fun j hj => Function.update_of_ne hj _ _) hr⟩

end JointThermoComplexity.Complexity.ReadBitFlag

#print axioms JointThermoComplexity.Complexity.ReadBitFlag.hoareTime
