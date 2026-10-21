module
public import proofs.JointThermoComplexity.Complexity.SourceBitReadMachine
public import proofs.JointThermoComplexity.Complexity.TapeSafety

set_option autoImplicit false
@[expose] public section

/-! Total one-step source bit reading with exact data and availability flags.
The input cursor advances only when a bit is present. Formula output is kept. -/

namespace JointThermoComplexity.Complexity.SourceBitRead
open _root_.Complexity _root_.Complexity.TM HeaderAt
open SourceBitReadMachine
variable {w : ℕ}

def value : List Bool → Bool
  | [] => false
  | b :: _ => b

def symbol : List Bool → Γ
  | [] => .blank
  | b :: _ => Γ.ofBool b

theorem read_symbol {before input emitted : List Bool} {inp out : Tape} {work : Fin w → Tape}
    (hc : Cursor before input emitted inp work out) : inp.read = symbol input := by
  cases input with
  | nil =>
    change inp.read = Γ.blank
    simp [Tape.read, hc.head, hc.cells, Tape.init_ofBool_cells_ge before before.length le_rfl]
  | cons b rest => exact InputCursor.read_bit b hc

def machine (data flag : Fin w) : TM w := SourceBitReadMachine.machine data flag

theorem hoareTime (data flag : Fin w) (hne : data ≠ flag) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ data → j ≠ flag → work' j = work j) → R work → R work') :
    (machine data flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work data).head = 1 ∧ (work flag).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BooleanMachine.copied input) (BooleanMachine.suffix input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work data).head = 1 ∧ (work flag).head = 1 ∧
        (work data).read = Γ.ofBool (value input) ∧ (work flag).read = Γ.ofBool (BooleanMachine.accepted input) ∧ R work) 1 := by
  rintro inp work out ⟨hc, hs, hdh, hfh, hr⟩
  have hg : BooleanMachine.isBit inp.read = BooleanMachine.accepted input := by
    rw [read_symbol hc]
    cases input with
    | nil => rfl
    | cons b rest => cases b <;> rfl
  have hb : (ReadBitFlagMachine.asWrite inp.read).toΓ = Γ.ofBool (value input) := by
    rw [read_symbol hc]
    cases input with
    | nil => rfl
    | cons b rest => cases b <;> rfl
  let d : Cfg w (machine data flag).Q := ⟨true,
    inp.move (if BooleanMachine.accepted input then .right else .stay),
    changedWork work data flag (value input) (BooleanMachine.accepted input), out⟩
  have hstep : (machine data flag).step ⟨false, inp, work, out⟩ = some d :=
    SourceBitReadMachine.step data flag hne _ _ ⟨false, inp, work, out⟩ rfl hc.input_read hc.output_read
      (fun j => (hc.works j).1) hg hb
  have hreach : (machine data flag).reachesIn 1 ⟨false, inp, work, out⟩ d := .step hstep .zero
  have hheads (j : Fin w) : (d.work j).head = (work j).head := by
    by_cases hjd : j = data
    · subst j
      simp only [d, changed_data work data flag hne, Tape.write_head]
    · by_cases hjf : j = flag
      · subst j
        simp only [d, changed_flag work data flag hne, Tape.write_head]
      · simp only [d, changed_other work data flag j hjd hjf]
  have hsafe (j : Fin w) : Parked (d.work j) :=
    ⟨by rw [hheads]; exact (hs j).1, TapeSafety.work_reaches j hreach (hs j).2⟩
  have hcur0 : Cursor (before ++ BooleanMachine.copied input) (BooleanMachine.suffix input) emitted d.input work out := by
    cases input with
    | nil => simpa only [d, BooleanMachine.accepted, BooleanMachine.copied, BooleanMachine.suffix,
        Bool.false_eq_true, ↓reduceIte, Tape.move, List.append_nil] using hc
    | cons b rest =>
      simpa only [d, BooleanMachine.accepted, BooleanMachine.copied, BooleanMachine.suffix,
        ↓reduceIte] using InputCursor.consume b hc
  have hcur : Cursor (before ++ BooleanMachine.copied input) (BooleanMachine.suffix input) emitted d.input d.work d.output :=
    ⟨hcur0.cells, hcur0.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩, hcur0.tapePrefix, hcur0.zero⟩
  have hdread : (d.work data).read = Γ.ofBool (value input) := by
    rw [show d.work data = (work data).write (Γ.ofBool (value input)) from changed_data work data flag hne _ _]
    simp only [Tape.read, Tape.write, hdh, Nat.one_ne_zero, ↓reduceIte, Function.update_self]
  have hfread : (d.work flag).read = Γ.ofBool (BooleanMachine.accepted input) := by
    rw [show d.work flag = (work flag).write (Γ.ofBool (BooleanMachine.accepted input)) from changed_flag work data flag hne _ _]
    simp only [Tape.read, Tape.write, hfh, Nat.one_ne_zero, ↓reduceIte, Function.update_self]
  exact ⟨d, 1, le_rfl, hreach, rfl, hcur, hsafe, (hheads data).trans hdh, (hheads flag).trans hfh,
    hdread, hfread, hR work d.work (fun j hjd hjf => changed_other work data flag j hjd hjf _ _) hr⟩

end JointThermoComplexity.Complexity.SourceBitRead

#print axioms JointThermoComplexity.Complexity.SourceBitRead.hoareTime
