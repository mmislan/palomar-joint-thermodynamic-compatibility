module
public import proofs.JointThermoComplexity.Complexity.DimensionMachine
public import proofs.JointThermoComplexity.Complexity.MachineEntry

set_option autoImplicit false
@[expose] public section

/-! Fresh-input execution, retained registers and exact three-header status. -/

namespace JointThermoComplexity.Complexity.DimensionEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (n : ℕ) : TM (n + 4) := MachineEntry.machine (DimensionMachine.machine n)

def consumed (input : List Bool) : List Bool :=
  HeaderControl.copied input ++ HeaderControl.copied (DimensionHeaders.tail₁ input) ++
    HeaderControl.copied (DimensionHeaders.tail₂ input)

def blankRegister : Tape := (Tape.init []).move .right

theorem blank_register : IsReg 0 blankRegister := reg_zero_init_bumped

theorem free_ne_slot (n : ℕ) (i : Fin n) (j : Fin 3) :
    i.castAdd 4 ≠ DimensionMachine.slot n j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, DimensionMachine.slot] at hv
  omega

theorem free_ne_flag (n : ℕ) (i : Fin n) : i.castAdd 4 ≠ DimensionMachine.flag n := by
  intro h
  have hv := congrArg Fin.val h
  simp [DimensionMachine.flag, HeaderMachine.flagIndex, NaturalMachine.flagIndex] at hv
  omega

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ 2 * input.length + 18 ∧
      (machine n).reachesIn t ((machine n).initCfg input) d ∧ (machine n).halted d ∧
      Cursor (consumed input) (DimensionHeaders.tail₃ input) (consumed input) d.input d.work d.output ∧
      IsReg (DimensionHeaders.species input) (d.work (DimensionMachine.slot n 0)) ∧
      IsReg (DimensionHeaders.reactions input) (d.work (DimensionMachine.slot n 1)) ∧
      IsReg (DimensionHeaders.cores input) (d.work (DimensionMachine.slot n 2)) ∧
      (d.work (DimensionMachine.flag n)).head = 1 ∧
      (d.work (DimensionMachine.flag n)).read = Γ.ofBool (DimensionHeaders.accepted input) ∧
      (∀ i : Fin n, d.work (i.castAdd 4) = blankRegister) := by
  let P : (Fin (n + 4) → Tape) → Prop := fun work => ∀ i : Fin n, work (i.castAdd 4) = blankRegister
  have hP : ∀ j work work',
      (∀ i, i ≠ DimensionMachine.slot n j → i ≠ DimensionMachine.flag n → work' i = work i) →
      P work → P work' := by
    intro j work work' h hp i
    exact (h (i.castAdd 4) (free_ne_slot n i j) (free_ne_flag n i)).trans (hp i)
  have hpre : DimensionMachine.Frame [] input [] (fun _ => 0) P
      ((Tape.init (input.map Γ.ofBool)).move .right) (fun _ => blankRegister) blankRegister := by
    refine ⟨⟨?_, rfl, ?_, Tape.init_nil_move_right_hasBinaryPrefix_nil, by simp [blankRegister, Tape.move]⟩,
      fun _ => blank_register, rfl, fun _ => rfl⟩
    · simp [Tape.move]
    · intro i
      exact ⟨blank_register.parked.read_ne_start, blank_register.parked.1⟩
  obtain ⟨d', t, ht, hreach, hhalt, hc, hn, hr, hk, hf, hv, hfree⟩ :=
    DimensionMachine.hoareTime n [] input [] P hP _ _ _ hpre
  have hcursor : Cursor (consumed input) (DimensionHeaders.tail₃ input) (consumed input)
      d'.input d'.work d'.output := by
    simpa [consumed, List.append_assoc] using hc
  have hreach' : (machine n).reachesIn (t + 1) ((machine n).initCfg input)
      (MachineEntry.wrap (DimensionMachine.machine n) d') := by
    apply MachineEntry.reaches (DimensionMachine.machine n) ((machine n).initCfg input) rfl
    exact hreach
  exact ⟨MachineEntry.wrap (DimensionMachine.machine n) d', t + 1, by omega, hreach',
    MachineEntry.body_halted (DimensionMachine.machine n) hhalt, hcursor, hn, hr, hk, hf, hv, hfree⟩

theorem computesInTime (n : ℕ) :
    (machine n).ComputesInTime consumed (fun L => 2 * L + 18) := by
  intro input
  obtain ⟨d, t, ht, hreach, hhalt, hc, _⟩ := run n input
  exact ⟨d, t, ht, hreach, hhalt, hc.tapePrefix.2.1,
    hc.tapePrefix.2.2 _ (Nat.le_refl _)⟩

theorem input_cells_preserved {n : ℕ} {input : List Bool} {inp : Tape}
    {work : Fin (n + 4) → Tape} {out : Tape}
    (h : Cursor (consumed input) (DimensionHeaders.tail₃ input) (consumed input) inp work out) :
    inp.cells = (Tape.init (input.map Γ.ofBool)).cells := by
  simpa only [consumed, DimensionHeaders.prefix_and_suffix] using h.cells

theorem codec_status_iff (input : List Bool) {value : Γ}
    (h : value = Γ.ofBool (DimensionHeaders.accepted input)) :
    value = Γ.one ↔ ∃ n r c tail, DimensionHeaders.parse input = some (n, r, c, tail) := by
  rw [h, DimensionHeaders.accepted_eq_last, ← DimensionHeaders.status_iff_parse]
  cases HeaderControl.valid (DimensionHeaders.tail₂ input) <;> simp [Γ.ofBool]

end JointThermoComplexity.Complexity.DimensionEntry

#print axioms JointThermoComplexity.Complexity.DimensionEntry.run
#print axioms JointThermoComplexity.Complexity.DimensionEntry.computesInTime
#print axioms JointThermoComplexity.Complexity.DimensionEntry.codec_status_iff
