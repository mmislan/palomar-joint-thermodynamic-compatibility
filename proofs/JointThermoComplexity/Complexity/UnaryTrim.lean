module
public import proofs.JointThermoComplexity.Complexity.UnaryTrimMachine
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Framed two-transition removal of the final unary mark, leaving the shorter end cursor. -/

namespace JointThermoComplexity.Complexity.UnaryTrim
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (UnaryTrimMachine.machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate (v + 1) true) ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate v true) ∧ (work idx).cells 0 = Γ.start ∧ R work) 2 := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  have hv : work idx = ⟨v + 2, regCells (v + 1)⟩ := by
    apply Tape.ext
    · simpa only [List.length_replicate, Nat.add_assoc] using hp.1
    · have ht : IsReg (v + 1) (⟨1, (work idx).cells⟩ : Tape) := CountTape.register_of_string ⟨rfl, hp.2⟩ hz
      have he := congrArg (fun t : Tape => t.cells) ht.eq_regT
      change (work idx).cells = regCells (v + 1)
      exact he
  obtain ⟨d, hreach, hhalt, hi, ho, ht, hw⟩ :=
    UnaryTrimMachine.run idx v ⟨some false, inp, work, out⟩ rfl hv hc.input_read (fun j => (hc.works j).1) hc.output_read
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j; rw [ht]; exact parked_regCells (by omega)
    · rw [hw j hj]; exact hs j
  have hprefix : (d.work idx).HasBinaryPrefix (List.replicate v true) := by
    rw [ht]
    exact ⟨by simp only [List.length_replicate], (CountTape.string_of_register (reg_regT v)).2⟩
  exact ⟨d, 2, le_rfl, hreach, hhalt,
    ⟨by simpa only [hi] using hc.cells, by simpa only [hi] using hc.head,
      (fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩),
      by simpa only [ho] using hc.tapePrefix, by simpa only [ho] using hc.zero⟩,
    hsafe, hprefix, by rw [ht]; rfl, hR work d.work hw hr⟩

end JointThermoComplexity.Complexity.UnaryTrim

#print axioms JointThermoComplexity.Complexity.UnaryTrim.hoareTime
