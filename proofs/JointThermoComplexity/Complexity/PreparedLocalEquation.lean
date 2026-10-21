module
public import proofs.JointThermoComplexity.Complexity.LocalAddressSetup
public import proofs.JointThermoComplexity.Complexity.RowEntriesCodec

set_option autoImplicit false
@[expose] public section

/-! One finite machine prepares every child/witness address and emits the selected exact local row entries. -/

namespace JointThermoComplexity.Complexity.PreparedLocalEquation
open _root_.Complexity _root_.Complexity.TM HeaderAt AddressCounterPlacement LocalAddressSetup
open DInstabilityComplexity.MachineConstruction

def scratch : Fin 32 := ⟨29, by decide⟩

def machine (kind : LocalEquationTemplates.Kind) : TM 32 :=
  seqTM LocalAddressSetup.machine (LocalEquationTemplateRun.machine addressPorts scratch kind)

def timeBound (B : ℕ) : ℕ := counterIterTime 10 B + 1 + (32 * (3 * B + 3) ^ 2 + 192 * (3 * B + 3) + 736)

noncomputable def timePolynomial : Polynomial ℕ :=
  counterTimePolynomial 10 + 1 + (32 * (3 * Polynomial.X + 3) ^ 2 + 192 * (3 * Polynomial.X + 3) + 736)

theorem timePolynomial_eval (B : ℕ) : timePolynomial.eval B = timeBound B := by
  simp [timePolynomial, timeBound, counterTimePolynomial_eval]

theorem ports_scratch : ∀ i, addressPorts i ≠ scratch := by decide

theorem scratch_outside : ¬InBlock scratch := by unfold InBlock placeWorkInMiddle; decide

theorem hoareTime (kind : LocalEquationTemplates.Kind) (values : Fin 9 → ℕ) (B : ℕ) (hv : ∀ i, values i ≤ B)
    (before input emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    (machine kind).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Registers values work ∧ IsReg 0 (work scratch) ∧ R work)
      (fun inp work out => Cursor before input
        (emitted ++ RowEntriesCodec.entries (LocalEquationTemplates.wordRows kind (addressValues values))) inp work out ∧
          (∀ j, Parked (work j)) ∧ Registers (prepared values) work ∧ IsReg 0 (work scratch) ∧ R work)
      (timeBound B) := by
  let C : (Fin 32 → Tape) → Prop := fun work => IsReg 0 (work scratch) ∧ R work
  have hC : Stable C := by
    rintro work work' he ⟨hs, hr⟩
    exact ⟨by simpa only [he scratch scratch_outside] using hs, hR work work' he hr⟩
  have hp := LocalAddressSetup.hoareTime values B hv before input emitted C hC
  let D : (Fin 32 → Tape) → Prop := fun work => Registers (prepared values) work ∧ IsReg 0 (work scratch) ∧ R work
  have he := LocalEquationTemplateRun.hoareTime addressPorts scratch ports_scratch kind (addressValues values)
    (3 * B + 3) (fun i => prepared_bound values B hv ⟨i.val, by omega⟩) before input emitted D
  have hseq := seqTM_hoareTime LocalAddressSetup.machine
    (LocalEquationTemplateRun.machine addressPorts scratch kind) hp (by
      rintro inp work out ⟨hc, hs, hr, hz, hframe⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, (fun i => hr ⟨i.val, by omega⟩), hz, hr, hz, hframe⟩) he
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hs, _, _, hr, hz, hframe⟩
    rw [RowEntriesCodec.template_entries] at hc
    exact ⟨hc, hs, hr, hz, hframe⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.PreparedLocalEquation

#print axioms JointThermoComplexity.Complexity.PreparedLocalEquation.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.PreparedLocalEquation.hoareTime
