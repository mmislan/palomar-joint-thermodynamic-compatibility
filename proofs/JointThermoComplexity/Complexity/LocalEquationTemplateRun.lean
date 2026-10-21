module
public import proofs.JointThermoComplexity.Complexity.LocalEquationTemplates

set_option autoImplicit false
@[expose] public section

/-! Ten fixed finite serializers implement the nonleaf/formula rows and root activation. -/

namespace JointThermoComplexity.Complexity.LocalEquationTemplateRun
open _root_.Complexity _root_.Complexity.TM HeaderAt AddressCodeProgram LocalEquationTemplates
variable {w : ℕ}

def program (kind : Kind) : List (Instr 6) := AddressRowProgram.entries (rows kind)

def machine (ports : Fin 6 → Fin w) (scratch : Fin w) (kind : Kind) : TM w :=
  AddressCodeProgram.machine ports scratch (program kind)

def output (kind : Kind) (values : Fin 6 → ℕ) : List Bool := AddressCodeProgram.output values (program kind)

theorem fixed_program_bounds (kind : Kind) : AddressRowProgram.indexCount (program kind) ≤ 16 ∧
    AddressRowProgram.literalBytes (program kind) ≤ 256 ∧ (program kind).length ≤ 256 := by
  cases kind <;> decide

theorem time_bound (kind : Kind) (B : ℕ) : timeBound B (program kind) ≤ 32 * B ^ 2 + 192 * B + 736 := by
  obtain ⟨hi, hb, hl⟩ := fixed_program_bounds kind
  have h2 := Nat.mul_le_mul_right (B ^ 2) (Nat.mul_le_mul_left 2 hi)
  have h12 := Nat.mul_le_mul_right B (Nat.mul_le_mul_left 12 hi)
  rw [AddressRowProgram.program_time_polynomial]
  omega

theorem output_complete (kind : Kind) (values : Fin 6 → ℕ) :
    output kind values ++ [false] = RowWordCodec.rows (wordRows kind values) := by
  have h := AddressRowProgram.rows_output values (rows kind)
  rw [AddressRowProgram.rows_entries, AddressCodeProgram.output_append] at h
  simpa only [output, program, AddressCodeProgram.output, List.flatMap_cons, List.flatMap_nil,
    code, List.append_nil, wordRows] using h

theorem hoareTime (ports : Fin 6 → Fin w) (scratch : Fin w) (hne : ∀ i, ports i ≠ scratch)
    (kind : Kind) (values : Fin 6 → ℕ) (B : ℕ) (hB : ∀ i, values i ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine ports scratch kind).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports scratch values R work)
      (fun inp work out => Cursor before input (emitted ++ output kind values) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports scratch values R work) (32 * B ^ 2 + 192 * B + 736) :=
  (AddressRowProgram.entries_hoareTime ports scratch hne values B hB (rows kind) before input emitted R).mono_bound
    (time_bound kind B)

end JointThermoComplexity.Complexity.LocalEquationTemplateRun

#print axioms JointThermoComplexity.Complexity.LocalEquationTemplateRun.output_complete
#print axioms JointThermoComplexity.Complexity.LocalEquationTemplateRun.hoareTime
