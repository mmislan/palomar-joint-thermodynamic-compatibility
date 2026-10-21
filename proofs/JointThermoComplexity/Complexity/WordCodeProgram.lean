module
public import proofs.JointThermoComplexity.Complexity.BinaryCoordinateReplay
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! Fixed output programs replay binary word slots and paired coordinates.
All buffers and the complete work frame survive each instruction.
-/

namespace JointThermoComplexity.Complexity.WordCodeProgram
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w k : ℕ}

inductive Instr (k : ℕ) where
  | bits : List Bool → Instr k
  | word : Fin k → Instr k
  | paired : Bool → Fin k → Instr k

def code (values : Fin k → List Bool) : Instr k → List Bool
  | .bits bits => bits
  | .word i => BitCodec.encodeBits (values i)
  | .paired odd i => BinaryCoordinateReplay.pairedCode odd (values i)

def output (values : Fin k → List Bool) (program : List (Instr k)) : List Bool := program.flatMap (code values)

theorem output_append (values : Fin k → List Bool) (a b : List (Instr k)) :
    output values (a ++ b) = output values a ++ output values b := List.flatMap_append

def atomMachine (ports : Fin k → Fin w) : Instr k → TM w
  | .bits bits => emitBitsTM bits
  | .word i => BinaryEmit.machine (ports i)
  | .paired odd i => BinaryCoordinateReplay.machine odd (ports i)

def atomTime (B : ℕ) : Instr k → ℕ
  | .bits bits => bits.length
  | .word _ | .paired _ _ => 3 * B + 12

def machine (ports : Fin k → Fin w) : List (Instr k) → TM w
  | [] => emitBitsTM []
  | i :: rest => seqTM (atomMachine ports i) (machine ports rest)

def timeBound (B : ℕ) : List (Instr k) → ℕ
  | [] => 0
  | i :: rest => atomTime B i + 1 + timeBound B rest

def Ready (ports : Fin k → Fin w) (values : Fin k → List Bool) (R : (Fin w → Tape) → Prop)
    (work : Fin w → Tape) : Prop :=
  (∀ i, (work (ports i)).HasBinaryString (values i) ∧ (work (ports i)).cells 0 = Γ.start) ∧ R work

theorem atom_hoareTime (ports : Fin k → Fin w) (values : Fin k → List Bool) (B : ℕ)
    (hB : ∀ i, (values i).length ≤ B) (i : Instr k) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (atomMachine ports i).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports values R work)
      (fun inp work out => Cursor before input (emitted ++ code values i) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports values R work) (atomTime B i) := by
  cases i with
  | bits bits => exact FixedOutput.hoareTime bits before input emitted (Ready ports values R)
  | word i =>
    have hi := BinaryCoordinateReplay.emit_hoareTime (ports i) (values i) before input emitted (Ready ports values R)
    exact hi.consequence
      (fun _ _ _ ⟨hc, hs, hr⟩ => ⟨hc, hs, (hr.1 i).1, (hr.1 i).2, hr⟩)
      (fun _ _ _ ⟨hc, hs, _, _, hr⟩ => ⟨hc, hs, hr⟩) (by have := hB i; dsimp [atomTime]; omega)
  | paired odd i =>
    have hi := BinaryCoordinateReplay.hoareTime odd (ports i) (values i) before input emitted (Ready ports values R)
    exact hi.consequence
      (fun _ _ _ ⟨hc, hs, hr⟩ => ⟨hc, hs, (hr.1 i).1, (hr.1 i).2, hr⟩)
      (fun _ _ _ ⟨hc, hs, _, _, hr⟩ => ⟨hc, hs, hr⟩) (by have := hB i; dsimp [atomTime]; omega)

theorem hoareTime (ports : Fin k → Fin w) (values : Fin k → List Bool) (B : ℕ)
    (hB : ∀ i, (values i).length ≤ B) (program : List (Instr k))
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine ports program).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports values R work)
      (fun inp work out => Cursor before input (emitted ++ output values program) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports values R work) (timeBound B program) := by
  induction program generalizing emitted with
  | nil => simpa only [machine, timeBound, output, List.flatMap_nil, List.append_nil, List.length_nil] using
      FixedOutput.hoareTime [] before input emitted (Ready ports values R)
  | cons i rest ih =>
    have hi := atom_hoareTime ports values B hB i before input emitted R
    have ht := ih (emitted ++ code values i)
    have hs := seqTM_hoareTime (atomMachine ports i) (machine ports rest) hi (by
      rintro inp work out ⟨hc, hw, hr⟩
      obtain ⟨hi, hworks, ho⟩ := hc.phase
      rw [hi, hworks, ho]
      exact ⟨hc, hw, hr⟩) ht
    simpa only [machine, timeBound, output, List.flatMap_cons, List.append_assoc] using hs

def literalBytes : List (Instr k) → ℕ
  | [] => 0
  | .bits bits :: rest => bits.length + literalBytes rest
  | .word _ :: rest | .paired _ _ :: rest => literalBytes rest

def slotCount : List (Instr k) → ℕ
  | [] => 0
  | .bits _ :: rest => slotCount rest
  | .word _ :: rest | .paired _ _ :: rest => slotCount rest + 1

theorem program_time (B : ℕ) (program : List (Instr k)) :
    timeBound B program = literalBytes program + slotCount program * (3 * B + 12) + program.length := by
  induction program with
  | nil => simp only [timeBound, literalBytes, slotCount, Nat.zero_mul, Nat.zero_add, List.length_nil]
  | cons i rest ih =>
    cases i <;> simp only [timeBound, atomTime, literalBytes, slotCount, List.length_cons, ih]
    · omega
    · rw [Nat.add_mul, Nat.one_mul]; omega
    · rw [Nat.add_mul, Nat.one_mul]; omega

theorem program_time_polynomial (B : ℕ) (program : List (Instr k)) :
    timeBound B program = 3 * slotCount program * B + 12 * slotCount program + literalBytes program + program.length := by
  rw [program_time]
  ring

end JointThermoComplexity.Complexity.WordCodeProgram

#print axioms JointThermoComplexity.Complexity.WordCodeProgram.hoareTime
#print axioms JointThermoComplexity.Complexity.WordCodeProgram.program_time_polynomial
