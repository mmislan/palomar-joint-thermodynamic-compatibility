module
public import proofs.JointThermoComplexity.Complexity.ReusableIndexEmitter
public import proofs.JointThermoComplexity.Complexity.CountTape

set_option autoImplicit false
@[expose] public section

/-! Fixed serialization programs read runtime address registers and preserve the complete work frame. -/

namespace JointThermoComplexity.Complexity.AddressCodeProgram
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
variable {w k : ℕ}

theorem binary_zero {t : Tape} (h : IsReg 0 t) : Register 0 t := by
  exact ⟨by simpa only [List.replicate_zero, Nat.zero_bits] using CountTape.string_of_register h, h.cell0⟩

theorem unary_zero {t : Tape} (h : Register 0 t) : IsReg 0 t :=
  CountTape.register_of_string (by simpa only [List.replicate_zero, Nat.zero_bits] using h.1) h.2

theorem index_exact (idx scratch : Fin w) (hne : idx ≠ scratch) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (ReusableIndexEmitter.machine idx scratch).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg v (work idx) ∧ IsReg 0 (work scratch) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.naturalCode v) inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ IsReg 0 (work scratch) ∧ R work)
      (ReusableIndexEmitter.timeBound v) := by
  rintro inp work out ⟨hc, hs, hv, hz, hr⟩
  let C : (Fin w → Tape) → Prop := fun work' => ∀ j, j ≠ idx → j ≠ scratch → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ idx → j ≠ scratch → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hh j hj hk
    exact (he j hj hk).trans (hh j hj hk)
  obtain ⟨d, t, ht, hd, hh, hv', hc', hz', hother⟩ :=
    ReusableIndexEmitter.hoareTime idx scratch hne v before input emitted C hC
      inp work out ⟨hv, hc, binary_zero hz, fun _ _ _ => rfl⟩
  have hzero := unary_zero hz'
  have heq : d.work = work := by
    funext j
    by_cases hj : j = idx
    · subst j
      exact hv'.eq_regT.trans hv.eq_regT.symm
    · by_cases hk : j = scratch
      · subst j
        exact hzero.eq_regT.trans hz.eq_regT.symm
      · exact hother j hj hk
  exact ⟨d, t, ht, hd, hh, hc', by simpa only [heq] using hs, hv', hzero, by simpa only [heq] using hr⟩

theorem index_time_mono {v B : ℕ} (hv : v ≤ B) : ReusableIndexEmitter.timeBound v ≤ ReusableIndexEmitter.timeBound B := by
  have hm : v * (2 * v + 6) ≤ B * (2 * B + 6) := Nat.mul_le_mul hv (by omega)
  unfold ReusableIndexEmitter.timeBound
  omega

inductive Instr (k : ℕ) where
  | bits : List Bool → Instr k
  | index : Fin k → Instr k

def code (values : Fin k → ℕ) : Instr k → List Bool
  | .bits bits => bits
  | .index i => BitCodec.naturalCode (values i)

def output (values : Fin k → ℕ) (program : List (Instr k)) : List Bool := program.flatMap (code values)

theorem output_append (values : Fin k → ℕ) (a b : List (Instr k)) :
    output values (a ++ b) = output values a ++ output values b := List.flatMap_append

def atomMachine (ports : Fin k → Fin w) (scratch : Fin w) : Instr k → TM w
  | .bits bits => emitBitsTM bits
  | .index i => ReusableIndexEmitter.machine (ports i) scratch

def atomTime (B : ℕ) : Instr k → ℕ
  | .bits bits => bits.length
  | .index _ => ReusableIndexEmitter.timeBound B

def machine (ports : Fin k → Fin w) (scratch : Fin w) : List (Instr k) → TM w
  | [] => emitBitsTM []
  | i :: rest => seqTM (atomMachine ports scratch i) (machine ports scratch rest)

def timeBound (B : ℕ) : List (Instr k) → ℕ
  | [] => 0
  | i :: rest => atomTime B i + 1 + timeBound B rest

def Ready (ports : Fin k → Fin w) (scratch : Fin w) (values : Fin k → ℕ) (R : (Fin w → Tape) → Prop)
    (work : Fin w → Tape) : Prop :=
  (∀ i, IsReg (values i) (work (ports i))) ∧ IsReg 0 (work scratch) ∧ R work

theorem atom_hoareTime (ports : Fin k → Fin w) (scratch : Fin w) (hne : ∀ i, ports i ≠ scratch)
    (values : Fin k → ℕ) (B : ℕ) (hB : ∀ i, values i ≤ B) (i : Instr k)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (atomMachine ports scratch i).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports scratch values R work)
      (fun inp work out => Cursor before input (emitted ++ code values i) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports scratch values R work) (atomTime B i) := by
  cases i with
  | bits bits => exact FixedOutput.hoareTime bits before input emitted (Ready ports scratch values R)
  | index i =>
    have hi := index_exact (ports i) scratch (hne i) (values i) before input emitted (Ready ports scratch values R)
    exact hi.consequence (fun _ _ _ ⟨hc, hs, hr⟩ => ⟨hc, hs, hr.1 i, hr.2.1, hr⟩)
      (fun _ _ _ ⟨hc, hs, _, _, hr⟩ => ⟨hc, hs, hr⟩) (index_time_mono (hB i))

theorem hoareTime (ports : Fin k → Fin w) (scratch : Fin w) (hne : ∀ i, ports i ≠ scratch)
    (values : Fin k → ℕ) (B : ℕ) (hB : ∀ i, values i ≤ B) (program : List (Instr k))
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine ports scratch program).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ports scratch values R work)
      (fun inp work out => Cursor before input (emitted ++ output values program) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready ports scratch values R work) (timeBound B program) := by
  induction program generalizing emitted with
  | nil => simpa only [machine, timeBound, output, List.flatMap_nil, List.append_nil, List.length_nil] using
      FixedOutput.hoareTime [] before input emitted (Ready ports scratch values R)
  | cons i rest ih =>
    have hi := atom_hoareTime ports scratch hne values B hB i before input emitted R
    have ht := ih (emitted ++ code values i)
    have hs := seqTM_hoareTime (atomMachine ports scratch i) (machine ports scratch rest) hi (by
      rintro inp work out ⟨hc, hw, hr⟩
      obtain ⟨hi, hworks, ho⟩ := hc.phase
      rw [hi, hworks, ho]
      exact ⟨hc, hw, hr⟩) ht
    simpa only [machine, timeBound, output, List.flatMap_cons, List.append_assoc] using hs

end JointThermoComplexity.Complexity.AddressCodeProgram

#print axioms JointThermoComplexity.Complexity.AddressCodeProgram.index_exact
#print axioms JointThermoComplexity.Complexity.AddressCodeProgram.hoareTime
