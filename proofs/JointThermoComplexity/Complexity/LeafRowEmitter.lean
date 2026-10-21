module
public import proofs.JointThermoComplexity.Complexity.AddressCodeProgram
public import proofs.JointThermoComplexity.Complexity.RowWordCodec
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientRun
public import proofs.JointThermoComplexity.Complexity.NaturalWordCopy

set_option autoImplicit false
@[expose] public section

/-! Leaf rows combine a generated root address with a copied binary variable or signed literal field. -/

namespace JointThermoComplexity.Complexity.LeafRowEmitter
open _root_.Complexity _root_.Complexity.TM HeaderAt AddressCodeProgram

def root : Fin 32 := ⟨19, by decide⟩
def scratch : Fin 32 := ⟨29, by decide⟩
def flag : Fin 32 := ⟨14, by decide⟩

structure Ready (v : ℕ) (R : (Fin 32 → Tape) → Prop) (work : Fin 32 → Tape) : Prop where
  rootReg : IsReg v (work root)
  scratchReg : IsReg 0 (work scratch)
  flagHead : (work flag).head = 1
  markers : ∀ j, (work j).cells 0 = Γ.start
  frame : R work

def header : List Bool := [true, true] ++ BitCodec.integerCode 1 ++ [true]
def middle (isVar : Bool) : List Bool := if isVar then [false, true] ++ BitCodec.integerCode (-1) ++ [true] else [false, true]
def tail : List Bool := [false, false]

def prefixProgram (isVar : Bool) : List (Instr 1) := [.bits header, .index 0, .bits (middle isVar)]
def prefixCode (isVar : Bool) (v : ℕ) : List Bool := header ++ BitCodec.naturalCode v ++ middle isVar

def prefixMachine (isVar : Bool) : TM 32 := AddressCodeProgram.machine (fun _ => root) scratch (prefixProgram isVar)

def fieldMachine (isVar : Bool) : TM 32 :=
  if isVar then NaturalWordCopy.machine (NaturalWordCopy.select (n := 31) flag) else SmallCoefficientMachine.machine true 32

def taken (isVar : Bool) (input : List Bool) : List Bool :=
  if isVar then PayloadControl.copied .empty input else IntegerMachineRun.copied input

def rest (isVar : Bool) (input : List Bool) : List Bool :=
  if isVar then NumericCursor.naturalRest input else NumericCursor.integerRest input

def fieldCode (isVar : Bool) (input : List Bool) : List Bool :=
  if isVar then PayloadControl.copied .empty input else BitCodec.integerCode (-SmallIntegerLookup.value input)

def output (isVar : Bool) (v : ℕ) (input : List Bool) : List Bool := prefixCode isVar v ++ fieldCode isVar input ++ tail

def machine (isVar : Bool) : TM 32 := seqTM (prefixMachine isVar) (seqTM (fieldMachine isVar) (emitBitsTM tail))

theorem split (isVar : Bool) (input : List Bool) : taken isVar input ++ rest isVar input = input := by
  cases isVar with
  | false => exact NumericCursor.integer_split input
  | true => exact NumericCursor.natural_split input

theorem prefix_output (isVar : Bool) (v : ℕ) : AddressCodeProgram.output (fun _ => v) (prefixProgram isVar) = prefixCode isVar v := by
  simp only [prefixProgram, AddressCodeProgram.output, List.flatMap_cons, List.flatMap_nil, code,
    prefixCode, List.append_nil, List.append_assoc]

theorem prefix_bound (isVar : Bool) (B : ℕ) : timeBound B (prefixProgram isVar) ≤ ReusableIndexEmitter.timeBound B + 20 := by
  cases isVar with
  | false =>
    change 7 + 1 + (ReusableIndexEmitter.timeBound B + 1 + (2 + 1 + 0)) ≤ _
    omega
  | true =>
    change 7 + 1 + (ReusableIndexEmitter.timeBound B + 1 + (7 + 1 + 0)) ≤ _
    omega

theorem prefix_hoareTime (isVar : Bool) (v B : ℕ) (hv : v ≤ B) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) :
    (prefixMachine isVar).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready v R work)
      (fun inp work out => Cursor before input (emitted ++ prefixCode isVar v) inp work out ∧
        (∀ j, Parked (work j)) ∧ Ready v R work) (ReusableIndexEmitter.timeBound B + 20) := by
  have h := AddressCodeProgram.hoareTime (fun _ : Fin 1 => root) scratch (fun _ => by decide)
    (fun _ => v) B (fun _ => hv) (prefixProgram isVar) before input emitted (Ready v R)
  rw [prefix_output] at h
  exact h.consequence (fun _ _ _ ⟨hc, hs, hr⟩ => ⟨hc, hs, (fun _ => hr.rootReg), hr.scratchReg, hr⟩)
    (fun _ _ _ ⟨hc, hs, _, _, hr⟩ => ⟨hc, hs, hr⟩) (prefix_bound isVar B)

theorem field_hoareTime (isVar : Bool) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag → work' j = work j) → R work → R work') :
    (fieldMachine isVar).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready v R work)
      (fun inp work out => Cursor (before ++ taken isVar input) (rest isVar input)
        (emitted ++ fieldCode isVar input) inp work out ∧ (∀ j, Parked (work j)) ∧ Ready v R work) (input.length + 9) := by
  cases isVar with
  | false => exact SmallCoefficientRun.hoareTime true before input emitted (Ready v R)
  | true =>
    let C : (Fin 32 → Tape) → Prop := fun work => IsReg v (work root) ∧ IsReg 0 (work scratch) ∧ R work
    have hC : ∀ work work', (∀ j, j ≠ flag → work' j = work j) → C work → C work' := by
      rintro work work' he ⟨hr, hs, hf⟩
      exact ⟨by simpa only [he _ (by decide : root ≠ flag)] using hr,
        by simpa only [he _ (by decide : scratch ≠ flag)] using hs, hR work work' he hf⟩
    have h := NaturalWordCopy.parked_hoareTime (NaturalWordCopy.select (n := 31) flag) before input emitted C
      (by simpa only [NaturalWordCopy.flag_select] using hC)
    simp only [NaturalWordCopy.flag_select] at h
    exact h.consequence
      (fun _ _ _ ⟨hc, hs, hr⟩ => ⟨hc, hs, hr.markers, hr.flagHead, hr.rootReg, hr.scratchReg, hr.frame⟩)
      (fun _ _ _ ⟨hc, hs, hz, hf, _, hr, hscratch, hframe⟩ => ⟨hc, hs, hr, hscratch, hf, hz, hframe⟩) (by omega)

theorem hoareTime (isVar : Bool) (v B : ℕ) (hv : v ≤ B) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag → work' j = work j) → R work → R work') :
    (machine isVar).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready v R work)
      (fun inp work out => Cursor (before ++ taken isVar input) (rest isVar input) (emitted ++ output isVar v input)
        inp work out ∧ (∀ j, Parked (work j)) ∧ Ready v R work)
      (ReusableIndexEmitter.timeBound B + input.length + 40) := by
  have hh := prefix_hoareTime isVar v B hv before input emitted R
  have hf := field_hoareTime isVar v before input (emitted ++ prefixCode isVar v) R hR
  have ht := FixedOutput.hoareTime tail (before ++ taken isVar input) (rest isVar input)
    ((emitted ++ prefixCode isVar v) ++ fieldCode isVar input) (Ready v R)
  have hrest := seqTM_hoareTime (fieldMachine isVar) (emitBitsTM tail) hf (by
    rintro inp work out ⟨hc, hs, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hr⟩) ht
  have hfull := seqTM_hoareTime (prefixMachine isVar) (seqTM (fieldMachine isVar) (emitBitsTM tail)) hh (by
    rintro inp work out ⟨hc, hs, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hr⟩) hrest
  apply hfull.consequence (fun _ _ _ h => h)
  · rintro inp work out h
    simpa only [output, List.append_assoc] using h
  · change ReusableIndexEmitter.timeBound B + 20 + 1 + (input.length + 9 + 1 + 2) ≤ _
    omega

theorem variable_output (v : ℕ) (input : List Bool) : output true v input =
    true :: RowWordCodec.polynomial [(1, [BitCodec.naturalCode v]), (-1, [PayloadControl.copied .empty input])] := by
  simp [output, prefixCode, fieldCode, header, middle, tail, RowWordCodec.polynomial, RowWordCodec.marked,
    RowWordCodec.term, RowWordCodec.monomial, List.append_assoc]

theorem integer_output (v : ℕ) (input : List Bool) : output false v input =
    true :: RowWordCodec.polynomial [(1, [BitCodec.naturalCode v]), (-SmallIntegerLookup.value input, [])] := by
  simp [output, prefixCode, fieldCode, header, middle, tail, RowWordCodec.polynomial, RowWordCodec.marked,
    RowWordCodec.term, RowWordCodec.monomial, List.append_assoc]

end JointThermoComplexity.Complexity.LeafRowEmitter

#print axioms JointThermoComplexity.Complexity.LeafRowEmitter.hoareTime
#print axioms JointThermoComplexity.Complexity.LeafRowEmitter.variable_output
