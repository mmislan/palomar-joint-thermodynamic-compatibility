module
public import proofs.JointThermoComplexity.Complexity.IntegerMachineRun
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Exact numeric suffixes, including malformed structural payloads. -/

namespace JointThermoComplexity.Complexity.NumericCursor
open _root_.Complexity
open _root_.Complexity.TM
open PayloadControl HeaderAt

def payloadRest : ReadState → List Bool → List Bool
  | _, [] => []
  | p, bit :: rest =>
    match next p bit with
    | none => rest
    | some q => payloadRest q rest

def naturalRest (input : List Bool) : List Bool := payloadRest .empty input

def integerRest : List Bool → List Bool
  | [] => []
  | _ :: rest => naturalRest rest

theorem payload_split (input : List Bool) : ∀ p, copied p input ++ payloadRest p input = input := by
  induction input with
  | nil => intro p; rfl
  | cons bit rest ih =>
    intro p
    cases hn : next p bit with
    | none => simp only [copied, payloadRest, hn, List.singleton_append]
    | some q => simpa only [copied, payloadRest, hn, List.cons_append, List.cons.injEq, true_and] using ih q

theorem natural_split (input : List Bool) : copied .empty input ++ naturalRest input = input := payload_split input .empty

theorem integer_split (input : List Bool) : IntegerMachineRun.copied input ++ integerRest input = input := by
  cases input with
  | nil => rfl
  | cons sign rest =>
    simpa only [IntegerMachineRun.copied, integerRest, List.cons_append, List.cons.injEq, true_and] using natural_split rest

theorem natural_copied_code (a : ℕ) (tail : List Bool) :
    copied .empty (BitCodec.naturalCode a ++ tail) = BitCodec.naturalCode a := by
  simpa only [BitCodec.naturalCode, PayloadControl.flag] using copied_encoded [] a.bits tail

theorem natural_rest_code (a : ℕ) (tail : List Bool) : naturalRest (BitCodec.naturalCode a ++ tail) = tail := by
  have hs := natural_split (BitCodec.naturalCode a ++ tail)
  rw [natural_copied_code] at hs
  exact List.append_cancel_left hs

theorem natural_parsed {input tail : List Bool} {a : ℕ}
    (h : BitCodec.parseNatural input = some (a, tail)) :
    copied .empty input = BitCodec.naturalCode a ∧ naturalRest input = tail := by
  rw [BitCodec.parseNatural_sound h]
  exact ⟨natural_copied_code a tail, natural_rest_code a tail⟩

theorem positive_parsed {input tail : List Bool} {a : {k : ℕ // 0 < k}}
    (h : FiniteCodec.positive.parse input = some (a, tail)) :
    copied .empty input = BitCodec.naturalCode a.val ∧ naturalRest input = tail := by
  rw [FiniteCodec.positive.sound h]
  exact ⟨natural_copied_code a.val tail, natural_rest_code a.val tail⟩

theorem integer_copied_code (a : ℤ) (tail : List Bool) :
    IntegerMachineRun.copied (BitCodec.integerCode a ++ tail) = BitCodec.integerCode a := by
  cases a <;> simp only [BitCodec.integerCode, List.cons_append, IntegerMachineRun.copied, natural_copied_code]

theorem integer_rest_code (a : ℤ) (tail : List Bool) : integerRest (BitCodec.integerCode a ++ tail) = tail := by
  cases a <;> simp only [BitCodec.integerCode, List.cons_append, integerRest, natural_rest_code]

theorem integer_parsed {input tail : List Bool} {a : ℤ}
    (h : BitCodec.parseInteger input = some (a, tail)) :
    IntegerMachineRun.copied input = BitCodec.integerCode a ∧ integerRest input = tail := by
  rw [BitCodec.parseInteger_sound h]
  exact ⟨integer_copied_code a tail, integer_rest_code a tail⟩

theorem advance {m : ℕ} {before input emitted taken rest : List Bool}
    {inp out inp' out' : Tape} {work work' : Fin m → Tape}
    (hc : Cursor before input emitted inp work out) (hsplit : taken ++ rest = input)
    (hcells : inp'.cells = inp.cells) (hhead : inp'.head = before.length + taken.length + 1)
    (hwork : ∀ j, (work' j).read ≠ Γ.start ∧ 1 ≤ (work' j).head)
    (hp : out'.HasBinaryPrefix (emitted ++ taken)) (hz : out'.cells 0 = Γ.start) :
    Cursor (before ++ taken) rest (emitted ++ taken) inp' work' out' := by
  refine ⟨?_, ?_, hwork, hp, hz⟩
  · simpa only [List.append_assoc, hsplit] using hcells.trans hc.cells
  · simpa only [List.length_append] using hhead

end JointThermoComplexity.Complexity.NumericCursor

#print axioms JointThermoComplexity.Complexity.NumericCursor.natural_parsed
#print axioms JointThermoComplexity.Complexity.NumericCursor.positive_parsed
#print axioms JointThermoComplexity.Complexity.NumericCursor.integer_parsed
