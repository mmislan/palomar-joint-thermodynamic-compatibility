module
public import proofs.JointThermoComplexity.Complexity.NaturalMachineRun

set_option autoImplicit false
@[expose] public section

/-! The proved machine's status bit equals canonical codec acceptance. -/

namespace JointThermoComplexity.Complexity.NaturalMachineParser
open _root_.Complexity
open _root_.Complexity.TM
open BitCodec PayloadControl NaturalMachine NaturalMachineRun

def accepted (requirePositive : Bool) (input : List Bool) : Bool :=
  if requirePositive then (FiniteCodec.positive.parse input).isSome else (parseNatural input).isSome

theorem verdict_eq_accepted (requirePositive : Bool) (input : List Bool) :
    verdict requirePositive .empty input = accepted requirePositive input := by
  have h : (verdict requirePositive .empty input = true) ↔ accepted requirePositive input = true := by
    cases requirePositive with
    | false =>
      simpa [accepted, Option.isSome_iff_exists, Prod.exists] using accepts_natural input
    | true =>
      simpa [accepted, Option.isSome_iff_exists, Prod.exists] using accepts_positive input
  cases hv : verdict requirePositive .empty input <;>
    cases ha : accepted requirePositive input <;> simp_all

variable {n : ℕ}

theorem run_parser_from_cursor (requirePositive : Bool) (before emitted remaining : List Bool)
    (c : Cfg (n + 1) (machine requirePositive n).Q) (hs : c.state = .start)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start) (hflag : (c.work (flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hzero : c.output.cells 0 = Γ.start) :
    ∃ c' t, t ≤ remaining.length + 2 ∧
      (machine requirePositive n).reachesIn t c c' ∧ (machine requirePositive n).halted c' ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = before.length + (copied .empty remaining).length + 1 ∧
      (∀ i, i ≠ flagIndex n → c'.work i = c.work i) ∧
      (c'.work (flagIndex n)).head = 1 ∧
      (c'.work (flagIndex n)).read = Γ.ofBool (accepted requirePositive remaining) ∧
      c'.output.cells 0 = Γ.start ∧ c'.output.HasBinaryPrefix (emitted ++ copied .empty remaining) := by
  simpa only [verdict_eq_accepted] using
    run_from_cursor requirePositive before emitted remaining c hs hcells hhead hwork hflag hp hzero

def integerAccepted : List Bool → Bool
  | [] => false
  | sign :: rest => accepted sign rest

theorem integerAccepted_iff (input : List Bool) :
    integerAccepted input = true ↔ ∃ value suffix, parseInteger input = some (value, suffix) := by
  cases input with
  | nil => simp [integerAccepted, parseInteger]
  | cons sign rest =>
    cases sign with
    | false =>
      cases hp : parseNatural rest with
      | none => simp [integerAccepted, accepted, parseInteger, hp]
      | some pair =>
        obtain ⟨value, suffix⟩ := pair
        simp [integerAccepted, accepted, parseInteger, hp]
    | true =>
      cases hp : parseNatural rest with
      | none => simp [integerAccepted, accepted, FiniteCodec.positive, parseInteger, hp]
      | some pair =>
        obtain ⟨value, suffix⟩ := pair
        cases value <;> simp [integerAccepted, accepted, FiniteCodec.positive, parseInteger, hp]

end JointThermoComplexity.Complexity.NaturalMachineParser

#print axioms JointThermoComplexity.Complexity.NaturalMachineParser.run_parser_from_cursor
#print axioms JointThermoComplexity.Complexity.NaturalMachineParser.integerAccepted_iff
