module
public import proofs.JointThermoComplexity.Complexity.NaturalArraySkip
public import proofs.JointThermoComplexity.Complexity.ReadOnlyFrame

set_option autoImplicit false
@[expose] public section

/-! Dense natural-table traversal under an independent outer physical loop head. -/

namespace JointThermoComplexity.Complexity.NaturalArrayFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w n : ℕ}

theorem hoareTime (outer inner : Fin w) (hne : inner ≠ outer) (v head : ℕ) (hh : 1 ≤ head)
    (L : ℕ) (hn : n ≤ L) (values : Fin n → ℕ)
    (hsize : ∀ i, (BitCodec.naturalCode (values i)).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (NaturalArraySkip.machine inner).HoareTime
      (Frame outer v head (fun inp work out => Cursor before (NaturalArraySkip.code values ++ tail) emitted inp work out ∧
        IsReg n (work inner) ∧ R work out))
      (Frame outer v head (fun inp work out => Cursor (before ++ NaturalArraySkip.code values) tail emitted inp work out ∧
        IsReg n (work inner) ∧ R work out))
      (NaturalArraySkip.timeBound L) :=
  ReadOnlyFrame.hoareTime (NaturalArraySkip.machine inner) outer v head hh
    (NaturalArraySkip.code values) before tail emitted (fun work => IsReg n (work inner))
    (NaturalArraySkip.timeBound L) (by intro work work' he hp; simpa only [he inner hne] using hp)
    (fun S => NaturalArraySkip.hoareTime inner L hn values hsize before tail emitted S) R

end JointThermoComplexity.Complexity.NaturalArrayFrame

#print axioms JointThermoComplexity.Complexity.NaturalArrayFrame.hoareTime
