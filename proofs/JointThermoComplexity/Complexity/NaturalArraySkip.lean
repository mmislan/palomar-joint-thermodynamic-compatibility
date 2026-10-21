module
public import proofs.JointThermoComplexity.Complexity.NaturalListSkip
public import proofs.JointThermoComplexity.Complexity.FiniteCodec
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Traverse a dense natural table in time polynomial in field bit length and count. -/

namespace JointThermoComplexity.Complexity.NaturalArraySkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w n : ℕ}

def code (values : Fin n → ℕ) : List Bool := FiniteCodec.functionCode FiniteCodec.natural values

abbrev machine (fuel : Fin w) : TM w := NaturalListSkip.machine fuel

def timeBound (L : ℕ) : ℕ := L ^ 2 + 3 * L + 2

theorem code_eq (values : Fin n → ℕ) : code values = NaturalListSkip.code (List.ofFn values) :=
  FiniteCodec.functionCode_eq_flatMap FiniteCodec.natural values

theorem hoareTime (fuel : Fin w) (L : ℕ) (hn : n ≤ L) (values : Fin n → ℕ)
    (hsize : ∀ i, (BitCodec.naturalCode (values i)).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine fuel).HoareTime
      (fun inp work out => Cursor before (code values ++ tail) emitted inp work out ∧ IsReg n (work fuel) ∧ R work out)
      (fun inp work out => Cursor (before ++ code values) tail emitted inp work out ∧ IsReg n (work fuel) ∧ R work out)
      (timeBound L) := by
  have hs := NaturalListSkip.hoareTime fuel L (List.ofFn values) (by
    intro value hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact hsize i) before tail emitted R
  exact hs.consequence
    (fun _ _ _ h => by simpa only [← code_eq, List.length_ofFn] using h)
    (fun _ _ _ h => by simpa only [← code_eq, List.length_ofFn] using h) (by
      simp only [NaturalListSkip.timeBound, List.length_ofFn, timeBound]
      calc n * (L + 2) + (n + 2) ≤ L * (L + 2) + (L + 2) :=
            Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.add_le_add_right hn 2)
           _ = L ^ 2 + 3 * L + 2 := by ring1)

end JointThermoComplexity.Complexity.NaturalArraySkip

#print axioms JointThermoComplexity.Complexity.NaturalArraySkip.hoareTime
