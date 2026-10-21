module
public import proofs.JointThermoComplexity.Complexity.ReactionNaturalSelect

set_option autoImplicit false
@[expose] public section

/-! A common exact-cursor interface for either fixed role in a reaction's two dense natural arrays. -/

namespace JointThermoComplexity.Complexity.ReactionFieldSelect
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState NaturalSelectionCode ReactionCircuit ReactionNaturalSelect

variable {w n : ℕ}

def value (q : Reaction n) (s : Fin n) (product : Bool) : ℕ := if product then q.product s else q.reactant s

def taken (q : Reaction n) (s : Fin n) (product : Bool) (before : List Bool) : List Bool :=
  if product then (((before ++ NaturalArraySkip.code q.reactant) ++ leading q.product s) ++ BitCodec.naturalCode (q.product s))
  else ((before ++ leading q.reactant s) ++ BitCodec.naturalCode (q.reactant s))

def remaining (q : Reaction n) (s : Fin n) (product : Bool) (tail : List Bool) : List Bool :=
  if product then trailing q.product s ++ factors q tail
  else trailing q.reactant s ++ NaturalArraySkip.code q.product ++ factors q tail

def machine (idx count position : Fin (w + 1)) (product : Bool) : TM (w + 1) :=
  if product then productMachine idx count position else reactantMachine idx position

theorem hoareTime (idx count position : Fin (w + 1)) (hcount : count ≠ idx) (hposition : position ≠ idx) (product : Bool) (L : ℕ)
    (q : Reaction n) (hq : ReactionSkip.Bounded L q) (s : Fin n)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx count position product).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ IsReg s.val (work position) ∧ IsReg n (work count) ∧ R work)
      (fun inp work out => Cursor (taken q s product before) (remaining q s product tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (value q s product).bits ∧ (work idx).cells 0 = Γ.start ∧
        Reusable L (work idx) ∧ IsReg s.val (work position) ∧ IsReg n (work count) ∧ R work) (productTimeBound L) := by
  cases product
  · have h := reactant_hoareTime idx position hposition L q hq s before tail emitted
      (fun work => IsReg n (work count) ∧ R work) (by
        rintro work work' hw ⟨hn, hr⟩
        exact ⟨by simpa only [hw count hcount] using hn, hR work work' hw hr⟩)
    have hb := h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
      (show NaturalIndexedLoad.timeBound L ≤ productTimeBound L by unfold NaturalIndexedLoad.timeBound productTimeBound; omega)
    simpa only [machine, value, taken, remaining, Bool.false_eq_true, ↓reduceIte] using hb
  · simpa only [machine, value, taken, remaining, ↓reduceIte] using
      product_hoareTime idx count position hcount hposition L q hq s before tail emitted R hR

end JointThermoComplexity.Complexity.ReactionFieldSelect

#print axioms JointThermoComplexity.Complexity.ReactionFieldSelect.hoareTime
