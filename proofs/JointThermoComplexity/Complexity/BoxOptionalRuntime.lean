module
public import proofs.JointThermoComplexity.Complexity.BoxState
public import proofs.JointThermoComplexity.Complexity.SomeBoxBuild
public import proofs.JointThermoComplexity.Complexity.InputBranchRun

set_option autoImplicit false
@[expose] public section

/-! The optional-box machine with arbitrary framed metadata, including a restored outer fuel view. -/

namespace JointThermoComplexity.Complexity.BoxOptionalRuntime
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts BoxState NetworkData

def bufferPorts (m : ℕ) : List (Fin (m + 15)) := [next (m + 2), accumulator (m + 2), power (m + 2), saved m]

theorem separate (m : ℕ) : BoxLoad.Separate (next (m + 2)) (accumulator (m + 2)) (power (m + 2)) (saved m) :=
  ⟨next_ne_accumulator (m + 2), next_ne_power (m + 2), (saved_ne_next m).symm,
    accumulator_ne_power (m + 2), (saved_ne_accumulator m).symm, (saved_ne_power m).symm⟩

theorem source_separate (m : ℕ) : ∀ j ∈ bufferPorts m, species (m + 1) ≠ j := by
  have hsave : species (m + 1) ≠ saved m := by
    intro h; have hv := congrArg Fin.val h; change (7 : ℕ) = 8 at hv; omega
  simp [bufferPorts, species_ne_next (m + 1), species_ne_accumulator (m + 1), species_ne_power (m + 1), hsave]

theorem scratch_separate (m : ℕ) : ∀ j ∈ bufferPorts m, scratch (m + 2) ≠ j := by
  simp [bufferPorts, (next_ne_scratch (m + 2)).symm, (accumulator_ne_scratch (m + 2)).symm,
    (power_ne_scratch (m + 2)).symm, (saved_ne_scratch m).symm]

def Bounded (L : ℕ) : Option ClosedBox → Prop
  | none => True
  | some b => (BitCodec.integerCode b.lower.numerator).length ≤ L ∧
      (BitCodec.naturalCode b.lower.denominator).length ≤ L ∧
      (BitCodec.integerCode b.upper.numerator).length ≤ L ∧
      (BitCodec.naturalCode b.upper.denominator).length ≤ L

def presentMachine (m : ℕ) : TM (m + 15) :=
  SomeBoxBuild.machine (scratch (m + 2)) (next (m + 2)) (accumulator (m + 2)) (power (m + 2)) (saved m) (species (m + 1))

def machine (m : ℕ) : TM (m + 15) := InputBranch.machine (presentMachine m) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := SomeBoxBuild.timeBound L + 2

theorem hoareTime {arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (box : Option ClosedBox)
    (hsize : Bounded L box) (idx : Fin arity) (before tail emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((FiniteCodec.optional DataCodec.box).code box ++ tail) emitted inp work out ∧
        Ready m L idx.val R work)
      (fun inp work out => Cursor (before ++ (FiniteCodec.optional DataCodec.box).code box) tail
        (emitted ++ (NetworkFormula.boxFormula box idx).code) inp work out ∧ Ready m L idx.val R work)
      (timeBound L) := by
  cases box with
  | none =>
    have hn := FixedOutput.hoareTime [false, false, false] (before ++ [false]) tail emitted (Ready m L idx.val R)
    have hn' : (emitBitsTM (n := m + 15) [false, false, false]).HoareTime
        (fun inp work out => Cursor (before ++ [false]) tail emitted inp work out ∧ Ready m L idx.val R work)
        (fun inp work out => Cursor (before ++ [false]) tail (emitted ++ [false, false, false]) inp work out ∧
          Ready m L idx.val R work) 3 :=
      hn.consequence (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.1, hr⟩) (fun _ _ _ ⟨hc, _, hr⟩ => ⟨hc, hr⟩) le_rfl
    have hs := InputBranchRun.no_hoareTime (presentMachine m) (emitBitsTM [false, false, false]) before tail emitted (before ++ [false]) tail
      (emitted ++ [false, false, false]) (Ready m L idx.val R) (Ready m L idx.val R) 3 hn'
    exact hs.consequence (by
      intro inp work out hp
      simpa only [FiniteCodec.optional, List.singleton_append] using hp) (by
        intro inp work out hp
        simpa only [FiniteCodec.optional, NetworkFormula.boxFormula, RealSyntax.Formula.code] using hp)
      (by unfold timeBound SomeBoxBuild.timeBound; omega)
  | some b =>
    obtain ⟨hln, hld, hhn, hhd⟩ := hsize
    have hi : idx.val ≤ 4 * L := by have h := idx.isLt; omega
    have hy := SomeBoxBuild.hoareTime L (scratch (m + 2)) (next (m + 2)) (accumulator (m + 2)) (power (m + 2))
      (saved m) (species (m + 1)) (separate m) (species_ne_scratch (m + 1)) (source_separate m) (scratch_separate m)
      b idx hi hln hld hhn hhd (before ++ [true]) tail emitted R
      (fun work work' hw hr => hR work work' (fun j hj hk hl hm _ => hw j hj hk hl hm) hr)
    have hy' : (SomeBoxBuild.machine (scratch (m + 2)) (next (m + 2)) (accumulator (m + 2)) (power (m + 2))
        (saved m) (species (m + 1))).HoareTime
        (fun inp work out => Cursor (before ++ [true]) (DataCodec.box.code b ++ tail) emitted inp work out ∧ Ready m L idx.val R work)
        (fun inp work out => Cursor ((before ++ [true]) ++ DataCodec.box.code b) tail
          (emitted ++ (NetworkFormula.boxFormula (some b) idx).code) inp work out ∧ Ready m L idx.val R work)
        (SomeBoxBuild.timeBound L) := hy.consequence (by
          rintro inp work out ⟨hc, hs, hz, hi, ⟨hln, hld, hhn, hhd⟩, hr⟩
          exact ⟨hc, hs, hln, hld, hhn, hhd, hi, hz, hr⟩) (by
            rintro inp work out ⟨hc, hs, hln, hld, hhn, hhd, hi, hz, hr⟩
            exact ⟨hc, hs, hz, hi, ⟨hln, hld, hhn, hhd⟩, hr⟩) le_rfl
    have hs := InputBranchRun.yes_hoareTime (presentMachine m) (emitBitsTM [false, false, false]) before (DataCodec.box.code b ++ tail) emitted
      ((before ++ [true]) ++ DataCodec.box.code b) tail (emitted ++ (NetworkFormula.boxFormula (some b) idx).code)
      (Ready m L idx.val R) (Ready m L idx.val R) (SomeBoxBuild.timeBound L) hy'
    exact hs.consequence (by
      intro inp work out hp
      simpa only [FiniteCodec.optional, List.cons_append] using hp) (by
        intro inp work out hp
        simpa only [FiniteCodec.optional, List.append_assoc, List.singleton_append] using hp)
      (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.BoxOptionalRuntime

#print axioms JointThermoComplexity.Complexity.BoxOptionalRuntime.hoareTime
