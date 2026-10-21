module
public import proofs.JointThermoComplexity.Complexity.ReactionIndexedAccess
public import proofs.JointThermoComplexity.Complexity.ReactionFieldSelect

set_option autoImplicit false
@[expose] public section

/-! Select an actual reaction and species field from the full table, retaining binary magnitude and all other state. -/

namespace JointThermoComplexity.Complexity.ReactionFieldIndexedLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState ReactionCircuit ReactionSelectionCode

variable {w n r : ℕ}

def machine (idx count reaction species : Fin (w + 1)) (product : Bool) : TM (w + 1) :=
  seqTM (ReactionIndexedAccess.machine count reaction) (ReactionFieldSelect.machine idx count species product)

def timeBound (L : ℕ) : ℕ := 2 * L ^ 3 + 10 * L ^ 2 + 31 * L + 24

theorem hoareTime (idx count reaction species : Fin (w + 1)) (hcr : count ≠ reaction)
    (hcount : count ≠ idx) (hreaction : reaction ≠ idx) (hspecies : species ≠ idx) (product : Bool) (L : ℕ) (hr : r ≤ L)
    (values : Fin r → Reaction n) (i : Fin r) (s : Fin n) (hsize : ∀ j, ReactionSkip.Bounded L (values j))
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx count reaction species product).HoareTime
      (fun inp work out => Cursor before (code values ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work idx) ∧ IsReg i.val (work reaction) ∧ IsReg s.val (work species) ∧ IsReg n (work count) ∧ R work)
      (fun inp work out => Cursor (ReactionFieldSelect.taken (values i) s product (before ++ leading values i))
        (ReactionFieldSelect.remaining (values i) s product (trailing values i ++ tail)) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (ReactionFieldSelect.value (values i) s product).bits ∧
        (work idx).cells 0 = Γ.start ∧ Reusable L (work idx) ∧ IsReg s.val (work species) ∧ IsReg n (work count) ∧
        IsReg i.val (work reaction) ∧ R work) (timeBound L) := by
  let R' : (Fin (w + 1) → Tape) → Prop := fun work => IsReg i.val (work reaction) ∧ R work
  have hR' : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R' work → R' work' := by
    rintro work work' hw ⟨hi, hr⟩
    exact ⟨by simpa only [hw reaction hreaction] using hi, hR work work' hw hr⟩
  have ha := ReactionIndexedAccess.hoareTime count reaction hcr L hr values i hsize before tail emitted
    (fun work _ => (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ IsReg s.val (work species) ∧ R work)
  have hl := ReactionFieldSelect.hoareTime idx count species hcount hspecies product L (values i) (hsize i) s
    (before ++ leading values i) (trailing values i ++ tail) emitted R' hR'
  have hfull := seqTM_hoareTime (ReactionIndexedAccess.machine count reaction) (ReactionFieldSelect.machine idx count species product) ha (by
    rintro inp work out ⟨hc, hi, hn, hs, hb, hsp, hr⟩
    obtain ⟨hinp, hw, ho⟩ := hc.phase
    rw [hinp, hw, ho]
    exact ⟨by simpa only [List.append_assoc] using hc, hs, hb, hsp, hn, hi, hr⟩) hl
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, hb, hi, hsp, hn, hr⟩
    exact ⟨hc, hi, hn, hs, hb, hsp, hr⟩) (fun _ _ _ h => h) (by
      unfold ReactionTableSkip.timeBound ReactionNaturalSelect.productTimeBound timeBound
      omega)

end JointThermoComplexity.Complexity.ReactionFieldIndexedLoad

#print axioms JointThermoComplexity.Complexity.ReactionFieldIndexedLoad.hoareTime
