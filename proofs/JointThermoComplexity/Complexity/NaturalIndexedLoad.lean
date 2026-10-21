module
public import proofs.JointThermoComplexity.Complexity.NaturalRawLoad
public import proofs.JointThermoComplexity.Complexity.NaturalArraySkip

set_option autoImplicit false
@[expose] public section

/-! A retained unary field index selects one actual binary natural payload in polynomial time. -/

namespace JointThermoComplexity.Complexity.NaturalIndexedLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState

variable {w : ℕ}

def machine (idx fuel : Fin (w + 1)) : TM (w + 1) :=
  seqTM (NaturalListSkip.machine fuel) (NaturalRawLoad.machine idx)

def timeBound (L : ℕ) : ℕ := L ^ 2 + 18 * L + 18

theorem hoareTime (idx fuel : Fin (w + 1)) (hne : fuel ≠ idx) (L : ℕ)
    (items : List ℕ) (hcount : items.length ≤ L) (value : ℕ)
    (hsize : ∀ x ∈ items, (BitCodec.naturalCode x).length ≤ L) (hlen : (BitCodec.naturalCode value).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx fuel).HoareTime
      (fun inp work out => Cursor before (NaturalListSkip.code items ++ BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ IsReg items.length (work fuel) ∧ R work)
      (fun inp work out => Cursor ((before ++ NaturalListSkip.code items) ++ BitCodec.naturalCode value) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString value.bits ∧ (work idx).cells 0 = Γ.start ∧
        Reusable L (work idx) ∧ IsReg items.length (work fuel) ∧ R work) (timeBound L) := by
  let R' : (Fin (w + 1) → Tape) → Prop := fun work => IsReg items.length (work fuel) ∧ R work
  have hR' : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R' work → R' work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw fuel hne] using hf, hR work work' hw hr⟩
  have hs := NaturalListSkip.hoareTime fuel L items hsize before (BitCodec.naturalCode value ++ tail) emitted
    (fun work _ => (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
  have hl := NaturalRawLoad.hoareTime L idx value hlen (before ++ NaturalListSkip.code items) tail emitted R' hR'
  have hfull := seqTM_hoareTime (NaturalListSkip.machine fuel) (NaturalRawLoad.machine idx) hs (by
    rintro inp work out ⟨hc, hf, hs, hb, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hf, hr⟩) hl
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, hb, hf, hr⟩
    exact ⟨by simpa only [List.append_assoc] using hc, hf, hs, hb, hr⟩) (fun _ _ _ h => h) (by
      unfold NaturalListSkip.timeBound timeBound
      calc items.length * (L + 2) + (items.length + 2) + 1 + (15 * L + 15) ≤
          L * (L + 2) + (L + 2) + 1 + (15 * L + 15) := by
            have hm := Nat.mul_le_mul_right (L + 2) hcount
            omega
           _ = L ^ 2 + 18 * L + 18 := by ring1)

end JointThermoComplexity.Complexity.NaturalIndexedLoad

#print axioms JointThermoComplexity.Complexity.NaturalIndexedLoad.hoareTime
