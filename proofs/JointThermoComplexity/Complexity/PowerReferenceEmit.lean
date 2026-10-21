module
public import proofs.JointThermoComplexity.Complexity.PowerCellEmit

set_option autoImplicit false
@[expose] public section

/-! The power-cell machine has an exact reference-sum endpoint without supplied match flags. -/

namespace JointThermoComplexity.Complexity.PowerReferenceEmit
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def power (ps : List (Ports w)) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) : ℕ :=
  (ps.map (fun p => if values p.operand = values p.constant then weights p else 0)).sum

theorem hoareTime (ps : List (Ports w)) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (B : ℕ)
    (hsep : PowerCellCompare.Separated ps) (hu : PowerCellCompare.Unique ps)
    (hbits : ∀ p ∈ ps, (values p.operand).bits.length ≤ B ∧ (values p.constant).bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : PowerCellCompare.Stable ps R) :
    (PowerCellEmit.machine ps weights).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.naturalCode (power ps weights values)) inp work out ∧
        (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ PowerCellCompare.Flags ps values work ∧ R work)
      (ps.length * (24 * B + 22) + 1 + PowerCellWord.bound (PowerCellEmit.items ps weights) 0) := by
  rintro inp work out ⟨hc, hs, hr, hx⟩
  obtain ⟨c, tc, htc, hcr, hch, hcc, hcs, hcready, hcflags, hcx⟩ :=
    PowerCellCompare.hoareTime ps values B hsep hu hbits before input emitted R hR inp work out ⟨hc, hs, hr, hx⟩
  let matched : Fin (w + 1) → Bool := fun j => decide ((c.work j).read = Γ.zero)
  have hmatch : ∀ p ∈ ps, matched p.flag = decide (values p.operand = values p.constant) := by
    intro p hp
    change decide ((c.work p.flag).read = Γ.zero) = _
    rw [hcflags p hp]
    by_cases he : values p.operand = values p.constant
    · simp [he, Γ.ofBool]
    · have hz : Γ.one ≠ Γ.zero := by decide
      simp [he, Γ.ofBool, hz]
  let F : (Fin (w + 1) → Tape) → Prop := fun next =>
    PowerCellCompare.Ready ps values next ∧ PowerCellCompare.Flags ps values next ∧ R next
  have hf := PowerCellEmit.flags ps weights values matched hmatch c.work hcflags
  obtain ⟨d, td, htd, hdr, hdh, hdc, hds, _, hdready, hdflags, hdx⟩ :=
    PowerCellWord.hoareTime (PowerCellEmit.items ps weights) matched 0 before input emitted F
      c.input c.work c.output ⟨hcc, hcs, hf, hcready, hcflags, hcx⟩
  obtain ⟨hi, hw, ho⟩ := hcc.phase
  have hrr : (PowerCellWord.machine (PowerCellEmit.items ps weights) 0).reachesIn td
      ⟨(PowerCellWord.machine (PowerCellEmit.items ps weights) 0).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, ho]
    exact hdr
  have hreach := seqTM_reachesIn_of_reachesIn (PowerCellCompare.machine ps)
    (PowerCellWord.machine (PowerCellEmit.items ps weights) 0) hcr hch hrr
  refine ⟨phase2Wrap (PowerCellCompare.machine ps) (PowerCellWord.machine (PowerCellEmit.items ps weights) 0) d,
    tc + 1 + td, by omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdh, ?_, hds, hdready, hdflags, hdx⟩
  simpa only [phase2Wrap, PowerCellEmit.score_eq_reference_power ps weights values matched hmatch, power] using hdc

theorem degree_four_hoareTime (ps : List (Ports w)) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (B : ℕ)
    (hsep : PowerCellCompare.Separated ps) (hu : PowerCellCompare.Unique ps)
    (hbits : ∀ p ∈ ps, (values p.operand).bits.length ≤ B ∧ (values p.constant).bits.length ≤ B)
    (hcount : ps.length ≤ 4) (hweight : PowerCellWord.weight (PowerCellEmit.items ps weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : PowerCellCompare.Stable ps R) :
    (PowerCellEmit.machine ps weights).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.naturalCode (power ps weights values)) inp work out ∧
        (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ PowerCellCompare.Flags ps values work ∧ R work)
      (96 * B + 106) :=
  (hoareTime ps weights values B hsep hu hbits before input emitted R hR).mono_bound (by
    have hlen : (PowerCellEmit.items ps weights).length ≤ 4 := by simpa only [PowerCellEmit.items, List.length_map] using hcount
    have hb : PowerCellWord.bound (PowerCellEmit.items ps weights) 0 ≤ 17 := by unfold PowerCellWord.bound; omega
    have hn := Nat.mul_le_mul_right (24 * B + 22) hcount
    omega)

end JointThermoComplexity.Complexity.PowerReferenceEmit

#print axioms JointThermoComplexity.Complexity.PowerReferenceEmit.hoareTime
#print axioms JointThermoComplexity.Complexity.PowerReferenceEmit.degree_four_hoareTime
