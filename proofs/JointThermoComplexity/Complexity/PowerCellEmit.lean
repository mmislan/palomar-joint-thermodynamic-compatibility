module
public import proofs.JointThermoComplexity.Complexity.PowerCellCompare
public import proofs.JointThermoComplexity.Complexity.PowerCellWord

set_option autoImplicit false
@[expose] public section

/-! Actual retained comparisons followed by the exact finite weighted-power word. -/

namespace JointThermoComplexity.Complexity.PowerCellEmit
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def items (ps : List (Ports w)) (weights : Ports w → ℕ) : List (PowerCellWord.Item (w + 1)) :=
  ps.map (fun p => (p.flag, weights p))

def machine (ps : List (Ports w)) (weights : Ports w → ℕ) : TM (w + 1) :=
  seqTM (PowerCellCompare.machine ps) (PowerCellWord.machine (items ps weights) 0)

theorem flags (ps : List (Ports w)) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (matched : Fin (w + 1) → Bool)
    (hmatch : ∀ p ∈ ps, matched p.flag = decide (values p.operand = values p.constant))
    (work : Fin (w + 1) → Tape) (hf : PowerCellCompare.Flags ps values work) :
    PowerCellWord.Flags (items ps weights) matched work := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hv := hf p hp
  rw [hmatch p hp]
  by_cases he : values p.operand = values p.constant <;> simpa [he] using hv

theorem score_eq_sum (xs : List (PowerCellWord.Item (w + 1))) (matched : Fin (w + 1) → Bool) (acc : ℕ) :
    PowerCellWord.score xs matched acc = acc + (xs.map (fun p => if matched p.1 then p.2 else 0)).sum := by
  induction xs generalizing acc with
  | nil => simp [PowerCellWord.score]
  | cons p rest ih =>
    cases h : matched p.1 <;> simp [PowerCellWord.score, h, ih, Nat.add_assoc]

theorem score_eq_reference_power (ps : List (Ports w)) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (matched : Fin (w + 1) → Bool)
    (hmatch : ∀ p ∈ ps, matched p.flag = decide (values p.operand = values p.constant)) :
    PowerCellWord.score (items ps weights) matched 0 =
      (ps.map (fun p => if values p.operand = values p.constant then weights p else 0)).sum := by
  rw [score_eq_sum, Nat.zero_add]
  congr 1
  simp only [items, List.map_map]
  apply List.map_congr_left
  intro p hp
  change (if matched p.flag then weights p else 0) = _
  rw [hmatch p hp]
  simp only [decide_eq_true_eq]

theorem hoareTime (ps : List (Ports w)) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (matched : Fin (w + 1) → Bool) (B : ℕ)
    (hsep : PowerCellCompare.Separated ps) (hu : PowerCellCompare.Unique ps)
    (hbits : ∀ p ∈ ps, (values p.operand).bits.length ≤ B ∧ (values p.constant).bits.length ≤ B)
    (hmatch : ∀ p ∈ ps, matched p.flag = decide (values p.operand = values p.constant))
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : PowerCellCompare.Stable ps R) :
    (machine ps weights).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ R work)
      (fun inp work out => Cursor before input
        (emitted ++ BitCodec.naturalCode (PowerCellWord.score (items ps weights) matched 0)) inp work out ∧
        (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ PowerCellCompare.Flags ps values work ∧ R work)
      (ps.length * (24 * B + 22) + 1 + PowerCellWord.bound (items ps weights) 0) := by
  let F : (Fin (w + 1) → Tape) → Prop := fun work =>
    PowerCellCompare.Ready ps values work ∧ PowerCellCompare.Flags ps values work ∧ R work
  have h1 := PowerCellCompare.hoareTime ps values B hsep hu hbits before input emitted R hR
  have h2 := PowerCellWord.hoareTime (items ps weights) matched 0 before input emitted F
  have hh := seqTM_hoareTime _ _ h1 (by
    rintro inp work out ⟨hc, hs, hr, hf, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, flags ps weights values matched hmatch work hf, hr, hf, hx⟩) h2
  apply hh.consequence
  · intro inp work out hp
    exact hp
  · rintro inp work out ⟨hc, hs, _, hr, hf, hx⟩
    exact ⟨hc, hs, hr, hf, hx⟩
  · exact le_rfl

theorem degree_four_hoareTime (ps : List (Ports w)) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (matched : Fin (w + 1) → Bool) (B : ℕ)
    (hsep : PowerCellCompare.Separated ps) (hu : PowerCellCompare.Unique ps)
    (hbits : ∀ p ∈ ps, (values p.operand).bits.length ≤ B ∧ (values p.constant).bits.length ≤ B)
    (hmatch : ∀ p ∈ ps, matched p.flag = decide (values p.operand = values p.constant))
    (hcount : ps.length ≤ 4) (hweight : PowerCellWord.weight (items ps weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : PowerCellCompare.Stable ps R) :
    (machine ps weights).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ R work)
      (fun inp work out => Cursor before input
        (emitted ++ BitCodec.naturalCode (PowerCellWord.score (items ps weights) matched 0)) inp work out ∧
        (∀ j, Parked (work j)) ∧ PowerCellCompare.Ready ps values work ∧ PowerCellCompare.Flags ps values work ∧ R work)
      (4 * (24 * B + 22) + 18) :=
  (hoareTime ps weights values matched B hsep hu hbits hmatch before input emitted R hR).mono_bound (by
    have hb : PowerCellWord.bound (items ps weights) 0 ≤ 17 := by
      have hlen : (items ps weights).length ≤ 4 := by simpa only [items, List.length_map] using hcount
      unfold PowerCellWord.bound
      omega
    have hn := Nat.mul_le_mul_right (24 * B + 22) hcount
    omega)

end JointThermoComplexity.Complexity.PowerCellEmit

#print axioms JointThermoComplexity.Complexity.PowerCellEmit.hoareTime
#print axioms JointThermoComplexity.Complexity.PowerCellEmit.degree_four_hoareTime
#print axioms JointThermoComplexity.Complexity.PowerCellEmit.score_eq_sum
#print axioms JointThermoComplexity.Complexity.PowerCellEmit.score_eq_reference_power
