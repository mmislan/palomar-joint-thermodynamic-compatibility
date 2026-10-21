module
public import proofs.JointThermoComplexity.Complexity.OffsetContribution
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! A finite template program sums the exact row weights in order. Its row
list is compiled before input; the source coefficient is retained throughout. -/

namespace JointThermoComplexity.Complexity.OffsetTemplateProgram
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)
open OffsetContribution (Empty Separate Stable)
variable {w : ℕ}

abbrev Row := ℤ × ℕ

def Bounded (rows : List Row) : Prop := ∀ row ∈ rows, row.1.natAbs ≤ 81 ∧ row.2 ≤ 4

def total (negative : Bool) (v : ℕ) : List Row → ℕ
  | [] => 0
  | row :: rows => OffsetWeightControl.weight negative v row.1 row.2 + total negative v rows

def machine : List Row → Fin w → Fin w → Fin w → Fin w → Fin w → TM (w + 1)
  | [], _, _, _, _, _ => emitBitsTM []
  | row :: rows, idx, sign, adjusted, acc, aux =>
    seqTM (OffsetContribution.machine row.1 row.2 idx sign adjusted acc aux)
      (machine rows idx sign adjusted acc aux)

def Fields (idx sign adjusted acc aux : Fin w) (v A : ℕ) (negative : Bool)
    (R : (Fin w → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  Register v (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool negative ∧
    (work adjusted.castSucc).head = 1 ∧ Register A (work acc.castSucc) ∧
    Empty (work aux.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work)

def Inv (idx sign adjusted acc aux : Fin w) (v A : ℕ) (negative : Bool)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    Fields idx sign adjusted acc aux v A negative R work

def bound (N B C : ℕ) : ℕ := N * (13 * (C + N * (B + 2609)) + 54 * B + 138381)

theorem row_bits (row : Row) (negative : Bool) (v : ℕ) (ht : row.1.natAbs ≤ 81) (hd : row.2 ≤ 4) :
    (OffsetWeightControl.weight negative v row.1 row.2).bits.length ≤ v.bits.length + 2608 := by
  have hs := OffsetWeightControl.static_bounds row.1 row.2 ht hd
  have hb := OffsetWeightControl.bits_weight negative v row.1 row.2
  omega

theorem bits_result (rows : List Row) (negative : Bool) (v A : ℕ) (hrows : Bounded rows) :
    (A + total negative v rows).bits.length ≤ A.bits.length + rows.length * (v.bits.length + 2609) := by
  induction rows generalizing A with
  | nil => simp [total]
  | cons row rows ih =>
    have hh := hrows row List.mem_cons_self
    have ht : Bounded rows := fun a ha => hrows a (List.mem_cons_of_mem row ha)
    have hrow := row_bits row negative v hh.1 hh.2
    have hsum := BinaryAddBuffer.sum_bits_length A (OffsetWeightControl.weight negative v row.1 row.2)
    have hi := ih (A + OffsetWeightControl.weight negative v row.1 row.2) ht
    simp only [total, ← Nat.add_assoc, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem hoareTime (rows : List Row) (negative : Bool) (v A C : ℕ)
    (idx sign adjusted acc aux : Fin w) (sep : Separate idx sign adjusted acc aux)
    (hrows : Bounded rows) (hA : A.bits.length ≤ C) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable adjusted acc aux R) :
    (machine rows idx sign adjusted acc aux).HoareTime
      (Inv idx sign adjusted acc aux v A negative before input emitted R)
      (Inv idx sign adjusted acc aux v (A + total negative v rows) negative before input emitted R)
      (bound rows.length v.bits.length C) := by
  induction rows generalizing A C with
  | nil =>
    have h := FixedOutput.hoareTime [] before input emitted (Fields idx sign adjusted acc aux v A negative R)
    apply h.consequence (fun _ _ _ hp => hp)
    · intro inp work out hp
      simpa only [Inv, total, List.append_nil, Nat.add_zero] using hp
    · simp [bound]
  | cons row rows ih =>
    have hh := hrows row List.mem_cons_self
    have htail : Bounded rows := fun a ha => hrows a (List.mem_cons_of_mem row ha)
    let q := OffsetWeightControl.weight negative v row.1 row.2
    let S := v.bits.length + 2609
    have hq : q.bits.length ≤ v.bits.length + 2608 := row_bits row negative v hh.1 hh.2
    have hnext : (A + q).bits.length ≤ C + S := by
      have h := BinaryAddBuffer.sum_bits_length A q
      dsimp only [S]
      omega
    have hc := OffsetContribution.hoareTime row.1 row.2 v A negative idx sign adjusted acc aux sep hh.1 hh.2
      before input emitted R hR
    have hc' : (OffsetContribution.machine row.1 row.2 idx sign adjusted acc aux).HoareTime
        (Inv idx sign adjusted acc aux v A negative before input emitted R)
        (Inv idx sign adjusted acc aux v (A + q) negative before input emitted R)
        (13 * A.bits.length + 54 * v.bits.length + 138380) := hc.consequence
      (fun _ _ _ hp => hp) (by
        rintro inp work out ⟨hc, hs, hv, hn, hh, _hread, ha, hu, hlast, hx⟩
        exact ⟨hc, hs, hv, hn, hh, ha, hu, hlast, hx⟩) le_rfl
    have hi := ih (A + q) (C + S) htail hnext
    have hf := seqTM_hoareTime _ _ hc' (by
      intro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) hi
    apply hf.consequence (fun _ _ _ hp => hp)
    · intro inp work out hp
      simpa only [Inv, total, q, Nat.add_assoc] using hp
    · have he : C + S + rows.length * (v.bits.length + 2609) =
          C + (rows.length + 1) * (v.bits.length + 2609) := by dsimp only [S]; ring
      simp only [bound, List.length_cons]
      rw [he]
      let F := 13 * (C + (rows.length + 1) * (v.bits.length + 2609)) + 54 * v.bits.length + 138381
      have hh : 13 * A.bits.length + 54 * v.bits.length + 138380 + 1 ≤ F := by dsimp only [F]; omega
      calc
        _ ≤ F + rows.length * F := Nat.add_le_add_right hh _
        _ = _ := by ring

end JointThermoComplexity.Complexity.OffsetTemplateProgram

#print axioms JointThermoComplexity.Complexity.OffsetTemplateProgram.machine
#print axioms JointThermoComplexity.Complexity.OffsetTemplateProgram.bits_result
#print axioms JointThermoComplexity.Complexity.OffsetTemplateProgram.hoareTime
