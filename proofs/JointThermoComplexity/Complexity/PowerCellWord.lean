module
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryControl
public import proofs.JointThermoComplexity.Complexity.WorkSymbolBranch

set_option autoImplicit false
@[expose] public section

/-! A finite read-only flag tree emits the exact catalyst-power natural code. -/

namespace JointThermoComplexity.Complexity.PowerCellWord
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)
variable {w : ℕ}

abbrev Item (w : ℕ) := Fin w × ℕ

def weight : List (Item w) → ℕ
  | [] => 0
  | p :: rest => p.2 + weight rest

def score : List (Item w) → (Fin w → Bool) → ℕ → ℕ
  | [], _, acc => acc
  | p :: rest, matched, acc => score rest matched (if matched p.1 then acc + p.2 else acc)

def machine : List (Item w) → ℕ → TM w
  | [], acc => emitBitsTM (BitCodec.naturalCode acc)
  | p :: rest, acc => WorkSymbolBranch.machine Γ.zero p.1 (machine rest (acc + p.2)) (machine rest acc)

def Flags (items : List (Item w)) (matched : Fin w → Bool) (work : Fin w → Tape) : Prop :=
  ∀ p ∈ items, (work p.1).read = Γ.ofBool (!(matched p.1))

def Pre (items : List (Item w)) (matched : Fin w → Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Flags items matched work ∧ R work

def bound (items : List (Item w)) (acc : ℕ) : ℕ := 2 * (acc + weight items) + 1 + 2 * items.length

theorem score_le (items : List (Item w)) (matched : Fin w → Bool) (acc : ℕ) :
    score items matched acc ≤ acc + weight items := by
  induction items generalizing acc with
  | nil => exact le_rfl
  | cons p rest ih =>
    cases h : matched p.1
    · simpa only [score, h, Bool.false_eq_true, ↓reduceIte, weight] using (ih acc).trans (by omega)
    · simpa only [score, h, ↓reduceIte, weight, Nat.add_assoc] using ih (acc + p.2)

theorem hoareTime (items : List (Item w)) (matched : Fin w → Bool) (acc : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine items acc).HoareTime (Pre items matched before input emitted R)
      (Pre items matched before input (emitted ++ BitCodec.naturalCode (score items matched acc)) R)
      (bound items acc) := by
  induction items generalizing acc R with
  | nil =>
    have hh := FixedOutput.hoareTime (BitCodec.naturalCode acc) before input emitted
      (fun work => Flags [] matched work ∧ R work)
    exact hh.mono_bound (by
      have hn := BoundedUnaryControl.bits_le acc
      rw [BitCodec.naturalCode_length]
      unfold bound weight
      simp only [List.length_nil]
      omega)
  | cons p rest ih =>
    let P : (Fin w → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Flags (p :: rest) matched work ∧ R work
    have htail (a : ℕ) : (machine rest a).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before input (emitted ++ BitCodec.naturalCode (score rest matched a)) inp work out ∧ P work)
        (bound rest a) := by
      have hh := ih a (fun work => Flags (p :: rest) matched work ∧ R work)
      apply hh.consequence
      · rintro inp work out ⟨hc, hs, hf, hr⟩
        exact ⟨hc, hs, fun q hq => hf q (List.mem_cons_of_mem _ hq), hf, hr⟩
      · rintro inp work out ⟨hc, hs, _, hf, hr⟩
        exact ⟨hc, hs, hf, hr⟩
      · exact le_rfl
    cases h : matched p.1 with
    | true =>
      have hh := WorkSymbolBranch.yes_hoareTime Γ.zero p.1 (machine rest (acc + p.2)) (machine rest acc)
        before input emitted before input (emitted ++ BitCodec.naturalCode (score rest matched (acc + p.2)))
        P P (bound rest (acc + p.2)) (htail (acc + p.2))
      apply hh.consequence
      · rintro inp work out ⟨hc, hs, hf, hr⟩
        refine ⟨⟨hc, hs, hf, hr⟩, ?_⟩
        have hv := hf p List.mem_cons_self
        simpa only [h, Bool.not_true, Γ.ofBool] using hv
      · intro inp work out hp
        simpa only [Pre, score, h, ↓reduceIte] using hp
      · unfold bound
        simp only [weight, List.length_cons]
        omega
    | false =>
      have hh := WorkSymbolBranch.no_hoareTime Γ.zero p.1 (machine rest (acc + p.2)) (machine rest acc)
        before input emitted before input (emitted ++ BitCodec.naturalCode (score rest matched acc))
        P P (bound rest acc) (htail acc)
      apply hh.consequence
      · rintro inp work out ⟨hc, hs, hf, hr⟩
        refine ⟨⟨hc, hs, hf, hr⟩, ?_⟩
        have hv := hf p List.mem_cons_self
        rw [hv]
        simpa only [h, Bool.not_false, Γ.ofBool] using (show Γ.one ≠ Γ.zero from by decide)
      · intro inp work out hp
        simpa only [Pre, score, h, Bool.false_eq_true, ↓reduceIte] using hp
      · unfold bound
        simp only [weight, List.length_cons]
        omega

theorem degree_four_hoareTime (items : List (Item w)) (matched : Fin w → Bool) (acc : ℕ)
    (hweight : acc + weight items ≤ 4) (hcount : items.length ≤ 4)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine items acc).HoareTime (Pre items matched before input emitted R)
      (Pre items matched before input (emitted ++ BitCodec.naturalCode (score items matched acc)) R) 17 :=
  (hoareTime items matched acc before input emitted R).mono_bound (by unfold bound; omega)

end JointThermoComplexity.Complexity.PowerCellWord

#print axioms JointThermoComplexity.Complexity.PowerCellWord.hoareTime
#print axioms JointThermoComplexity.Complexity.PowerCellWord.degree_four_hoareTime
#print axioms JointThermoComplexity.Complexity.PowerCellWord.score_le
