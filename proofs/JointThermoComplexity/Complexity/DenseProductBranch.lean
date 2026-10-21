module
public import proofs.JointThermoComplexity.Complexity.DenseFixedComplexOriginal
public import proofs.JointThermoComplexity.Complexity.DenseCycleData

set_option autoImplicit false
@[expose] public section

/-! A single fixed flag branch selects gain2 or gain1 from the precompiled product machines. -/

namespace JointThermoComplexity.Complexity.DenseProductBranch
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DenseComplexPorts DenseComplexFrame DenseComplexCore DenseComplexOriginal
variable {N : ℕ}

def FlagFrame (i : Fin (N + 2)) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  (work 43).read = Γ.ofBool (decide (i.val ≠ N + 1)) ∧ R work

theorem flag_stable (i : Fin (N + 2)) (R : (Fin 64 → Tape) → Prop) (hR : Stable true R) :
    Stable true (FlagFrame i R) := by
  rintro work next he ⟨hf, hx⟩
  exact ⟨by rw [he 43 (by unfold Outside target; decide)]; exact hf, hR work next he hx⟩

def ProductEmits (right : Bool) (external : TM 64) (m : ℕ) (hm : m ≤ 4) (sourceValues : Fin 64 → ℕ)
    (n N B : ℕ) (i : Fin (N + 2)) (word : List Bool) (E : ℕ) : Prop :=
  ∀ k, k = RationalLiteralNetwork.gain N i →
    ∀ (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop), Stable true R →
      (DenseComplexCore.machine right true k external).HoareTime
        (Pre true m hm sourceValues n N (vertex true i).val before input emitted R)
        (Pre true m hm sourceValues n N (vertex true i).val before input (emitted ++ word) R)
        (bound right N B k E)

def machine (right : Bool) (external : TM 64) : TM 64 :=
  WorkSymbolBranch.machine Γ.zero (43 : Fin 64)
    (DenseComplexCore.machine right true 2 external) (DenseComplexCore.machine right true 1 external)

def timeBound (right : Bool) (N B E : ℕ) : ℕ := bound right N B 1 E + bound right N B 2 E + 2

theorem hoareTime (right : Bool) (external : TM 64) (m : ℕ) (hm : m ≤ 4) (sourceValues : Fin 64 → ℕ)
    (n N B : ℕ) (i : Fin (N + 2)) (word : List Bool) (E : ℕ)
    (he : ProductEmits right external m hm sourceValues n N B i word E)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable true R) :
    (machine right external).HoareTime
      (Pre true m hm sourceValues n N (vertex true i).val before input emitted (FlagFrame i R))
      (Pre true m hm sourceValues n N (vertex true i).val before input (emitted ++ word) (FlagFrame i R))
      (timeBound right N B E) := by
  let P : (Fin 64 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
    IndicatorVectorUnit.Fields (DenseComplexPorts.comparison true) 0 (vertex true i).val
      (DenseInternalBlocks.Frame (ports true) N (InternalR m hm sourceValues n (FlagFrame i R))) work
  by_cases hi : i.val = N + 1
  · have hk : 2 = RationalLiteralNetwork.gain N i := by simp only [DenseCycleData.gain_eq, hi, ↓reduceIte]
    have hb := he 2 hk before input emitted (FlagFrame i R) (flag_stable i R hR)
    have hh := WorkSymbolBranch.yes_hoareTime Γ.zero (43 : Fin 64)
      (DenseComplexCore.machine right true 2 external) (DenseComplexCore.machine right true 1 external)
      before input emitted before input (emitted ++ word) P P (bound right N B 2 E) (by
        apply hb.consequence
        · exact fun _ _ _ hp => hp
        · exact fun _ _ _ hp => hp
        · exact le_rfl)
    apply hh.consequence
    · rintro inp work out ⟨hc, hs, hidx, ht, hf, hn, hb, hr, ha, hread, hx⟩
      refine ⟨⟨hc, hs, hidx, ht, hf, hn, hb, hr, ha, hread, hx⟩, ?_⟩
      simpa [hi, Γ.ofBool] using hread
    · exact fun _ _ _ hp => hp
    · unfold timeBound
      omega
  · have hk : 1 = RationalLiteralNetwork.gain N i := by simp only [DenseCycleData.gain_eq, hi, ↓reduceIte]
    have hb := he 1 hk before input emitted (FlagFrame i R) (flag_stable i R hR)
    have hh := WorkSymbolBranch.no_hoareTime Γ.zero (43 : Fin 64)
      (DenseComplexCore.machine right true 2 external) (DenseComplexCore.machine right true 1 external)
      before input emitted before input (emitted ++ word) P P (bound right N B 1 E) (by
        apply hb.consequence
        · exact fun _ _ _ hp => hp
        · exact fun _ _ _ hp => hp
        · exact le_rfl)
    apply hh.consequence
    · rintro inp work out ⟨hc, hs, hidx, ht, hf, hn, hb, hr, ha, hread, hx⟩
      refine ⟨⟨hc, hs, hidx, ht, hf, hn, hb, hr, ha, hread, hx⟩, ?_⟩
      have hd : decide (i.val ≠ N + 1) = true := by simpa only [decide_eq_true_eq] using hi
      rw [hread, hd]
      decide
    · exact fun _ _ _ hp => hp
    · unfold timeBound
      omega

end JointThermoComplexity.Complexity.DenseProductBranch

#print axioms JointThermoComplexity.Complexity.DenseProductBranch.hoareTime
