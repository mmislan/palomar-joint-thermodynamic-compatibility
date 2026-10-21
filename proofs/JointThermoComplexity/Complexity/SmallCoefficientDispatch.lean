module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientMatch

set_option autoImplicit false
@[expose] public section

/-! Actual finite catalog lookup, with a uniform runtime on arbitrary stored
words and exact selection on every canonical coefficient from minus five to five.
-/

namespace JointThermoComplexity.Complexity.SmallCoefficientDispatch
open _root_.Complexity _root_.Complexity.TM SmallCoefficientMatch
open HeaderAt (Cursor)
variable {w : ℕ}

def machine (p : Ports w) (body : ℤ → TM (w + 1)) (fallback : TM (w + 1)) : List ℤ → TM (w + 1)
  | [] => fallback
  | z :: rest => seqTM (SmallCoefficientMatch.machine p z)
      (WorkSymbolBranch.machine Γ.zero p.flag (body z) (machine p body fallback rest))

def timeBound (B T count : ℕ) : ℕ := count * (SmallCoefficientMatch.timeBound B + 3) + T

theorem hoareTime (p : Ports w) (bits : List Bool) (entries : List ℤ)
    (he : ∀ z ∈ entries, z.natAbs ≤ 5) (B T : ℕ) (hB : 2 ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R)
    (body : ℤ → TM (w + 1)) (f : ℤ → List Bool) (fallback : TM (w + 1)) (fallbackBits : List Bool)
    (hb : ∀ z ∈ entries, (body z).HoareTime (Logical p bits B before input emitted R)
      (Logical p bits B before input (emitted ++ f z) R) T)
    (hf : fallback.HoareTime (Logical p bits B before input emitted R)
      (Logical p bits B before input (emitted ++ fallbackBits) R) T) :
    (machine p body fallback entries).HoareTime (Logical p bits B before input emitted R)
      (Logical p bits B before input (emitted ++ SmallCoefficientTable.select bits f fallbackBits entries) R)
      (timeBound B T entries.length) := by
  induction entries with
  | nil => simpa only [machine, SmallCoefficientTable.select, timeBound, List.length_nil, Nat.zero_mul, Nat.zero_add] using hf
  | cons z rest ih =>
    have hz := he z (by simp)
    have hbody := hb z (by simp)
    have hrest := ih (fun q hq => he q (by simp [hq])) (fun q hq => hb q (by simp [hq]))
    have htest := SmallCoefficientMatch.hoareTime p bits z hz B hB before input emitted R hR
    have hbranch : (WorkSymbolBranch.machine Γ.zero p.flag (body z) (machine p body fallback rest)).HoareTime
        (fun inp work out => Logical p bits B before input emitted R inp work out ∧
          (work p.flag).read = Γ.ofBool (!(SmallCoefficientTable.equalCode bits z)))
        (Logical p bits B before input (emitted ++ SmallCoefficientTable.select bits f fallbackBits (z :: rest)) R)
        (timeBound B T rest.length + 2) := by
      cases hm : SmallCoefficientTable.equalCode bits z with
      | true =>
        have h := WorkSymbolBranch.yes_hoareTime Γ.zero p.flag (body z) (machine p body fallback rest)
          before input emitted before input (emitted ++ f z) (Ready p bits B R) (Ready p bits B R) T hbody
        apply h.consequence
        · rintro inp work out ⟨⟨hc, hr⟩, hflag⟩
          exact ⟨⟨hc, hr⟩, by simpa only [Bool.not_true, Γ.ofBool] using hflag⟩
        · intro inp work out hh
          simpa only [SmallCoefficientTable.select, hm, ↓reduceIte, Logical] using hh
        · unfold timeBound
          omega
      | false =>
        have h := WorkSymbolBranch.no_hoareTime Γ.zero p.flag (body z) (machine p body fallback rest)
          before input emitted before input (emitted ++ SmallCoefficientTable.select bits f fallbackBits rest)
          (Ready p bits B R) (Ready p bits B R) (timeBound B T rest.length) hrest
        apply h.consequence
        · rintro inp work out ⟨⟨hc, hr⟩, hflag⟩
          refine ⟨⟨hc, hr⟩, ?_⟩
          rw [hflag]
          decide
        · intro inp work out hh
          simpa only [SmallCoefficientTable.select, hm, Bool.false_eq_true, ↓reduceIte, Logical] using hh
        · exact le_rfl
    have h := seqTM_hoareTime _ _ htest (by
      rintro inp work out ⟨⟨hc, hr⟩, hflag⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨⟨hc, hr⟩, hflag⟩) hbranch
    exact h.mono_bound (by simp only [timeBound, List.length_cons, Nat.add_mul, Nat.one_mul]; omega)

theorem catalog_hoareTime (p : Ports w) (a : ℤ) (ha : a.natAbs ≤ 5) (B T : ℕ) (hB : 2 ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R)
    (body : ℤ → TM (w + 1)) (f : ℤ → List Bool) (fallback : TM (w + 1)) (fallbackBits : List Bool)
    (hb : ∀ z ∈ SmallCoefficientTable.catalog, (body z).HoareTime
      (Logical p (BitCodec.integerCode a) B before input emitted R)
      (Logical p (BitCodec.integerCode a) B before input (emitted ++ f z) R) T)
    (hf : fallback.HoareTime (Logical p (BitCodec.integerCode a) B before input emitted R)
      (Logical p (BitCodec.integerCode a) B before input (emitted ++ fallbackBits) R) T) :
    (machine p body fallback SmallCoefficientTable.catalog).HoareTime
      (Logical p (BitCodec.integerCode a) B before input emitted R)
      (Logical p (BitCodec.integerCode a) B before input (emitted ++ f a) R) (timeBound B T 11) := by
  simpa only [SmallCoefficientTable.catalog_length, SmallCoefficientTable.select_catalog a ha f fallbackBits] using
    hoareTime p (BitCodec.integerCode a) SmallCoefficientTable.catalog SmallCoefficientTable.catalog_bound B T hB
      before input emitted R hR body f fallback fallbackBits hb hf

end JointThermoComplexity.Complexity.SmallCoefficientDispatch

#print axioms JointThermoComplexity.Complexity.SmallCoefficientDispatch.hoareTime
#print axioms JointThermoComplexity.Complexity.SmallCoefficientDispatch.catalog_hoareTime
