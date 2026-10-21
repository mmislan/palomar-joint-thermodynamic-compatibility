module
public import proofs.JointThermoComplexity.Complexity.BinaryEqualityFlag

set_option autoImplicit false
@[expose] public section

/-! Emit an exact natural-valued indicator cell from retained binary indices. -/

namespace JointThermoComplexity.Complexity.BinaryEqualityEmit
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def word (k n m : ℕ) : List Bool := BitCodec.naturalCode (if n = m then k else 0)
def choose (p : Ports w) (k : ℕ) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.zero p.flag (emitBitsTM (BitCodec.naturalCode k)) (emitBitsTM (BitCodec.naturalCode 0))
def machine (p : Ports w) (k : ℕ) : TM (w + 1) := seqTM (BinaryEqualityFlag.machine p) (choose p k)

def Fields (p : Ports w) (n m : ℕ) (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  Register n (work p.operand) ∧ Register m (work p.constant) ∧ (work p.flag).head = 1 ∧ R work ∧
    (work p.flag).read = Γ.ofBool (decide (n ≠ m))

theorem fixed (p : Ports w) (n m : ℕ) (bits before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM bits : TM (w + 1)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Fields p n m R work)
      (fun inp work out => Cursor before input (emitted ++ bits) inp work out ∧ (∀ j, Parked (work j)) ∧ Fields p n m R work)
      bits.length := FixedOutput.hoareTime bits before input emitted (Fields p n m R)

theorem choose_hoareTime (p : Ports w) (k n m : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) :
    (choose p k).HoareTime
      (fun inp work out => BinaryEqualityFlag.Pre p n m before input emitted R inp work out ∧
        (work p.flag).read = Γ.ofBool (decide (n ≠ m)))
      (fun inp work out => BinaryEqualityFlag.Pre p n m before input (emitted ++ word k n m) R inp work out ∧
        (work p.flag).read = Γ.ofBool (decide (n ≠ m)))
      (max (BitCodec.naturalCode k).length (BitCodec.naturalCode 0).length + 2) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Fields p n m R work
  by_cases hn : n = m
  · have hfixed := fixed p n m (BitCodec.naturalCode k) before input emitted R
    have hh := WorkSymbolBranch.yes_hoareTime Γ.zero p.flag (emitBitsTM (BitCodec.naturalCode k))
      (emitBitsTM (BitCodec.naturalCode 0)) before input emitted before input (emitted ++ BitCodec.naturalCode k)
      P P (BitCodec.naturalCode k).length hfixed
    apply hh.consequence
    · rintro inp work out ⟨⟨hc, hs, hv, hu, hf, hr⟩, hflag⟩
      exact ⟨⟨hc, hs, hv, hu, hf, hr, hflag⟩, by simpa [hn, Γ.ofBool] using hflag⟩
    · rintro inp work out ⟨hc, hs, hv, hu, hf, hr, hflag⟩
      exact ⟨⟨by simpa only [word, hn, ↓reduceIte] using hc, hs, hv, hu, hf, hr⟩, hflag⟩
    · have hh := Nat.le_max_left (BitCodec.naturalCode k).length (BitCodec.naturalCode 0).length
      omega
  · have hfixed := fixed p n m (BitCodec.naturalCode 0) before input emitted R
    have hh := WorkSymbolBranch.no_hoareTime Γ.zero p.flag (emitBitsTM (BitCodec.naturalCode k))
      (emitBitsTM (BitCodec.naturalCode 0)) before input emitted before input (emitted ++ BitCodec.naturalCode 0)
      P P (BitCodec.naturalCode 0).length hfixed
    apply hh.consequence
    · rintro inp work out ⟨⟨hc, hs, hv, hu, hf, hr⟩, hflag⟩
      refine ⟨⟨hc, hs, hv, hu, hf, hr, hflag⟩, ?_⟩
      rw [hflag]
      simp [hn, Γ.ofBool]
    · rintro inp work out ⟨hc, hs, hv, hu, hf, hr, hflag⟩
      exact ⟨⟨by simpa only [word, hn, ↓reduceIte] using hc, hs, hv, hu, hf, hr⟩, hflag⟩
    · have hh := Nat.le_max_right (BitCodec.naturalCode k).length (BitCodec.naturalCode 0).length
      omega

def bound (B k : ℕ) : ℕ := 24 * B + max (BitCodec.naturalCode k).length (BitCodec.naturalCode 0).length + 24

theorem hoareTime (p : Ports w) (k n m B : ℕ) (hn : n.bits.length ≤ B) (hm : m.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : SmallCoefficientMatch.Stable p R) :
    (machine p k).HoareTime (BinaryEqualityFlag.Pre p n m before input emitted R)
      (BinaryEqualityFlag.Pre p n m before input (emitted ++ word k n m) R) (bound B k) := by
  have he := BinaryEqualityFlag.hoareTime p n m B hn hm before input emitted R hR
  have ho := choose_hoareTime p k n m before input emitted R
  have hh := seqTM_hoareTime _ _ he (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.1.phase
    rw [hi, hw, ho]
    exact hp) ho
  exact hh.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp.1) (by unfold bound; omega)

end JointThermoComplexity.Complexity.BinaryEqualityEmit

#print axioms JointThermoComplexity.Complexity.BinaryEqualityEmit.hoareTime
