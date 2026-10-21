module
public import proofs.JointThermoComplexity.Complexity.SparseDimensionWords
public import proofs.JointThermoComplexity.Complexity.SparseDimensionFrame

set_option autoImplicit false
@[expose] public section

/-! Actual species/reaction/core dimension headers with reusable source state. -/

namespace JointThermoComplexity.Complexity.SparseDimensionEmit
open _root_.Complexity _root_.Complexity.TM HeaderAt
open SparseOffsetPorts SparseDimensionWords SparseDimensionFrame
open CountedSparseControl (State)

def Pred (L n : ℕ) (s : State) (emitted : List Bool) : _root_.Complexity.TM.TapePred 33 := fun inp work out =>
  CountedMarkedStep.Inv L emitted (SparseCountedEntry.frame n) s inp work out ∧ IsReg L (work fuel.castSucc)

def Work (L n : ℕ) (s : State) (work : Fin 33 → Tape) : Prop :=
  CountedMarkedStep.Fields L s.base.offset s.rows (SparseCountedEntry.frame n) work ∧
    (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool s.base.running ∧ IsReg L (work fuel.castSucc)

theorem phase (L n : ℕ) (s : State) (emitted : List Bool) :
    ∀ inp work out, Pred L n s emitted inp work out →
      Pred L n s emitted (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out hp
  obtain ⟨hi, hw, ho⟩ := hp.1.1.phase
  rw [hi, hw, ho]
  exact hp

theorem repeat_hoareTime (L n : ℕ) (s : State) (emitted word : List Bool) :
    (RepeatedOutput.machine arity.castSucc word).HoareTime (Pred L n s emitted)
      (Pred L n s (emitted ++ RepeatedOutput.copies word n)) (n * (word.length + 2) + (n + 2)) := by
  have hh := RepeatedOutput.hoareTime arity.castSucc n s.base.before s.base.input emitted word (Work L n s)
  apply hh.consequence
  · rintro inp work out ⟨⟨hc, hs, hfields, hmh, hmr⟩, hf⟩
    have hn := hfields.1.2.2.2.2.2
    exact ⟨hn, hc, hs, hfields, hmh, hmr, hf⟩
  · rintro inp work out ⟨_, hc, hs, hfields, hmh, hmr, hf⟩
    exact ⟨⟨hc, hs, hfields, hmh, hmr⟩, hf⟩
  · exact le_rfl

theorem fixed_hoareTime (L n : ℕ) (s : State) (emitted bits : List Bool) :
    (emitBitsTM bits : TM 33).HoareTime (Pred L n s emitted) (Pred L n s (emitted ++ bits)) bits.length := by
  have hh := FixedOutput.hoareTime bits s.base.before s.base.input emitted (Work L n s)
  apply hh.consequence
  · rintro inp work out ⟨⟨hc, hs, hfields, hmh, hmr⟩, hf⟩
    exact ⟨hc, hs, hfields, hmh, hmr, hf⟩
  · rintro inp work out ⟨hc, hs, hfields, hmh, hmr, hf⟩
    exact ⟨⟨hc, hs, hfields, hmh, hmr⟩, hf⟩
  · exact le_rfl

def twice : TM 33 := BoundedUnaryEmit.payload ports [true, true]
def twiceBound (L : ℕ) : ℕ := 2560 * L ^ 2 + 387 * L + 12

theorem twice_hoareTime (L n : ℕ) (s : State) (ht : s.rows ≤ 16 * L) (emitted : List Bool) :
    twice.HoareTime (Pred L n s emitted)
      (Pred L n s (emitted ++ RepeatedOutput.copies [true, true] s.rows)) (twiceBound L) := by
  have hbits := (BoundedUnaryControl.bits_le s.rows).trans ht
  have hh := BoundedUnaryEmit.payload_hoareTime ports [true, true] s.rows L (16 * L) hbits
    s.base.before s.base.input emitted (Protected L n s) (protected_stable L n s)
  have he : BoundedUnaryEmit.payloadBound L (16 * L) [true, true] = twiceBound L := by
    unfold BoundedUnaryEmit.payloadBound twiceBound
    rw [BoundedUnaryLoop.polynomial_timeBound]
    simp only [List.length_cons, List.length_nil]
    ring1
  rw [he] at hh
  apply hh.consequence
  · intro inp work out hp
    exact (state_iff L n s emitted inp out work).mp hp
  · intro inp work out hp
    rw [Nat.min_eq_right ht] at hp
    exact (state_iff L n s _ inp out work).mpr hp
  · exact le_rfl

def speciesMachine (boxed : Bool) : TM 33 := seqTM (RepeatedOutput.machine arity.castSucc (arityWord boxed))
  (seqTM twice (emitBitsTM (speciesPad boxed)))
def reactionMachine : TM 33 := seqTM twice (emitBitsTM reactionPad)
def machine (boxed : Bool) : TM 33 := seqTM (speciesMachine boxed)
  (seqTM reactionMachine (emitBitsTM (RealSyntax.binderCode 2)))

def speciesBound (L : ℕ) : ℕ := twiceBound L + 5 * L + 8
def reactionBound (L : ℕ) : ℕ := twiceBound L + 6
def bound (L : ℕ) : ℕ := 5120 * L ^ 2 + 779 * L + 44

theorem species_hoareTime (boxed : Bool) (L n : ℕ) (s : State) (hn : n ≤ L) (ht : s.rows ≤ 16 * L)
    (emitted : List Bool) :
    (speciesMachine boxed).HoareTime (Pred L n s emitted)
      (Pred L n s (emitted ++ RealSyntax.binderCode (species boxed n s.rows))) (speciesBound L) := by
  let ys := emitted ++ RepeatedOutput.copies (arityWord boxed) n
  let zs := ys ++ RepeatedOutput.copies [true, true] s.rows
  have ha := repeat_hoareTime L n s emitted (arityWord boxed)
  have ht' := twice_hoareTime L n s ht ys
  have hf := fixed_hoareTime L n s zs (speciesPad boxed)
  have htail := seqTM_hoareTime _ _ ht' (phase L n s zs) hf
  have hall := seqTM_hoareTime _ _ ha (phase L n s ys) htail
  have he : zs ++ speciesPad boxed = emitted ++ RealSyntax.binderCode (species boxed n s.rows) := by
    simpa only [ys, zs, List.append_assoc] using congrArg (fun tail : List Bool => emitted ++ tail) (species_word boxed n s.rows)
  apply hall.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    rw [he] at hp
    exact hp
  · have hw := arity_length boxed
    have hp := speciesPad_length boxed
    have hb : n * ((arityWord boxed).length + 2) + (n + 2) ≤ 5 * L + 2 := by
      have hm := Nat.mul_le_mul hn (show (arityWord boxed).length + 2 ≤ 4 by omega)
      omega
    unfold speciesBound
    omega

theorem reaction_hoareTime (L n : ℕ) (s : State) (ht : s.rows ≤ 16 * L) (emitted : List Bool) :
    reactionMachine.HoareTime (Pred L n s emitted)
      (Pred L n s (emitted ++ RealSyntax.binderCode (reactions s.rows))) (reactionBound L) := by
  let ys := emitted ++ RepeatedOutput.copies [true, true] s.rows
  have hp := twice_hoareTime L n s ht emitted
  have hf := fixed_hoareTime L n s ys reactionPad
  have hh := seqTM_hoareTime _ _ hp (phase L n s ys) hf
  have he : ys ++ reactionPad = emitted ++ RealSyntax.binderCode (reactions s.rows) := by
    simpa only [ys, List.append_assoc] using congrArg (fun tail : List Bool => emitted ++ tail) (reaction_word s.rows)
  apply hh.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    rw [he] at hp
    exact hp
  · unfold reactionBound reactionPad
    simp only [List.length_cons, List.length_nil]
    omega

theorem hoareTime (boxed : Bool) (L n : ℕ) (s : State) (hn : n ≤ L) (ht : s.rows ≤ 16 * L)
    (emitted : List Bool) :
    (machine boxed).HoareTime (Pred L n s emitted)
      (Pred L n s (emitted ++ header boxed n s.rows)) (bound L) := by
  let ys := emitted ++ RealSyntax.binderCode (species boxed n s.rows)
  let zs := ys ++ RealSyntax.binderCode (reactions s.rows)
  have hs := species_hoareTime boxed L n s hn ht emitted
  have hr := reaction_hoareTime L n s ht ys
  have hc := fixed_hoareTime L n s zs (RealSyntax.binderCode 2)
  have htail := seqTM_hoareTime _ _ hr (phase L n s zs) hc
  have hall := seqTM_hoareTime _ _ hs (phase L n s ys) htail
  apply hall.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    simpa only [ys, zs, header, List.append_assoc] using hp
  · change speciesBound L + 1 + (reactionBound L + 1 + 3) ≤ bound L
    unfold speciesBound reactionBound twiceBound bound
    omega

end JointThermoComplexity.Complexity.SparseDimensionEmit

#print axioms JointThermoComplexity.Complexity.SparseDimensionEmit.machine
#print axioms JointThermoComplexity.Complexity.SparseDimensionEmit.hoareTime
