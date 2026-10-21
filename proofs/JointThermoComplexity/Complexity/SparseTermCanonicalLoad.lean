module
public import proofs.JointThermoComplexity.Complexity.SparseTermRawControl
public import proofs.JointThermoComplexity.Complexity.SignedCanonicalLoad
public import proofs.JointThermoComplexity.Complexity.BoundedOccurrenceRun

set_option autoImplicit false
@[expose] public section

/-! A complete sparse term loader: original signed coefficient and at most
four binary variable references. The common availability flag is reused while
the original coefficient and sign survive the occurrence scan. -/

namespace JointThermoComplexity.Complexity.SparseTermCanonicalLoad
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BoundedOccurrenceMachine
variable {w : ℕ}

structure Separate (slots : List (Port w)) (ending flag magnitude sign : Fin (w + 1)) : Prop where
  occurrences : BoundedOccurrenceMachine.Separate slots ending flag
  magnitude_sign : magnitude ≠ sign
  magnitude_outside : ¬Touches slots ending flag magnitude
  sign_outside : ¬Touches slots ending flag sign

theorem inside_ne_outside {slots : List (Port w)} {ending flag j k : Fin (w + 1)}
    (hj : Touches slots ending flag j) (hk : ¬Touches slots ending flag k) : j ≠ k := by
  intro he
  exact hk (he ▸ hj)

def machine (slots : List (Port w)) (ending flag magnitude sign : Fin (w + 1)) : TM (w + 1) :=
  seqTM (SignedCanonicalLoad.machine magnitude sign flag) (BoundedOccurrenceMachine.machine slots ending flag)

def Pre (L : ℕ) (slots : List (Port w)) (ending flag magnitude sign : Fin (w + 1))
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape) : Prop :=
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable L (work magnitude) ∧
    (work sign).head = 1 ∧ Ready L slots ending flag work ∧ R work

def Post (L : ℕ) (slots : List (Port w)) (ending flag magnitude sign : Fin (w + 1))
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape) : Prop :=
  Cursor (before ++ SparseTermRawControl.taken slots.length input) (SparseTermRawControl.rest slots.length input)
      emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable L (work magnitude) ∧
    BinaryIncrementRun.Register (SignedRawControl.magnitude input) (work magnitude) ∧
    (work sign).head = 1 ∧ (work sign).read = Γ.ofBool (SignedRawControl.negative input) ∧
    Ready L slots ending flag work ∧ Loaded slots ending flag (SignedRawControl.rest input) work ∧ R work

theorem hoareTime (slots : List (Port w)) (ending flag magnitude sign : Fin (w + 1))
    (hsep : Separate slots ending flag magnitude sign) (L : ℕ) (before input emitted : List Bool)
    (hlen : input.length ≤ L) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ magnitude → j ≠ sign → ¬Touches slots ending flag j → next j = work j) →
      R work → R next) :
    (machine slots ending flag magnitude sign).HoareTime
      (Pre L slots ending flag magnitude sign before input emitted R)
      (Post L slots ending flag magnitude sign before input emitted R)
      (15 * L + 20 + 1 + (slots.length * (15 * L + 24) + 1)) := by
  have hflag : Touches slots ending flag flag := Or.inr (Or.inl rfl)
  have hend : Touches slots ending flag ending := Or.inl rfl
  have hmf : magnitude ≠ flag := (inside_ne_outside hflag hsep.magnitude_outside).symm
  have hsf : sign ≠ flag := (inside_ne_outside hflag hsep.sign_outside).symm
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    (∀ q ∈ slots, Reusable L (work q.1) ∧ (work q.2).head = 1) ∧ (work ending).head = 1 ∧ R work
  have hS : ∀ work next, (∀ j, j ≠ magnitude → j ≠ sign → j ≠ flag → next j = work j) → S work → S next := by
    rintro work next he ⟨hready, heh, hr⟩
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      have hd : Touches slots ending flag q.1 := Or.inr (Or.inr ⟨q, hq, Or.inl rfl⟩)
      have hm : Touches slots ending flag q.2 := Or.inr (Or.inr ⟨q, hq, Or.inr rfl⟩)
      rw [he q.1 (inside_ne_outside hd hsep.magnitude_outside) (inside_ne_outside hd hsep.sign_outside)
        (BoundedOccurrenceRun.data_ne_flag hsep.occurrences q hq),
        he q.2 (inside_ne_outside hm hsep.magnitude_outside) (inside_ne_outside hm hsep.sign_outside)
        (BoundedOccurrenceRun.marker_ne_flag hsep.occurrences q hq)]
      exact hready q hq
    · rw [he ending (inside_ne_outside hend hsep.magnitude_outside) (inside_ne_outside hend hsep.sign_outside)
        (BoundedOccurrenceRun.ending_ne_flag hsep.occurrences)]
      exact heh
    · exact hR work next (fun j hjm hjs hj => he j hjm hjs (fun hf => hj (hf ▸ hflag))) hr
  have hs := SignedCanonicalLoad.hoareTime L magnitude sign flag hsep.magnitude_sign hmf hsf
    before input emitted hlen S hS
  let T : (Fin (w + 1) → Tape) → Prop := fun work =>
    Reusable L (work magnitude) ∧ BinaryIncrementRun.Register (SignedRawControl.magnitude input) (work magnitude) ∧
    (work sign).head = 1 ∧ (work sign).read = Γ.ofBool (SignedRawControl.negative input) ∧ R work
  have hT : ∀ work next, (∀ j, ¬Touches slots ending flag j → next j = work j) → T work → T next := by
    rintro work next he ⟨hb, hv, hsh, hsr, hr⟩
    exact ⟨by rw [he magnitude hsep.magnitude_outside]; exact hb,
      by rw [he magnitude hsep.magnitude_outside]; exact hv,
      by rw [he sign hsep.sign_outside]; exact hsh,
      by rw [he sign hsep.sign_outside]; exact hsr,
      hR work next (fun j _ _ hj => he j hj) hr⟩
  have ho := BoundedOccurrenceRun.hoareTime slots ending flag hsep.occurrences L
    (before ++ SignedRawControl.taken input) (SignedRawControl.rest input) emitted
    ((SignedRawControl.rest_length input).trans hlen) T hT
  have hf := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨hc, hsafe, hv, hb, hsh, hfh, hsr, _hfr, hready, heh, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hsafe, ⟨hready, heh, hfh⟩, hb, hv, hsh, hsr, hx⟩) ho
  apply hf.consequence
  · rintro inp work out ⟨hc, hsafe, hb, hsh, hready, hx⟩
    exact ⟨hc, hsafe, hb, hsh, hready.2.2, hready.1, hready.2.1, hx⟩
  · rintro inp work out ⟨hc, hsafe, hready, hloaded, hb, hv, hsh, hsr, hx⟩
    exact ⟨by simpa only [SparseTermRawControl.taken, SparseTermRawControl.rest,
        SparseTermRawControl.occurrences, List.append_assoc] using hc,
      hsafe, hb, hv, hsh, hsr, hready, hloaded, hx⟩
  · exact le_rfl

theorem code_hoareTime {n : ℕ} (slots : List (Port w)) (ending flag magnitude sign : Fin (w + 1))
    (hsep : Separate slots ending flag magnitude sign) (L : ℕ) (before emitted suffix : List Bool)
    (c : ℤ) (vs : List (Fin n)) (hcap : vs.length ≤ slots.length)
    (hlen : (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix).length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ magnitude → j ≠ sign → ¬Touches slots ending flag j → next j = work j) →
      R work → R next) :
    (machine slots ending flag magnitude sign).HoareTime
      (Pre L slots ending flag magnitude sign before
        (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) emitted R)
      (fun inp work out => Cursor (before ++ (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs))
          suffix emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable L (work magnitude) ∧
        BinaryIncrementRun.Register c.natAbs (work magnitude) ∧ (work sign).head = 1 ∧
        (work sign).read = Γ.ofBool (decide (c < 0)) ∧ Ready L slots ending flag work ∧
        BoundedOccurrenceRun.Encoded slots ending (vs.map Fin.val) work ∧ (work flag).read = Γ.one ∧ R work)
      (15 * L + 20 + 1 + (slots.length * (15 * L + 24) + 1)) := by
  have h := hoareTime slots ending flag magnitude sign hsep L before
    (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) emitted hlen R hR
  apply h.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hsafe, hb, hv, hsh, hsr, hready, hloaded, hx⟩
    have hl : Loaded slots ending flag (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) work := by
      simpa only [List.append_assoc, SignedRawControl.rest_integer] using hloaded
    have hav := BoundedOccurrenceRun.loaded_available slots ending flag _ work hl
    rw [BoundedOccurrenceControl.finite_code vs suffix slots.length hcap] at hav
    exact ⟨by simpa only [SparseTermRawControl.taken_code c vs suffix slots.length hcap,
        SparseTermRawControl.rest_code c vs suffix slots.length hcap] using hc,
      hsafe, hb,
      by simpa only [List.append_assoc, SignedRawControl.magnitude_integer] using hv,
      hsh, by simpa only [List.append_assoc, SignedRawControl.negative_integer] using hsr,
      hready, BoundedOccurrenceRun.loaded_encoded slots ending flag vs suffix hcap work hl, hav, hx⟩
  · exact le_rfl

theorem four_hoareTime (slots : List (Port w)) (ending flag magnitude sign : Fin (w + 1))
    (hfour : slots.length = 4) (hsep : Separate slots ending flag magnitude sign) (L : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ magnitude → j ≠ sign → ¬Touches slots ending flag j → next j = work j) →
      R work → R next) :
    (machine slots ending flag magnitude sign).HoareTime
      (Pre L slots ending flag magnitude sign before input emitted R)
      (Post L slots ending flag magnitude sign before input emitted R) (75 * L + 118) := by
  apply (hoareTime slots ending flag magnitude sign hsep L before input emitted hlen R hR).mono_bound
  rw [hfour]
  omega

end JointThermoComplexity.Complexity.SparseTermCanonicalLoad

#print axioms JointThermoComplexity.Complexity.SparseTermCanonicalLoad.machine
#print axioms JointThermoComplexity.Complexity.SparseTermCanonicalLoad.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseTermCanonicalLoad.code_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseTermCanonicalLoad.four_hoareTime
