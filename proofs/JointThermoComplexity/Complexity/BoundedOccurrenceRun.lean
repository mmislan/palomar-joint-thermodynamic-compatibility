module
public import proofs.JointThermoComplexity.Complexity.BoundedOccurrenceMachine

set_option autoImplicit false
@[expose] public section

/-! All-raw runtime for the statically bounded occurrence loader. The retained
per-position markers support subsequent finite dispatch without interpreting a
binary numeric value as loop fuel. -/

namespace JointThermoComplexity.Complexity.BoundedOccurrenceRun
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BoundedOccurrenceMachine
variable {w : ℕ}

theorem data_ne_flag {slots : List (Port w)} {ending flag : Fin (w + 1)}
    (hs : Separate slots ending flag) : ∀ p ∈ slots, p.1 ≠ flag := by
  induction slots with
  | nil => simp
  | cons p slots ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hs.1.data_flag
    · exact ih hs.2 q hq

theorem marker_ne_flag {slots : List (Port w)} {ending flag : Fin (w + 1)}
    (hs : Separate slots ending flag) : ∀ p ∈ slots, p.2 ≠ flag := by
  induction slots with
  | nil => simp
  | cons p slots ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hs.1.marker_flag
    · exact ih hs.2 q hq

theorem ending_ne_flag {slots : List (Port w)} {ending flag : Fin (w + 1)}
    (hs : Separate slots ending flag) : ending ≠ flag := by
  induction slots with
  | nil => exact hs
  | cons p slots ih => exact ih hs.2

def Pre (L : ℕ) (slots : List (Port w)) (ending flag : Fin (w + 1))
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape) : Prop :=
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    Ready L slots ending flag work ∧ R work

def Post (L : ℕ) (slots : List (Port w)) (ending flag : Fin (w + 1))
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape) : Prop :=
  Cursor (before ++ (BoundedOccurrenceControl.scan slots.length input).taken)
      (BoundedOccurrenceControl.scan slots.length input).rest emitted inp work out ∧
    (∀ j, Parked (work j)) ∧ Ready L slots ending flag work ∧
      Loaded slots ending flag input work ∧ R work

theorem hoareTime (slots : List (Port w)) (ending flag : Fin (w + 1))
    (hsep : Separate slots ending flag) (L : ℕ) (before input emitted : List Bool)
    (hlen : input.length ≤ L) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, ¬Touches slots ending flag j → next j = work j) → R work → R next) :
    (machine slots ending flag).HoareTime
      (Pre L slots ending flag before input emitted R)
      (Post L slots ending flag before input emitted R)
      (slots.length * (15 * L + 24) + 1) := by
  induction slots generalizing before input R with
  | nil =>
    have hs := SourceBitRead.hoareTime ending flag hsep before input emitted R (by
      intro work next hsame hr
      exact hR work next (fun j hj => hsame j (fun he => hj (Or.inl he))
        (fun hf => hj (Or.inr (Or.inl hf)))) hr)
    apply hs.consequence
    · rintro inp work out ⟨hc, hsafe, hready, hr⟩
      exact ⟨hc, hsafe, hready.2.1, hready.2.2, hr⟩
    · rintro inp work out ⟨hc, hsafe, heh, hfh, her, hfr, hr⟩
      exact ⟨hc, hsafe, ⟨by simp, heh, hfh⟩, ⟨her, hfr⟩, hr⟩
    · simp
  | cons p slots ih =>
    obtain ⟨hp, ht⟩ := hsep
    let S : (Fin (w + 1) → Tape) → Prop := fun work =>
      (∀ q ∈ p :: slots, Reusable L (work q.1)) ∧
        (∀ q ∈ slots, (work q.2).head = 1) ∧ (work ending).head = 1 ∧ R work
    have hS : ∀ work next, (∀ j, j ≠ p.2 → j ≠ flag → next j = work j) → S work → S next := by
      rintro work next he ⟨hd, hm, hend, hr⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro q hq
        have hqm : q.1 ≠ p.2 := by
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hp.data_marker
          · exact (hp.marker_data q hq).symm
        rw [he q.1 hqm (data_ne_flag (slots := p :: slots) ⟨hp, ht⟩ q hq)]
        exact hd q hq
      · intro q hq
        rw [he q.2 (hp.marker_markers q hq).symm (marker_ne_flag ht q hq)]
        exact hm q hq
      · rw [he ending hp.marker_end.symm (ending_ne_flag ht)]
        exact hend
      · exact hR work next (fun j hj => he j
          (fun hm => hj (Or.inr (Or.inr ⟨p, List.mem_cons_self, Or.inr hm⟩)))
          (fun hf => hj (Or.inr (Or.inl hf)))) hr
    have hs := SourceBitRead.hoareTime p.2 flag hp.marker_flag before input emitted S hS
    cases hv : SourceBitRead.value input with
    | false =>
      let B : (Fin (w + 1) → Tape) → Prop := fun work =>
        (∀ j, Parked (work j)) ∧ (work p.2).head = 1 ∧ (work flag).head = 1 ∧
        (work p.2).read = Γ.ofBool false ∧
        (work flag).read = Γ.ofBool (BooleanMachine.accepted input) ∧ S work
      have hn := noop_hoareTime (before ++ BooleanMachine.copied input)
        (BooleanMachine.suffix input) emitted B
      have hb := WorkSymbolBranch.no_hoareTime Γ.one p.2
        (seqTM (NaturalCanonicalLoad.machine p.1) (machine slots ending flag)) (emitBitsTM [])
        (before ++ BooleanMachine.copied input) (BooleanMachine.suffix input) emitted
        (before ++ BooleanMachine.copied input) (BooleanMachine.suffix input) emitted B B 0 hn
      have hf := seqTM_hoareTime _ _ hs (by
        rintro inp work out ⟨hc, hsafe, hmh, hfh, hmr, hfr, hr⟩
        obtain ⟨hi, hw, ho⟩ := hc.phase
        rw [hi, hw, ho]
        have hm : (work p.2).read = Γ.ofBool false := by simpa only [hv] using hmr
        exact ⟨⟨hc, hsafe, hmh, hfh, hm, hfr, hr⟩, by rw [hm]; decide⟩) hb
      apply hf.consequence
      · rintro inp work out ⟨hc, hsafe, hready, hr⟩
        exact ⟨hc, hsafe, (hready.1 p List.mem_cons_self).2, hready.2.2,
          (fun q hq => (hready.1 q hq).1),
          (fun q hq => (hready.1 q (List.mem_cons_of_mem p hq)).2), hready.2.1, hr⟩
      · rintro inp work out ⟨hc, hsafe, hmh, hfh, hmr, hfr, hd, hm, heh, hr⟩
        refine ⟨?_, hsafe, ?_, ?_, hr⟩
        · simpa only [List.length_cons, BoundedOccurrenceControl.scan, hv, Bool.false_eq_true,
            ↓reduceIte, BoundedOccurrenceControl.stop] using hc
        · refine ⟨?_, heh, hfh⟩
          intro q hq
          refine ⟨hd q hq, ?_⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hmh
          · exact hm q hq
        · simpa only [Loaded, hv, Bool.false_eq_true, ↓reduceIte] using And.intro hmr hfr
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
    | true =>
      let body := BooleanMachine.suffix input
      let field := NaturalRawControl.scan body
      let beforeField := (before ++ BooleanMachine.copied input) ++ field.taken
      have hbody : body.length ≤ L := (SignedRawControl.suffix_length input).trans hlen
      have hfield : field.rest.length ≤ L := by
        change (NaturalRawControl.scan body).rest.length ≤ L
        have hf := congrArg List.length (NaturalRawControl.split body)
        simp only [List.length_append] at hf
        omega
      let T : (Fin (w + 1) → Tape) → Prop := fun work => Ready L slots ending flag work ∧
        (work p.2).head = 1 ∧ (work p.2).read = Γ.one ∧ R work
      have hT : ∀ work next, (∀ j, j ≠ p.1 → next j = work j) → T work → T next := by
        rintro work next he ⟨hready, hmh, hmr, hr⟩
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
        · intro q hq
          rw [he q.1 (hp.data_data q hq).symm, he q.2 (hp.data_markers q hq).symm]
          exact hready.1 q hq
        · rw [he ending hp.data_end.symm]; exact hready.2.1
        · rw [he flag hp.data_flag.symm]; exact hready.2.2
        · rw [he p.2 hp.data_marker.symm]; exact hmh
        · rw [he p.2 hp.data_marker.symm]; exact hmr
        · exact hR work next (fun j hj => he j
            (fun hd => hj (Or.inr (Or.inr ⟨p, List.mem_cons_self, Or.inl hd⟩)))) hr
      have hn := NaturalCanonicalLoad.hoareTime L p.1 (before ++ BooleanMachine.copied input)
        body emitted hbody T hT
      let U : (Fin (w + 1) → Tape) → Prop := fun work =>
        Reusable L (work p.1) ∧ BinaryIncrementRun.Register (NaturalCanonicalLoad.value body) (work p.1) ∧
        (work p.2).head = 1 ∧ (work p.2).read = Γ.one ∧ R work
      have hU : ∀ work next, (∀ j, ¬Touches slots ending flag j → next j = work j) → U work → U next := by
        rintro work next he ⟨hb, hv, hmh, hmr, hr⟩
        exact ⟨by rw [he p.1 hp.data_untouched]; exact hb,
          by rw [he p.1 hp.data_untouched]; exact hv,
          by rw [he p.2 hp.marker_untouched]; exact hmh,
          by rw [he p.2 hp.marker_untouched]; exact hmr,
          hR work next (fun j hj => he j (fun htouch => hj (touches_tail htouch))) hr⟩
      have hr := ih ht beforeField field.rest hfield U hU
      have hnr := seqTM_hoareTime _ _ hn (by
        rintro inp work out ⟨hc, hsafe, hv, hb, hready, hmh, hmr, hx⟩
        obtain ⟨hi, hw, ho⟩ := hc.phase
        rw [hi, hw, ho]
        exact ⟨hc, hsafe, hready, hb, hv, hmh, hmr, hx⟩) hr
      have hb := WorkSymbolBranch.yes_hoareTime Γ.one p.2
        (seqTM (NaturalCanonicalLoad.machine p.1) (machine slots ending flag)) (emitBitsTM [])
        (before ++ BooleanMachine.copied input) body emitted
        (beforeField ++ (BoundedOccurrenceControl.scan slots.length field.rest).taken)
        (BoundedOccurrenceControl.scan slots.length field.rest).rest emitted
        (fun work => (∀ j, Parked (work j)) ∧ Reusable L (work p.1) ∧ T work)
        (fun work => (∀ j, Parked (work j)) ∧ Ready L slots ending flag work ∧
          Loaded slots ending flag field.rest work ∧ U work)
        (15 * L + 18 + 1 + (slots.length * (15 * L + 24) + 1)) hnr
      have hf := seqTM_hoareTime _ _ hs (by
        rintro inp work out ⟨hc, hsafe, hmh, hfh, hmr, _hfr, hd, hm, heh, hx⟩
        obtain ⟨hi, hw, ho⟩ := hc.phase
        rw [hi, hw, ho]
        have hv : (work p.2).read = Γ.one := by simpa only [hv, Γ.ofBool] using hmr
        exact ⟨⟨hc, hsafe, hd p List.mem_cons_self,
          ⟨(fun q hq => ⟨hd q (List.mem_cons_of_mem p hq), hm q hq⟩), heh, hfh⟩,
          hmh, hv, hx⟩, hv⟩) hb
      apply hf.consequence
      · rintro inp work out ⟨hc, hsafe, hready, hx⟩
        exact ⟨hc, hsafe, (hready.1 p List.mem_cons_self).2, hready.2.2,
          (fun q hq => (hready.1 q hq).1),
          (fun q hq => (hready.1 q (List.mem_cons_of_mem p hq)).2), hready.2.1, hx⟩
      · rintro inp work out ⟨hc, hsafe, hready, hloaded, hreuse, hreg, hmh, hmr, hx⟩
        refine ⟨?_, hsafe, ?_, ?_, hx⟩
        · simpa only [List.length_cons, BoundedOccurrenceControl.scan, hv, ↓reduceIte,
            beforeField, field, body, List.append_assoc] using hc
        · refine ⟨?_, hready.2⟩
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hreuse, hmh⟩
          · exact hready.1 q hq
        · simpa only [Loaded, hv, ↓reduceIte, Γ.ofBool] using And.intro hmr (And.intro hreg hloaded)
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

def Encoded : List (Port w) → Fin (w + 1) → List ℕ → (Fin (w + 1) → Tape) → Prop
  | [], ending, [], work => (work ending).read = Γ.zero
  | p :: _, _, [], work => (work p.2).read = Γ.zero
  | [], _, _ :: _, _ => False
  | p :: slots, ending, v :: vs, work => (work p.2).read = Γ.one ∧
    BinaryIncrementRun.Register v (work p.1) ∧ Encoded slots ending vs work

theorem loaded_available (slots : List (Port w)) (ending flag : Fin (w + 1))
    (input : List Bool) (work : Fin (w + 1) → Tape) (h : Loaded slots ending flag input work) :
    (work flag).read = Γ.ofBool (BoundedOccurrenceControl.scan slots.length input).available := by
  induction slots generalizing input with
  | nil => exact h.2
  | cons p slots ih =>
    cases hv : SourceBitRead.value input
    · simpa only [Loaded, hv, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        BoundedOccurrenceControl.scan, BoundedOccurrenceControl.stop] using h.2
    · have hc : BinaryIncrementRun.Register (NaturalCanonicalLoad.value (BooleanMachine.suffix input)) (work p.1) ∧
          Loaded slots ending flag (NaturalRawControl.scan (BooleanMachine.suffix input)).rest work := by
        simpa only [hv, ↓reduceIte] using h.2
      simpa only [List.length_cons, BoundedOccurrenceControl.scan, hv, ↓reduceIte] using ih _ hc.2

theorem loaded_encoded {n : ℕ} (slots : List (Port w)) (ending flag : Fin (w + 1))
    (vs : List (Fin n)) (suffix : List Bool) (hlen : vs.length ≤ slots.length)
    (work : Fin (w + 1) → Tape)
    (h : Loaded slots ending flag (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) work) :
    Encoded slots ending (vs.map Fin.val) work := by
  induction slots generalizing vs with
  | nil =>
    have hz : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst vs
    exact h.1
  | cons p slots ih =>
    cases vs with
    | nil => exact h.1
    | cons v vs =>
      have hc : (work p.2).read = Γ.one ∧ BinaryIncrementRun.Register v.val (work p.1) ∧
          Loaded slots ending flag (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) work := by
        simpa [Loaded, SparseListCodec.listCode, SparseListCodec.finite, SourceBitRead.value,
          BooleanMachine.suffix, List.append_assoc, NaturalRawControl.natural,
          NaturalCanonicalLoad.value, Γ.ofBool] using h
      exact ⟨hc.1, hc.2.1, ih vs (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hlen) hc.2.2⟩

theorem finite_hoareTime {n : ℕ} (slots : List (Port w)) (ending flag : Fin (w + 1))
    (hsep : Separate slots ending flag) (L : ℕ) (before emitted suffix : List Bool)
    (vs : List (Fin n)) (hcap : vs.length ≤ slots.length)
    (hlen : (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix).length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, ¬Touches slots ending flag j → next j = work j) → R work → R next) :
    (machine slots ending flag).HoareTime
      (Pre L slots ending flag before (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) emitted R)
      (fun inp work out => Cursor (before ++ SparseListCodec.listCode (SparseListCodec.finite n) vs)
          suffix emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready L slots ending flag work ∧
        Encoded slots ending (vs.map Fin.val) work ∧ (work flag).read = Γ.one ∧ R work)
      (slots.length * (15 * L + 24) + 1) := by
  have h := hoareTime slots ending flag hsep L before
    (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) emitted hlen R hR
  apply h.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hsafe, hready, hloaded, hx⟩
    have hf := loaded_available slots ending flag _ work hloaded
    rw [BoundedOccurrenceControl.finite_code vs suffix slots.length hcap] at hf
    exact ⟨by simpa only [BoundedOccurrenceControl.finite_code vs suffix slots.length hcap] using hc,
      hsafe, hready, loaded_encoded slots ending flag vs suffix hcap work hloaded, hf, hx⟩
  · exact le_rfl

theorem four_hoareTime (slots : List (Port w)) (ending flag : Fin (w + 1))
    (hfour : slots.length = 4) (hsep : Separate slots ending flag) (L : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, ¬Touches slots ending flag j → next j = work j) → R work → R next) :
    (machine slots ending flag).HoareTime (Pre L slots ending flag before input emitted R)
      (Post L slots ending flag before input emitted R) (60 * L + 97) := by
  apply (hoareTime slots ending flag hsep L before input emitted hlen R hR).mono_bound
  rw [hfour]
  omega

end JointThermoComplexity.Complexity.BoundedOccurrenceRun

#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceRun.hoareTime
#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceRun.finite_hoareTime
#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceRun.four_hoareTime
