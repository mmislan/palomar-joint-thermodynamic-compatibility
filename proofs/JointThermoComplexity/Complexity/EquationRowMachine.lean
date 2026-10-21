module
public import proofs.JointThermoComplexity.Complexity.EquationRowFields

set_option autoImplicit false
@[expose] public section

/-! Actual bounded three-term row reader. On promised rows it preserves zero
terms and source order, stores signed coefficient words and exact monomial
prefixes, and consumes precisely one polynomial-row terminator.
-/

namespace JointThermoComplexity.Complexity.EquationRowMachine
open _root_.Complexity _root_.Complexity.TM BoxBufferState EquationRowControl EquationRowFrame
open HeaderAt (Cursor)
variable {w : ℕ}

theorem branch_hoareTime (p : Ports w) (s t : State) (i : Fin 3) (B time : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (body : TM (w + 1))
    (hbody : body.HoareTime (Logical p s B emitted R) (Logical p t B emitted R) time) :
    (WorkSymbolBranch.machine Γ.one (p.presence i) body (emitBitsTM [])).HoareTime
      (Logical p s B emitted R) (Logical p (if (s.terms i).present then t else s) B emitted R) (time + 2) := by
  cases hi : (s.terms i).present with
  | true =>
    have h := WorkSymbolBranch.yes_hoareTime Γ.one (p.presence i) body (emitBitsTM [])
      s.before s.input emitted t.before t.input emitted (Ready p s B R) (Ready p t B R) time hbody
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      exact ⟨⟨hc, hr⟩, by simpa [hi, Γ.ofBool] using (hr.presence i).2⟩
    · intro inp work out hh
      simpa [hi, Logical] using hh
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one (p.presence i) body (emitBitsTM [])
      s.before s.input emitted s.before s.input emitted (Ready p s B R) (Ready p s B R)
      0 (idle_hoareTime p s B emitted R)
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      rw [(hr.presence i).2, hi]
      decide
    · intro inp work out hh
      simpa [hi, Logical] using hh
    · omega

def endState (s : State) : State :=
  { s with
    before := s.before ++ BooleanMachine.copied s.input
    input := BooleanMachine.suffix s.input
    available := BooleanMachine.accepted s.input }

theorem end_hoareTime (p : Ports w) (s : State) (B : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (SourceBitRead.machine p.loopAvailable p.available).HoareTime
      (Logical p s B emitted R) (Logical p (endState s) B emitted R) 1 := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next => ∀ k, k ≠ p.loopAvailable → k ≠ p.available → next k = work k
  have hC : ∀ a b, (∀ k, k ≠ p.loopAvailable → k ≠ p.available → b k = a k) → C a → C b := by
    intro a b he ha k hi hv
    exact (he k hi hv).trans (ha k hi hv)
  obtain ⟨d, time, ht, hd, hh, hc', hs, hl, hv, _, havail, he⟩ :=
    SourceBitRead.hoareTime p.loopAvailable p.available (p.separate 22 21 (by decide)) s.before s.input emitted C hC
      inp work out ⟨hc, hr.safe, hr.loop_head, hr.available_head, fun _ _ _ => rfl⟩
  refine ⟨d, time, ht, hd, hh, hc', ?_⟩
  refine ⟨hs, ?_, ?_, ?_, ?_, hv, havail, hl, ?_, ?_, hR work d.work (fun k hk => he k (hk _) (hk _)) hr.extra⟩
  · intro i
    simpa only [endState, he _ (p.presence_loop i) (p.presence_available i)] using hr.presence i
  · intro i j
    simpa only [endState, he (p.flag i j) (p.slot_loop i _) (p.slot_available i _)] using hr.flags i j
  · intro i j
    simpa only [endState, he (p.word i j) (p.slot_loop i _) (p.slot_available i _)] using hr.words i j
  · intro i
    simpa only [endState, he (p.coefficient i) (p.slot_loop i 5) (p.slot_available i 5)] using hr.coefficients i
  · simpa only [he p.scratch (p.separate 23 22 (by decide)) (p.separate 23 21 (by decide))] using hr.scratch
  · simpa only [he p.fuel (p.separate 24 22 (by decide)) (p.separate 24 21 (by decide))] using hr.fuel

def termChoice (p : Ports w) (i : Fin 3) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.presence i) (EquationRowFields.bodyMachine p i) (emitBitsTM [])

def termMachine (p : Ports w) (i : Fin 3) : TM (w + 1) :=
  seqTM (SourceBitRead.machine (p.presence i) p.available) (termChoice p i)

def secondMachine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.presence 0) (termMachine p 1) (emitBitsTM [])

def thirdMachine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.presence 0)
    (WorkSymbolBranch.machine Γ.one (p.presence 1) (termMachine p 2) (emitBitsTM [])) (emitBitsTM [])

def closeMachine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.presence 0)
    (WorkSymbolBranch.machine Γ.one (p.presence 1)
      (WorkSymbolBranch.machine Γ.one (p.presence 2)
        (SourceBitRead.machine p.loopAvailable p.available) (emitBitsTM [])) (emitBitsTM [])) (emitBitsTM [])

def machine (p : Ports w) : TM (w + 1) :=
  seqTM (seqTM (seqTM (termMachine p 0) (secondMachine p)) (thirdMachine p)) (closeMachine p)

def termTime (B : ℕ) : ℕ := 13 * B + MonomialPrefixMachine.timeBound B + 45
def timeBound (B : ℕ) : ℕ := 3 * MonomialPrefixMachine.timeBound B + 39 * B + 160

theorem choice_hoareTime (p : Ports w) (s : State) (i : Fin 3) (B : ℕ) (hB : 2 ≤ B)
    (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (termChoice p i).HoareTime (Logical p s B emitted R)
      (Logical p (if (s.terms i).present then body B s i else s) B emitted R)
      (13 * B + MonomialPrefixMachine.timeBound B + 43) :=
  branch_hoareTime p s (body B s i) i B _ emitted R _ (EquationRowFields.body_hoareTime p s i B hB hlen emitted R hR)

theorem term_hoareTime (p : Ports w) (s : State) (i : Fin 3) (B : ℕ) (hB : 2 ≤ B)
    (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (termMachine p i).HoareTime (Logical p s B emitted R) (Logical p (term B s i) B emitted R) (termTime B) := by
  have h := seqTM_hoareTime _ _ (EquationRowFields.read_hoareTime p s i B emitted R hR) (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩)
    (choice_hoareTime p (EquationRowControl.read s i) i B hB ((read_length s i).trans hlen) emitted R hR)
  exact h.mono_bound (by unfold termTime; omega)

theorem second_hoareTime (p : Ports w) (s : State) (B : ℕ) (hB : 2 ≤ B) (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (secondMachine p).HoareTime (Logical p s B emitted R) (Logical p (second B s) B emitted R) (termTime B + 2) :=
  branch_hoareTime p s (term B s 1) 0 B _ emitted R _ (term_hoareTime p s 1 B hB hlen emitted R hR)

theorem third_hoareTime (p : Ports w) (s : State) (B : ℕ) (hB : 2 ≤ B) (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (thirdMachine p).HoareTime (Logical p s B emitted R) (Logical p (third B s) B emitted R) (termTime B + 4) :=
  branch_hoareTime p s (if (s.terms 1).present then term B s 2 else s) 0 B _ emitted R _
    (branch_hoareTime p s (term B s 2) 1 B _ emitted R _ (term_hoareTime p s 2 B hB hlen emitted R hR))

theorem close_hoareTime (p : Ports w) (s : State) (B : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (closeMachine p).HoareTime (Logical p s B emitted R) (Logical p (close s) B emitted R) 7 :=
  branch_hoareTime p s (if (s.terms 1).present then if (s.terms 2).present then endState s else s else s) 0 B _ emitted R _
    (branch_hoareTime p s (if (s.terms 2).present then endState s else s) 1 B _ emitted R _
      (branch_hoareTime p s (endState s) 2 B _ emitted R _ (end_hoareTime p s B emitted R hR)))

theorem hoareTime (p : Ports w) (s : State) (B : ℕ) (hB : 2 ≤ B) (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p s B emitted R) (Logical p (parse B s) B emitted R) (timeBound B) := by
  have h0 := term_hoareTime p s 0 B hB hlen emitted R hR
  have h1 := second_hoareTime p (term B s 0) B hB ((term_length B s 0).trans hlen) emitted R hR
  have h01 := seqTM_hoareTime _ _ h0 (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) h1
  have h2 := third_hoareTime p (second B (term B s 0)) B hB
    ((second_length _ _).trans ((term_length B s 0).trans hlen)) emitted R hR
  have h012 := seqTM_hoareTime _ _ h01 (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) h2
  have h3 := close_hoareTime p (third B (second B (term B s 0))) B emitted R hR
  have h := seqTM_hoareTime _ _ h012 (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) h3
  exact h.mono_bound (by unfold timeBound termTime; omega)

theorem code_monomial_length (row : List (ℤ × List ℕ)) (a : ℤ × List ℕ) (ha : a ∈ row) :
    a.2.length + 1 ≤ (code row).length := by
  induction row with
  | nil => simp at ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with he | he
    · subst b
      have h := MarkedNaturalControl.code_length a.2
      simp only [code, RowWordCodec.marked, List.length_cons, List.length_append]
      omega
    · have h := ih he
      simp only [code, RowWordCodec.marked, List.length_cons, List.length_append] at h ⊢
      omega

theorem encoded_hoareTime (p : Ports w) (s : State) (row : List (ℤ × List ℕ)) (suffix emitted : List Bool) (B : ℕ)
    (hB : 2 ≤ B) (hlen : (code row ++ suffix).length ≤ B) (hr : row.length ≤ 3)
    (ha : ∀ a ∈ row, a.1.natAbs ≤ 5)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p { s with input := code row ++ suffix } B emitted R)
      (Logical p (expected s row suffix) B emitted R) (timeBound B) := by
  have hf : ∀ a ∈ row, a.2.length + 1 ≤ B := by
    intro a hmem
    have h := code_monomial_length row a hmem
    rw [List.length_append] at hlen
    omega
  simpa only [parse_code B s row suffix hr ha hf] using
    hoareTime p { s with input := code row ++ suffix } B hB hlen emitted R hR

theorem code_finite (n : ℕ) (row : SparseInteger.Poly (Fin n)) :
    code (row.map (fun a => (a.1, a.2.map Fin.val))) = (SparsePolynomialCodec.polynomial n).code row := by
  rw [← RowWordCodec.polynomial_finite]
  have hm (indices : List (Fin n)) :
      MarkedNaturalControl.code (indices.map Fin.val) =
        RowWordCodec.monomial (indices.map (fun i => BitCodec.naturalCode i.val)) := by
    simp only [MarkedNaturalControl.code, RowWordCodec.monomial, RowWordCodec.marked_map, id_eq]
  induction row with
  | nil => rfl
  | cons a rest ih =>
    simpa only [List.map_cons, code, RowWordCodec.marked, RowWordCodec.polynomial,
      SparseInteger.relabel, RowWordCodec.term, hm, List.append_assoc] using
      congrArg (fun bits => true :: (BitCodec.integerCode a.1 ++ (MarkedNaturalControl.code (a.2.map Fin.val) ++ bits))) ih

end JointThermoComplexity.Complexity.EquationRowMachine

#print axioms JointThermoComplexity.Complexity.EquationRowMachine.hoareTime
#print axioms JointThermoComplexity.Complexity.EquationRowMachine.encoded_hoareTime
#print axioms JointThermoComplexity.Complexity.EquationRowMachine.code_finite
