module
public import proofs.JointThermoComplexity.Complexity.TermSpanBody
public import proofs.JointThermoComplexity.Complexity.FlagBranchNonone

set_option autoImplicit false
@[expose] public section

/-! An actual counted read-only term step, including zero pending and truncated tags. -/

namespace JointThermoComplexity.Complexity.TermSpanStep
open _root_.Complexity _root_.Complexity.TM TermSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

def tokenState (v nodes : ℕ) (before input : List Bool) : TermSpanControl.State :=
  ⟨before ++ SourceTermToken.taken input, SourceTermToken.rest input, v + TermSpanControl.children input, nodes⟩

def presenceMachine (n : ℕ) : TM (n + 7) :=
  FlagBranch.machine (flag n) (TermSpanBody.machine n) (UnaryPredecessor.machine (pending n))
def tokenMachine (n : ℕ) : TM (n + 7) := seqTM (TermSpanTagRead.machine n) (presenceMachine n)
def activeMachine (n : ℕ) : TM (n + 7) := seqTM (tokenMachine n) (UnarySuccessor.machine (nodeCounter n))
def machine (n : ℕ) : TM (n + 7) := FlagBranch.machine (pending n) (activeMachine n) (emitBitsTM [])

theorem after_true (v nodes : ℕ) (before input : List Bool) (ht : SourceTags.accepted input = true) :
    TermSpanBody.after (SourceTermToken.tagBits input) v nodes (before ++ input.take 3) (input.drop 3) =
      tokenState v nodes before input := by
  simp only [TermSpanBody.after, tokenState, SourceTermToken.taken, SourceTermToken.rest,
    TermSpanControl.children, ht, ↓reduceIte, List.append_assoc]

theorem after_false (v nodes : ℕ) (before input : List Bool) (ht : SourceTags.accepted input = false) :
    (⟨before ++ input.take 3, input.drop 3, v, nodes⟩ : TermSpanControl.State) = tokenState v nodes before input := by
  simp only [tokenState, SourceTermToken.taken, SourceTermToken.rest, TermSpanControl.children,
    ht, Bool.false_eq_true, ↓reduceIte, List.append_nil, Nat.add_zero]

theorem presence_hoareTime (L v nodes : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (presenceMachine n).HoareTime
      (fun inp work out => Inv emitted R (TermSpanTagRead.afterTag ⟨before, input, v + 1, nodes⟩) inp work out ∧
        (work (flag n)).read = Γ.ofBool (SourceTags.accepted input) ∧
        SourceTagDispatch.Reads (List.ofFn (tags n)) (SourceTermToken.tagBits input) work)
      (Inv emitted R (tokenState v nodes before input)) (L + 2 * v + 24) := by
  cases ht : SourceTags.accepted input with
  | false =>
    have hd := TermSpanCounter.decrement_hoareTime v nodes (before ++ input.take 3) (input.drop 3) emitted R hR
    have hb := FlagBranchRun.no_hoareTime (flag n) (TermSpanBody.machine n) (UnaryPredecessor.machine (pending n))
      (before ++ input.take 3) (input.drop 3) emitted (before ++ input.take 3) (input.drop 3) emitted
      (Ready (v + 1) nodes R) (Ready v nodes R) (2 * v + 12) hd
    exact hb.consequence (by
      rintro inp work out ⟨hp, hf, _hreads⟩
      exact ⟨hp, by simpa only [ht, Γ.ofBool] using hf⟩) (by
      intro inp work out hp
      change Inv emitted R ⟨before ++ input.take 3, input.drop 3, v, nodes⟩ inp work out at hp
      rw [after_false v nodes before input ht] at hp
      exact hp) (by omega)
  | true =>
    let next := TermSpanBody.after (SourceTermToken.tagBits input) v nodes (before ++ input.take 3) (input.drop 3)
    let P : (Fin (n + 7) → Tape) → Prop := fun work => Ready (v + 1) nodes R work ∧
      SourceTagDispatch.Reads (List.ofFn (tags n)) (SourceTermToken.tagBits input) work
    have hdrop : (input.drop 3).length ≤ L := by rw [List.length_drop]; omega
    have hm := TermSpanBody.hoareTime (SourceTermToken.tagBits input) (by simp [SourceTermToken.tagBits])
      L v nodes (before ++ input.take 3) (input.drop 3) emitted hdrop R hR
    have hb := FlagBranchRun.yes_hoareTime (flag n) (TermSpanBody.machine n) (UnaryPredecessor.machine (pending n))
      (before ++ input.take 3) (input.drop 3) emitted next.before next.input emitted P (Ready next.pending nodes R)
      (L + 2 * v + 22) (hm.consequence (by rintro inp work out ⟨hc, hr, hreads⟩; exact ⟨⟨hc, hr⟩, hreads⟩)
        (fun _ _ _ h => h) le_rfl)
    exact hb.consequence (by
      rintro inp work out ⟨⟨hc, hr⟩, hf, hreads⟩
      exact ⟨⟨hc, hr, hreads⟩, by simpa only [ht, Γ.ofBool] using hf⟩) (by
      intro inp work out hp
      change Inv emitted R next inp work out at hp
      have he : next = tokenState v nodes before input := after_true v nodes before input ht
      rw [he] at hp
      exact hp) (by omega)

theorem token_hoareTime (L v nodes : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (tokenMachine n).HoareTime (Inv emitted R ⟨before, input, v + 1, nodes⟩)
      (Inv emitted R (tokenState v nodes before input)) (L + 2 * v + 33) := by
  have ht := TermSpanTagRead.hoareTime emitted R hR ⟨before, input, v + 1, nodes⟩
  have hp := presence_hoareTime L v nodes before input emitted hlen R hR
  have h := seqTM_hoareTime (TermSpanTagRead.machine n) (presenceMachine n) ht (by
    rintro inp work out ⟨⟨hc, hr⟩, hf, hreads⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hr⟩, hf, hreads⟩) hp
  exact h.mono_bound (by omega)

theorem active_hoareTime (L v nodes : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (activeMachine n).HoareTime (Inv emitted R ⟨before, input, v + 1, nodes⟩)
      (Inv emitted R (TermSpanControl.step ⟨before, input, v + 1, nodes⟩)) (L + 2 * v + 2 * nodes + 40) := by
  have ht := token_hoareTime L v nodes before input emitted hlen R hR
  have hn := TermSpanCounter.increment_hoareTime emitted R hR (tokenState v nodes before input)
  have h := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ ht hn
  exact h.mono_bound (by
    change L + 2 * v + 33 + 1 + (2 * nodes + 6) ≤ L + 2 * v + 2 * nodes + 40
    omega)

theorem hoareTime (L : ℕ) (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R)
    (s : TermSpanControl.State) (hlen : s.input.length ≤ L) :
    (machine n).HoareTime (Inv emitted R s) (Inv emitted R (TermSpanControl.step s))
      (L + 2 * s.pending + 2 * s.nodes + 42) := by
  rcases s with ⟨before, input, count, nodes⟩
  cases count with
  | zero =>
    have hn := noop_hoareTime emitted R (⟨before, input, 0, nodes⟩ : TermSpanControl.State)
    have hb := FlagBranchNonone.hoareTime (pending n) (activeMachine n) (emitBitsTM [])
      before input emitted before input emitted (Ready 0 nodes R) (Ready 0 nodes R) 0 hn
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      have hv := hr.counter.read_eq
      change (work (pending n)).read = Γ.blank at hv
      rw [hv]
      decide) (fun _ _ _ h => h) (by omega)
  | succ v =>
    let next := TermSpanControl.step ⟨before, input, v + 1, nodes⟩
    have ha := active_hoareTime L v nodes before input emitted hlen R hR
    have hb := FlagBranchRun.yes_hoareTime (pending n) (activeMachine n) (emitBitsTM [])
      before input emitted next.before next.input emitted (Ready (v + 1) nodes R) (Ready next.pending next.nodes R)
      (L + 2 * v + 2 * nodes + 40) ha
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      have hv := hr.counter.read_eq
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv)
      (fun _ _ _ h => h) (by
        change L + 2 * v + 2 * nodes + 40 + 1 ≤ L + 2 * (v + 1) + 2 * nodes + 42
        omega)

theorem bounded_hoareTime (L P N : ℕ) (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R)
    (s : TermSpanControl.State) (hlen : s.input.length ≤ L) (hp : s.pending ≤ P) (hn : s.nodes ≤ N) :
    (machine n).HoareTime (Inv emitted R s) (Inv emitted R (TermSpanControl.step s)) (L + 2 * P + 2 * N + 42) :=
  (hoareTime L emitted R hR s hlen).mono_bound (by omega)

end JointThermoComplexity.Complexity.TermSpanStep

#print axioms JointThermoComplexity.Complexity.TermSpanStep.hoareTime
#print axioms JointThermoComplexity.Complexity.TermSpanStep.bounded_hoareTime
