module
public import proofs.JointThermoComplexity.Complexity.SourceTermCountReset

set_option autoImplicit false
@[expose] public section

/-! Actual reusable two-term parsing with an input-prefix independent state. -/

namespace JointThermoComplexity.Complexity.SourceTermPair
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField SourceTermLoopState
open SourceTermLoopBody (Inv)
variable {n : ℕ}

def withPrefix (before : List Bool) (s : State) : State := {s with before := before ++ s.before}

theorem step_prefix (arity : ℕ) (before : List Bool) (s : State) :
    step arity (withPrefix before s) = withPrefix before (step arity s) := by
  cases s with
  | mk old input pending valid =>
    cases valid <;> cases pending <;> simp [SourceTermLoopState.step, withPrefix, List.append_assoc]

theorem run_prefix (arity count : ℕ) (before : List Bool) (s : State) :
    run arity count (withPrefix before s) = withPrefix before (run arity count s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => simpa only [SourceTermLoopState.run, step_prefix] using ih (step arity s)

theorem final_prefix (arity count : ℕ) (before : List Bool) (s : State) :
    SourceTermForest.finalState arity count (withPrefix before s) = withPrefix before (SourceTermForest.finalState arity count s) := by
  unfold SourceTermForest.finalState
  rw [run_prefix]
  rfl

def state (arity L : ℕ) (input : List Bool) : State := SourceTermForest.finalState arity L ⟨[], input, 2, true⟩

theorem entry_state (arity L : ℕ) (before input : List Bool) :
    SourceTermForest.finalState arity L ⟨before, input, 2, true⟩ = withPrefix before (state arity L input) := by
  simpa only [withPrefix, List.append_nil, state] using final_prefix arity L before ⟨[], input, 2, true⟩

def machine (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1)) : TM (n + 2) :=
  seqTM (SourceTermCountReset.machine pending.castSucc) (SourceTermForest.machine ports fuel pending left right)

def timeBound (L old : ℕ) : ℕ := 2 * old + 22 + SourceTermForest.timeBound L 2 L

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right)
    (hfu : SourcePendingFrame.Separate ports fuel left right) (hfp : fuel ≠ pending)
    (L arity old : ℕ) (ha : arity.bits.length ≤ L) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ k, j ≠ ports k) → j ≠ pending → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine ports fuel pending left right).HoareTime
      (fun inp work out => Inv ports pending left right L arity emitted R ⟨before, input, old, true⟩ inp work out ∧
        IsReg L (work fuel.castSucc))
      (fun inp work out => Inv ports pending left right L arity emitted R (withPrefix before (state arity L input)) inp work out ∧
        IsReg L (work fuel.castSucc)) (timeBound L old) := by
  let RF : (Fin (n + 1) → Tape) → Prop := fun work => IsReg L (work fuel) ∧ R work
  have hRF : ∀ work work', (∀ j, j ≠ pending → work' j = work j) → RF work → RF work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw fuel hfp] using hf, hR _ _ (fun j _ _ _ _ hj _ => hw j hj) hr⟩
  have hreset := SourceTermCountReset.ready_hoareTime ports pending left right hp L arity old true before input emitted RF hRF
  have hforest := SourceTermForest.hoareTime ports fuel pending left right hs sep hp hfu hfp L arity L ha emitted R
    ⟨before, input, 2, true⟩ hlen hR
  have hfull := seqTM_hoareTime (SourceTermCountReset.machine pending.castSucc)
    (SourceTermForest.machine ports fuel pending left right) hreset (by
      rintro inp work out ⟨hc, hr, hv, hh, hf⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame.2⟩,
        hv, hh, hf⟩, hr.frame.1⟩) hforest
  exact hfull.consequence (by
    rintro inp work out ⟨⟨hc, hr, hv, hh, hf⟩, hFuel⟩
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hFuel, hr.frame⟩,
      hv, hh, hf⟩) (by
      intro inp work out h
      simpa only [entry_state] using h) (by
        change (2 * old + 21) + 1 + SourceTermForest.timeBound L 2 L ≤ timeBound L old
        unfold timeBound
        omega)

theorem timeBound_eq (L old : ℕ) : timeBound L old = 34 * L ^ 2 + 91 * L + 2 * old + 27 := by
  unfold timeBound SourceTermForest.timeBound SourceTermLoop.timeBound SourceTermLoop.bodyBound
  ring1

theorem bounded_timeBound (L old : ℕ) (hold : old ≤ L + 2) : timeBound L old ≤ 34 * L ^ 2 + 93 * L + 31 := by
  rw [timeBound_eq]
  omega

theorem state_bounds (arity L : ℕ) (input : List Bool) : (state arity L input).pending ≤ 2 + L ∧
    (state arity L input).input.length ≤ input.length ∧ (state arity L input).before ++ (state arity L input).input = input := by
  have h := run_bounds arity L ⟨[], input, 2, true⟩
  simpa only [state, SourceTermForest.finalState, SourceTermFinish.finishState, List.nil_append] using h

theorem status_criterion (arity L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    (state arity L input).valid = true ↔ ∃ a b : RealSyntax.Term arity,
      input = a.code ++ b.code ++ (state arity L input).input := by
  have h := SourceTermForest.status_criterion arity L 2 [] input
  constructor
  · intro hv
    obtain ⟨ts, hcount, _hn, hcode⟩ := h.mp hv
    cases ts with
    | nil => simp at hcount
    | cons a ts =>
      cases ts with
      | nil => simp at hcount
      | cons b ts =>
        have ht : ts = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hcount; omega)
        subst ts
        exact ⟨a, b, by simpa only [state, SourceTermScan.forestCode_cons, SourceTermScan.forestCode_nil, List.append_nil] using hcode⟩
  · rintro ⟨a, b, hcode⟩
    apply h.mpr
    refine ⟨[a, b], rfl, ?_, ?_⟩
    · have hn := SourceTermScan.forestNodes_le_code_length [a, b]
      have he := congrArg List.length hcode
      simp only [SourceTermScan.forestCode_cons, SourceTermScan.forestCode_nil, List.append_nil, List.length_append] at hn
      rw [List.length_append, List.length_append] at he
      omega
    · simpa only [state, SourceTermScan.forestCode_cons, SourceTermScan.forestCode_nil, List.append_nil] using hcode

theorem code_result (arity L : ℕ) (a b : RealSyntax.Term arity) (suffix : List Bool)
    (hlen : (a.code ++ b.code ++ suffix).length ≤ L) :
    (state arity L (a.code ++ b.code ++ suffix)).input = suffix ∧
      (state arity L (a.code ++ b.code ++ suffix)).valid = true := by
  have hn := SourceTermScan.forestNodes_le_code_length [a, b]
  have hnodes : SourceTermScan.forestNodes [a, b] ≤ L := by
    simp only [SourceTermScan.forestCode_cons, SourceTermScan.forestCode_nil, List.append_nil, List.length_append] at hn
    rw [List.length_append, List.length_append] at hlen
    omega
  have h := SourceTermForest.code_result arity L [a, b] [] suffix hnodes
  simpa only [state, SourceTermScan.forestCode_cons, SourceTermScan.forestCode_nil, List.append_nil,
    List.length_cons, List.length_nil] using h

theorem status_prefix_iff (arity L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    (state arity L input).valid = true ↔ ∃ a b : RealSyntax.Term arity, ∃ suffix,
      input = a.code ++ b.code ++ suffix := by
  constructor
  · intro h
    obtain ⟨a, b, he⟩ := (status_criterion arity L input hlen).mp h
    exact ⟨a, b, (state arity L input).input, he⟩
  · rintro ⟨a, b, suffix, rfl⟩
    exact (code_result arity L a b suffix hlen).2

theorem status_sound (arity L : ℕ) (input : List Bool) (hlen : input.length ≤ L)
    (h : (state arity L input).valid = true) :
    ∃ a b : RealSyntax.Term arity, (state arity L input).before = a.code ++ b.code ∧
      input = a.code ++ b.code ++ (state arity L input).input := by
  obtain ⟨a, b, he⟩ := (status_criterion arity L input hlen).mp h
  have hw := (state_bounds arity L input).2.2
  have hp : (state arity L input).before = a.code ++ b.code :=
    List.append_cancel_right (by simpa only [List.append_assoc] using hw.trans he)
  exact ⟨a, b, hp, he⟩

end JointThermoComplexity.Complexity.SourceTermPair

#print axioms JointThermoComplexity.Complexity.SourceTermPair.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermPair.timeBound_eq
#print axioms JointThermoComplexity.Complexity.SourceTermPair.status_criterion
#print axioms JointThermoComplexity.Complexity.SourceTermPair.code_result
#print axioms JointThermoComplexity.Complexity.SourceTermPair.status_sound
