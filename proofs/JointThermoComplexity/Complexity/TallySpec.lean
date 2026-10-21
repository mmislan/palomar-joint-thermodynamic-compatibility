module
public import proofs.JointThermoComplexity.Complexity.CountOffset

set_option autoImplicit false
@[expose] public section

/-! Composition rules for supplied actual gate-tally machines, with an unchanged output. -/

namespace JointThermoComplexity.Complexity.TallySpec
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend

variable {w : ℕ}

def State (count : ℕ) (before input emitted : List Bool) (P : (Fin w → Tape) → Prop) :
    _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
  (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧ P (oldWork work)

def Runs (tm : TM (w + 1)) (Env : (Fin w → Tape) → Prop) (word : List Bool) (increment bound : ℕ) : Prop :=
  ∀ (count : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop),
    tm.HoareTime
      (State count before (word ++ tail) emitted (fun work => Env work ∧ R work))
      (State (count + increment) (before ++ word) tail emitted (fun work => Env work ∧ R work)) bound

theorem seq_runs {tmA tmB : TM (w + 1)} {Env : (Fin w → Tape) → Prop}
    {wordA wordB : List Bool} {costA costB timeA timeB : ℕ}
    (hA : Runs tmA Env wordA costA timeA) (hB : Runs tmB Env wordB costB timeB) :
    Runs (seqTM tmA tmB) Env (wordA ++ wordB) (costA + costB) (timeA + 1 + timeB) := by
  intro count before tail emitted R
  have ha := hA count before (wordB ++ tail) emitted R
  have hb := hB (count + costA) (before ++ wordA) tail emitted R
  have hseq := seqTM_hoareTime tmA tmB ha (by
    rintro inp work out ⟨hc, hs, hp, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hz, hr⟩) hb
  exact hseq.consequence
    (fun _ _ _ h => by simpa only [State, List.append_assoc] using h)
    (fun _ _ _ h => by simpa only [State, List.append_assoc, Nat.add_assoc] using h) le_rfl

theorem offset_runs (offset : ℕ) (Env : (Fin w → Tape) → Prop) :
    Runs (CountOffset.machine offset) Env [] offset offset := by
  intro count before tail emitted R inp work out hp
  have hpre : Cursor before tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
      (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧
      Env (oldWork work) ∧ R (oldWork work) := by
    simpa only [State, List.nil_append] using hp
  obtain ⟨e, t, ht, hreach, hhalt, hpost⟩ :=
    CountOffset.hoareTime offset count before tail emitted (fun work => Env work ∧ R work) inp work out hpre
  exact ⟨e, t, ht, hreach, hhalt, by simpa only [State, List.append_nil] using hpost⟩

end JointThermoComplexity.Complexity.TallySpec

#print axioms JointThermoComplexity.Complexity.TallySpec.seq_runs
