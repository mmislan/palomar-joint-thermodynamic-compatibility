module
public import proofs.JointThermoComplexity.Complexity.RecordControl
public import proofs.JointThermoComplexity.Complexity.NaturalField

set_option autoImplicit false
@[expose] public section

/-!
# Compositional specifications for concrete record scanners

`Runs` is a Hoare specification for a supplied actual TM. Its instances must be
proved from checked transitions; it supplies no complexity-class assumption.
The shared environment describes retained registers, while the frame predicate
may inspect every tape other than the two status tapes.
-/

namespace JointThermoComplexity.Complexity.ScannerSpec
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt FiniteCodec FieldControl

variable {w : ℕ} {α β : Type} {A : Codec α} {B : Codec β}

def Runs (S : Control A) (tm : TM w) (master flag : Fin w)
    (Env : (Fin w → Tape) → Prop) (T : ℕ → ℕ) : Prop :=
  ∀ (initial : Bool) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop),
    (∀ work work', (∀ j, j ≠ master → j ≠ flag → work' j = work j) → R work → R work') →
    tm.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work flag).head = 1 ∧ (work master).head = 1 ∧ (work master).read = Γ.ofBool initial ∧ Env work ∧ R work)
      (fun inp work out => Cursor (before ++ S.taken input) (S.rest input) (emitted ++ S.taken input) inp work out ∧
        (work flag).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool (initial && S.valid input) ∧ Env work ∧ R work)
      (T input.length)

theorem product_runs {SA : Control A} {SB : Control B} {tmA tmB : TM w}
    {master flag : Fin w} {Env : (Fin w → Tape) → Prop} {TA TB : ℕ → ℕ}
    (hA : Runs SA tmA master flag Env TA) (hB : Runs SB tmB master flag Env TB) (hmono : Monotone TB) :
    Runs (RecordControl.product SA SB) (seqTM tmA tmB) master flag Env (fun L => TA L + 1 + TB L) := by
  intro initial before input emitted R hR
  have ha := hA initial before input emitted R hR
  have hb := hB (initial && SA.valid input) (before ++ SA.taken input) (SA.rest input) (emitted ++ SA.taken input) R hR
  have hlen : (SA.rest input).length ≤ input.length := by
    have hs := congrArg List.length (SA.split input)
    simp only [List.length_append] at hs
    omega
  have hb' := HoareTime.mono_bound hb (hmono hlen)
  have hseq := seqTM_hoareTime tmA tmB ha (by
    rintro inp work out ⟨hc, hf, hm, hv, he, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hf, hm, hv, he, hr⟩) hb'
  apply HoareTime.strengthen_post hseq
  rintro inp work out ⟨hc, hf, hm, hv, he, hr⟩
  refine ⟨?_, hf, hm, ?_, he, hr⟩
  · simpa only [RecordControl.product, List.append_assoc] using hc
  · simpa only [RecordControl.product, Bool.and_assoc] using hv

theorem transport_runs {S : Control A} {tm : TM w} {master flag : Fin w}
    {Env : (Fin w → Tape) → Prop} {T : ℕ → ℕ} (e : α ≃ β) (h : Runs S tm master flag Env T) :
    Runs (RecordControl.transport S e) tm master flag Env T := h

end JointThermoComplexity.Complexity.ScannerSpec

#print axioms JointThermoComplexity.Complexity.ScannerSpec.product_runs
