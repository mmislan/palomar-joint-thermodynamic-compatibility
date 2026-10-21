module
public import proofs.JointThermoComplexity.Complexity.ScannerSpec

set_option autoImplicit false
@[expose] public section

/-! Add preserved register setup to a proved concrete scanner specification. -/

namespace JointThermoComplexity.Complexity.ScannerEnv
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec FiniteCodec FieldControl

variable {w : ℕ} {α : Type} {A : Codec α}

theorem strengthen {S : Control A} {tm : TM w} {master flag : Fin w}
    {Env Env' : (Fin w → Tape) → Prop} {T : ℕ → ℕ}
    (hscan : Runs S tm master flag Env T)
    (himp : ∀ work, Env' work → Env work)
    (hEnv : ∀ work work', (∀ j, j ≠ master → j ≠ flag → work' j = work j) → Env' work → Env' work') :
    Runs S tm master flag Env' T := by
  intro initial before input emitted R hR inp work out hpre
  rcases hpre with ⟨hc, hf, hm, hv, he, hr⟩
  let RP : (Fin w → Tape) → Prop := fun work => Env' work ∧ R work
  have hRP : ∀ work work', (∀ j, j ≠ master → j ≠ flag → work' j = work j) → RP work → RP work' := by
    rintro work work' h ⟨he', hr'⟩
    exact ⟨hEnv work work' h he', hR work work' h hr'⟩
  obtain ⟨d, t, ht, hreach, hhalt, hc', hf', hm', hv', _, he', hr'⟩ :=
    hscan initial before input emitted RP hRP inp work out ⟨hc, hf, hm, hv, himp work he, he, hr⟩
  exact ⟨d, t, ht, hreach, hhalt, hc', hf', hm', hv', he', hr'⟩

end JointThermoComplexity.Complexity.ScannerEnv

#print axioms JointThermoComplexity.Complexity.ScannerEnv.strengthen
