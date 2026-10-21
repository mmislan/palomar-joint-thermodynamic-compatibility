module
public import proofs.JointThermoComplexity.Complexity.SourceTermToken

set_option autoImplicit false
@[expose] public section

/-! Set a fixed finite vector of work flags without consuming input or output. -/

namespace JointThermoComplexity.Complexity.FlagInitialization
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def machine : {count : ℕ} → (Fin count → Fin w) → (Fin count → Bool) → TM w
  | 0, _, _ => emitBitsTM []
  | _count + 1, ports, values => seqTM (SourceTermToken.setStatus (ports 0) (values 0))
      (machine (fun i => ports i.succ) (fun i => values i.succ))

theorem hoareTime (count : ℕ) (ports : Fin count → Fin w) (hinj : Function.Injective ports)
    (values : Fin count → Bool) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, (∀ i, j ≠ ports i) → next j = work j) → R work → R next) :
    (machine ports values).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ i, (work (ports i)).head = 1) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ i, (work (ports i)).head = 1) ∧ (∀ i, (work (ports i)).read = Γ.ofBool (values i)) ∧ R work)
      (2 * count) := by
  induction count generalizing R with
  | zero =>
    rintro inp work out ⟨hc, hs, hh, hr⟩
    exact ⟨⟨(machine ports values).qhalt, inp, work, out⟩, 0, le_rfl, .zero, rfl,
      hc, hs, hh, (fun i => Fin.elim0 i), hr⟩
  | succ count ih =>
    let tailPorts : Fin count → Fin w := fun i => ports i.succ
    let tailValues : Fin count → Bool := fun i => values i.succ
    have htail : Function.Injective tailPorts := fun i j he => Fin.succ_injective _ (hinj he)
    have hfirst : ∀ i, ports 0 ≠ tailPorts i := by
      intro i he
      have hv := congrArg Fin.val (hinj he)
      change 0 = i.val + 1 at hv
      omega
    let R₀ : (Fin w → Tape) → Prop := fun work => (∀ i, (work (tailPorts i)).head = 1) ∧ R work
    have hR₀ : ∀ work next, (∀ j, j ≠ ports 0 → next j = work j) → R₀ work → R₀ next := by
      rintro work next he ⟨hh, hr⟩
      exact ⟨fun i => by simpa only [he _ (hfirst i).symm] using hh i,
        hR work next (fun j hj => he j (hj 0)) hr⟩
    let R₁ : (Fin w → Tape) → Prop := fun work => (work (ports 0)).head = 1 ∧
      (work (ports 0)).read = Γ.ofBool (values 0) ∧ R work
    have hR₁ : ∀ work next, (∀ j, (∀ i, j ≠ tailPorts i) → next j = work j) → R₁ work → R₁ next := by
      rintro work next he ⟨hh, hv, hr⟩
      exact ⟨by simpa only [he _ hfirst] using hh, by simpa only [he _ hfirst] using hv,
        hR work next (fun j hj => he j (fun i => hj i.succ)) hr⟩
    have h0 := SourceTermToken.setStatus_hoareTime (ports 0) (values 0) before input emitted R₀ hR₀
    have h1 := ih tailPorts htail tailValues R₁ hR₁
    have hall := seqTM_hoareTime _ _ h0 (by
      rintro inp work out ⟨hc, hs, hh, hv, ht, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, ht, hh, hv, hr⟩) h1
    exact hall.consequence (by
      rintro inp work out ⟨hc, hs, hh, hr⟩
      exact ⟨hc, hs, hh 0, (fun i => hh i.succ), hr⟩) (by
      rintro inp work out ⟨hc, hs, hh, hv, h0h, h0v, hr⟩
      exact ⟨hc, hs, Fin.cases h0h hh, Fin.cases h0v hv, hr⟩) (by omega)

end JointThermoComplexity.Complexity.FlagInitialization

#print axioms JointThermoComplexity.Complexity.FlagInitialization.hoareTime
