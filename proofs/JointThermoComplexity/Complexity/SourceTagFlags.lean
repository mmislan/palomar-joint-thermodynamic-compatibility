module
public import proofs.JointThermoComplexity.Complexity.SourceBitRead
public import proofs.JointThermoComplexity.Complexity.SourceTagScanner

set_option autoImplicit false
@[expose] public section

/-! Fixed-width source headers are read into separate named work flags.
The machine is total on truncated words and never appends formula output. -/

namespace JointThermoComplexity.Complexity.SourceTagFlags
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def status (count : ℕ) (initial : Bool) (input : List Bool) : Bool :=
  match count with
  | 0 => initial
  | k + 1 => decide (k + 1 ≤ input.length)

def machine : {count : ℕ} → (Fin count → Fin w) → Fin w → TM w
  | 0, _, _ => emitBitsTM []
  | _count + 1, ports, flag =>
    seqTM (SourceBitRead.machine (ports 0) flag) (machine (fun i => ports i.succ) flag)

theorem prefix_next (count : ℕ) (input : List Bool) :
    BooleanMachine.copied input ++ (BooleanMachine.suffix input).take count = input.take (count + 1) := by
  cases input with
  | nil => simp [BooleanMachine.copied, BooleanMachine.suffix]
  | cons b input => rfl

theorem suffix_next (count : ℕ) (input : List Bool) :
    (BooleanMachine.suffix input).drop count = input.drop (count + 1) := by
  cases input with
  | nil => simp [BooleanMachine.suffix]
  | cons b input => rfl

theorem status_next (count : ℕ) (initial : Bool) (input : List Bool) :
    status count (BooleanMachine.accepted input) (BooleanMachine.suffix input) = status (count + 1) initial input := by
  cases count with
  | zero =>
    change BooleanMachine.accepted input = decide (1 ≤ input.length)
    rw [BooleanVector.accepted_length]
    have he : 0 < input.length ↔ 1 ≤ input.length := by omega
    simp only [he]
  | succ count =>
    change decide (count + 1 ≤ (BooleanMachine.suffix input).length) = decide (count + 1 + 1 ≤ input.length)
    rw [BooleanVector.suffix_eq_drop, List.length_drop]
    have he : count + 1 ≤ input.length - 1 ↔ count + 1 + 1 ≤ input.length := by omega
    simp only [he]

theorem hoareTime (count : ℕ) (ports : Fin count → Fin w) (hinj : Function.Injective ports)
    (flag : Fin w) (hsep : ∀ i, ports i ≠ flag) (initial : Bool)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, (∀ i, j ≠ ports i) → j ≠ flag → work' j = work j) → R work → R work') :
    (machine ports flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ i, (work (ports i)).head = 1) ∧ (work flag).head = 1 ∧ (work flag).read = Γ.ofBool initial ∧ R work)
      (fun inp work out => Cursor (before ++ input.take count) (input.drop count) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (∀ i, (work (ports i)).head = 1) ∧ (work flag).head = 1 ∧
        (work flag).read = Γ.ofBool (status count initial input) ∧
        (∀ i, (work (ports i)).read = Γ.ofBool (SourceBitRead.value (input.drop i.val))) ∧ R work) (2 * count) := by
  induction count generalizing before input initial R with
  | zero =>
    rintro inp work out ⟨hc, hs, hh, hfh, hfv, hr⟩
    refine ⟨⟨(machine ports flag).qhalt, inp, work, out⟩, 0, le_rfl, .zero, rfl, ?_, hs, hh, hfh, hfv, ?_, hr⟩
    · simpa only [List.take_zero, List.drop_zero, List.append_nil] using hc
    · intro i; exact Fin.elim0 i
  | succ count ih =>
    let tailPorts : Fin count → Fin w := fun i => ports i.succ
    have htail : Function.Injective tailPorts := by
      intro i j he
      have hv := congrArg Fin.val (hinj he)
      apply Fin.ext
      change i.val + 1 = j.val + 1 at hv
      omega
    have hfirst (i : Fin count) : ports 0 ≠ tailPorts i := by
      intro he
      have hv := congrArg Fin.val (hinj he)
      change 0 = i.val + 1 at hv
      omega
    let R₀ : (Fin w → Tape) → Prop := fun work => (∀ i, (work (tailPorts i)).head = 1) ∧ R work
    have hR₀ : ∀ work work', (∀ j, j ≠ ports 0 → j ≠ flag → work' j = work j) → R₀ work → R₀ work' := by
      rintro work work' hw ⟨hh, hr⟩
      refine ⟨?_, hR work work' (fun j hj hf => hw j (hj 0) hf) hr⟩
      intro i
      simpa only [hw (tailPorts i) (hfirst i).symm (hsep i.succ)] using hh i
    let R₁ : (Fin w → Tape) → Prop := fun work => (work (ports 0)).head = 1 ∧
      (work (ports 0)).read = Γ.ofBool (SourceBitRead.value input) ∧ R work
    have hR₁ : ∀ work work', (∀ j, (∀ i, j ≠ tailPorts i) → j ≠ flag → work' j = work j) → R₁ work → R₁ work' := by
      rintro work work' hw ⟨hh, hv, hr⟩
      have he := hw (ports 0) hfirst (hsep 0)
      exact ⟨by simpa only [he] using hh, by simpa only [he] using hv,
        hR work work' (fun j hj hf => hw j (fun i => hj i.succ) hf) hr⟩
    have h₀ := SourceBitRead.hoareTime (ports 0) flag (hsep 0) before input emitted R₀ hR₀
    have h₁ := ih tailPorts htail (fun i => hsep i.succ) (BooleanMachine.accepted input)
      (before ++ BooleanMachine.copied input) (BooleanMachine.suffix input) R₁ hR₁
    have hall := seqTM_hoareTime (SourceBitRead.machine (ports 0) flag) (machine tailPorts flag) h₀ (by
      rintro inp work out ⟨hc, hs, hh, hfh, hv, hfv, hstate⟩
      obtain ⟨hip, hwp, hop⟩ := hc.phase
      rw [hip, hwp, hop]
      exact ⟨hc, hs, hstate.1, hfh, hfv, hh, hv, hstate.2⟩) h₁
    exact hall.consequence (by
      rintro inp work out ⟨hc, hs, hh, hfh, _hv, hr⟩
      exact ⟨hc, hs, hh 0, hfh, (fun i => hh i.succ), hr⟩) (by
      rintro inp work out ⟨hc, hs, hh, hfh, hfv, hdata, hstate⟩
      refine ⟨?_, hs, ?_, hfh, ?_, ?_, hstate.2.2⟩
      · simpa only [List.append_assoc, prefix_next, suffix_next] using hc
      · exact Fin.cases hstate.1 hh
      · simpa only [status_next count initial input] using hfv
      · refine Fin.cases ?_ (fun i => ?_)
        · simpa only [Fin.val_zero, List.drop_zero] using hstate.2.1
        · simpa only [tailPorts, Fin.val_succ, suffix_next] using hdata i) (by omega)

theorem tag_hoareTime (ports : Fin 3 → Fin w) (hinj : Function.Injective ports)
    (flag : Fin w) (hsep : ∀ i, ports i ≠ flag) (initial : Bool)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, (∀ i, j ≠ ports i) → j ≠ flag → work' j = work j) → R work → R work') :
    (machine ports flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ i, (work (ports i)).head = 1) ∧ (work flag).head = 1 ∧ (work flag).read = Γ.ofBool initial ∧ R work)
      (fun inp work out => Cursor (before ++ input.take 3) (input.drop 3) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (∀ i, (work (ports i)).head = 1) ∧ (work flag).head = 1 ∧
        (work flag).read = Γ.ofBool (SourceTags.accepted input) ∧
        (∀ i, (work (ports i)).read = Γ.ofBool (SourceBitRead.value (input.drop i.val))) ∧ R work) 6 :=
  hoareTime 3 ports hinj flag hsep initial before input emitted R hR

end JointThermoComplexity.Complexity.SourceTagFlags

#print axioms JointThermoComplexity.Complexity.SourceTagFlags.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTagFlags.tag_hoareTime
