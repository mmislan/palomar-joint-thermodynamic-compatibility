module
public import proofs.JointThermoComplexity.Complexity.EquationRowControl
public import proofs.JointThermoComplexity.Complexity.MonomialPrefixMachine

set_option autoImplicit false
@[expose] public section

/-! Constant-size row storage and its injective work-tape embedding. Three
six-port term slots share four parser auxiliaries and keep three presence flags.
-/

namespace JointThermoComplexity.Complexity.EquationRowFrame
open _root_.Complexity _root_.Complexity.TM BoxBufferState EquationRowControl
open HeaderAt (Cursor)
variable {w : ℕ}

structure Ports (w : ℕ) where
  index : Fin 25 → Fin (w + 1)
  injective : Function.Injective index

namespace Ports
def slotIndex (i : Fin 3) (j : Fin 6) : Fin 25 := ⟨6 * i.val + j.val, by omega⟩
def presenceIndex (i : Fin 3) : Fin 25 := ⟨18 + i.val, by omega⟩
def slot (p : Ports w) (i : Fin 3) (j : Fin 6) : Fin (w + 1) := p.index (slotIndex i j)
def flag (p : Ports w) (i j : Fin 3) : Fin (w + 1) := p.slot i ⟨j.val, by omega⟩
def word (p : Ports w) (i : Fin 3) (j : Fin 2) : Fin (w + 1) := p.slot i ⟨3 + j.val, by omega⟩
def coefficient (p : Ports w) (i : Fin 3) : Fin (w + 1) := p.slot i 5
def presence (p : Ports w) (i : Fin 3) : Fin (w + 1) := p.index (presenceIndex i)
def available (p : Ports w) : Fin (w + 1) := p.index 21
def loopAvailable (p : Ports w) : Fin (w + 1) := p.index 22
def scratch (p : Ports w) : Fin (w + 1) := p.index 23
def fuel (p : Ports w) : Fin (w + 1) := p.index 24

theorem separate (p : Ports w) (a b : Fin 25) (h : a.val ≠ b.val) : p.index a ≠ p.index b :=
  p.injective.ne (Fin.ne_of_val_ne h)

theorem slot_ne (p : Ports w) {i k : Fin 3} {j l : Fin 6} (h : i ≠ k ∨ j ≠ l) : p.slot i j ≠ p.slot k l := by
  apply p.separate
  have hi : i.val ≠ k.val ∨ j.val ≠ l.val := h.imp (fun he hv => he (Fin.ext hv)) (fun he hv => he (Fin.ext hv))
  dsimp [slotIndex]
  omega

theorem slot_presence (p : Ports w) (i : Fin 3) (j : Fin 6) (k : Fin 3) : p.slot i j ≠ p.presence k :=
  p.separate _ _ (by dsimp [slotIndex, presenceIndex]; omega)

theorem slot_available (p : Ports w) (i : Fin 3) (j : Fin 6) : p.slot i j ≠ p.available :=
  p.separate _ _ (by dsimp [slotIndex]; omega)

theorem slot_loop (p : Ports w) (i : Fin 3) (j : Fin 6) : p.slot i j ≠ p.loopAvailable :=
  p.separate _ _ (by dsimp [slotIndex]; omega)

theorem slot_scratch (p : Ports w) (i : Fin 3) (j : Fin 6) : p.slot i j ≠ p.scratch :=
  p.separate _ _ (by dsimp [slotIndex]; omega)

theorem slot_fuel (p : Ports w) (i : Fin 3) (j : Fin 6) : p.slot i j ≠ p.fuel :=
  p.separate _ _ (by dsimp [slotIndex]; omega)

theorem presence_ne (p : Ports w) {i k : Fin 3} (h : i ≠ k) : p.presence i ≠ p.presence k := by
  apply p.separate
  have hv : i.val ≠ k.val := fun he => h (Fin.ext he)
  dsimp [presenceIndex]
  omega

theorem presence_available (p : Ports w) (i : Fin 3) : p.presence i ≠ p.available :=
  p.separate _ _ (by dsimp [presenceIndex]; omega)

theorem presence_loop (p : Ports w) (i : Fin 3) : p.presence i ≠ p.loopAvailable :=
  p.separate _ _ (by dsimp [presenceIndex]; omega)

def prefixIndex (i : Fin 3) : Fin 9 → Fin 25 :=
  ![slotIndex i 0, slotIndex i 1, slotIndex i 2, 21, 22, slotIndex i 3, slotIndex i 4, 23, 24]

theorem prefixIndex_injective (i : Fin 3) : Function.Injective (prefixIndex i) := by
  intro a b h
  apply Fin.ext
  have he := congrArg (fun k : Fin 25 => k.val) h
  fin_cases a <;> fin_cases b <;> dsimp [prefixIndex, slotIndex] at he ⊢ <;> omega

def prefixPorts (p : Ports w) (i : Fin 3) : MonomialPrefixMachine.Ports w :=
  ⟨fun a => p.index (prefixIndex i a), p.injective.comp (prefixIndex_injective i)⟩

theorem prefix_flag (p : Ports w) (i j : Fin 3) : (p.prefixPorts i).flag j = p.flag i j := by
  fin_cases j <;> rfl

theorem prefix_word (p : Ports w) (i : Fin 3) (j : Fin 2) : (p.prefixPorts i).word j = p.word i j := by
  fin_cases j <;> rfl

theorem outside_prefix (p : Ports w) (i : Fin 3) (a : Fin 25) (ha : a.val < 21)
    (hi : a.val < 6 * i.val ∨ 6 * i.val + 5 ≤ a.val) (b : Fin 9) : p.index a ≠ (p.prefixPorts i).index b := by
  apply p.separate
  fin_cases b <;> dsimp [prefixIndex, slotIndex] <;> omega

theorem presence_prefix (p : Ports w) (i k : Fin 3) (b : Fin 9) : p.presence k ≠ (p.prefixPorts i).index b :=
  p.outside_prefix i (presenceIndex k) (by dsimp [presenceIndex]; omega) (by dsimp [presenceIndex]; omega) b

theorem coefficient_prefix (p : Ports w) (i k : Fin 3) (b : Fin 9) : p.coefficient k ≠ (p.prefixPorts i).index b :=
  p.outside_prefix i (slotIndex k 5) (by dsimp [slotIndex]; omega) (by dsimp [slotIndex]; omega) b

theorem other_slot_prefix (p : Ports w) (i k : Fin 3) (j : Fin 6) (hk : k ≠ i) (b : Fin 9) :
    p.slot k j ≠ (p.prefixPorts i).index b := by
  have hv : k.val ≠ i.val := fun he => hk (Fin.ext he)
  exact p.outside_prefix i (slotIndex k j) (by dsimp [slotIndex]; omega) (by dsimp [slotIndex]; omega) b
end Ports

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ k, (∀ a, k ≠ p.index a) → work' k = work k) → R work → R work'

def Presence (p : Ports w) (s : State) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ i, (work (p.presence i)).head = 1 ∧ (work (p.presence i)).read = Γ.ofBool (s.terms i).present

def Flags (p : Ports w) (s : State) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ i j, (work (p.flag i j)).head = 1 ∧ (work (p.flag i j)).read = Γ.ofBool ((s.terms i).flags j)

def Words (p : Ports w) (s : State) (B : ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ i j, (work (p.word i j)).HasBinaryString ((s.terms i).words j) ∧
    (work (p.word i j)).cells 0 = Γ.start ∧ ((s.terms i).words j).length ≤ 4 * B

def Coefficients (p : Ports w) (s : State) (B : ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ i, (work (p.coefficient i)).HasBinaryString (s.terms i).coefficient ∧
    (work (p.coefficient i)).cells 0 = Γ.start ∧ (s.terms i).coefficient.length ≤ 4 * B

structure Ready (p : Ports w) (s : State) (B : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop where
  safe : ∀ k, Parked (work k)
  presence : Presence p s work
  flags : Flags p s work
  words : Words p s B work
  coefficients : Coefficients p s B work
  available_head : (work p.available).head = 1
  available_read : (work p.available).read = Γ.ofBool s.available
  loop_head : (work p.loopAvailable).head = 1
  scratch : Reusable B (work p.scratch)
  fuel : IsReg B (work p.fuel)
  extra : R work

def Logical (p : Ports w) (s : State) (B : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s B R work

theorem idle_hoareTime (p : Ports w) (s : State) (B : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM (n := w + 1) []).HoareTime (Logical p s B emitted R) (Logical p s B emitted R) 0 :=
  (FixedOutput.hoareTime [] s.before s.input emitted (Ready p s B R)).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.safe, hr⟩)
    (fun _ _ _ ⟨hc, _, hr⟩ => by simpa only [List.append_nil, Logical] using And.intro hc hr) le_rfl

end JointThermoComplexity.Complexity.EquationRowFrame

#print axioms JointThermoComplexity.Complexity.EquationRowFrame.Ports.prefixIndex_injective
#print axioms JointThermoComplexity.Complexity.EquationRowFrame.Ports.outside_prefix
#print axioms JointThermoComplexity.Complexity.EquationRowFrame.idle_hoareTime
