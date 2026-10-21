module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementFramed
public import proofs.JointThermoComplexity.Complexity.StrictGeneratedBytes

set_option autoImplicit false
@[expose] public section

/-! A fixed generated-template emission followed by two actual binary address
increments. Both address buffers and an arbitrary external frame are tracked.
-/

namespace JointThermoComplexity.Complexity.GeneratedEnergyStep
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun StrictGeneratedTemplates
open HeaderAt (Cursor)
variable {w : ℕ}

structure Ports (w : ℕ) where
  index : Fin 2 → Fin w
  injective : Function.Injective index

def Stable (p : Ports w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ k, (∀ i, k ≠ p.index i) → next k = work k) → R work → R next

structure Ready (p : Ports w) (values : Fin 2 → ℕ) (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop where
  safe : ∀ k, Parked (work k)
  registers : ∀ i, Register (values i) (work (p.index i))
  extra : R work

def Logical (p : Ports w) (values : Fin 2 → ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input emitted inp work out ∧ Ready p values R work

def advance (values : Fin 2 → ℕ) : Fin 2 → ℕ := fun i => values i + 1

theorem updates (values : Fin 2 → ℕ) :
    Function.update (Function.update values 0 (values 0 + 1)) 1
      ((Function.update values 0 (values 0 + 1)) 1 + 1) = advance values := by
  funext i
  fin_cases i <;> simp [advance, Function.update]

theorem increment_hoareTime (p : Ports w) (values : Fin 2 → ℕ) (i : Fin 2) (W : ℕ)
    (hW : (values i).bits.length ≤ W) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable p R) :
    (BinaryIncrementMachine.machine (p.index i)).HoareTime (Logical p values before input emitted R)
      (Logical p (Function.update values i (values i + 1)) before input emitted R) (2 * W + 4) := by
  let C : (Fin w → Tape) → Prop := fun work => (∀ j, j ≠ i → Register (values j) (work (p.index j))) ∧ R work
  have hC : BinaryIncrementFramed.Stable (p.index i) C := by
    rintro work next he ⟨hr, hx⟩
    exact ⟨fun j hj => by simpa only [he _ (p.injective.ne hj)] using hr j hj,
      hR work next (fun k hk => he k (hk i)) hx⟩
  have h := BinaryIncrementFramed.bounded_hoareTime (p.index i) (values i) W hW before input emitted C hC
  apply h.consequence
  · rintro inp work out ⟨hc, hr⟩
    exact ⟨hc, hr.safe, hr.registers i, (fun j _ => hr.registers j), hr.extra⟩
  · rintro inp work out ⟨hc, hs, hi, hj, hx⟩
    refine ⟨hc, ⟨hs, ?_, hx⟩⟩
    intro j
    by_cases he : j = i
    · subst j
      simpa only [Function.update_self] using hi
    · simpa only [Function.update_of_ne he] using hj j he
  · exact le_rfl

theorem emit_hoareTime (p : Ports w) (values : Fin 2 → ℕ) (W : ℕ)
    (hW : ∀ i, (values i).bits.length ≤ W) (kind : Kind) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (StrictGeneratedBytes.machine p.index kind).HoareTime (Logical p values before input emitted R)
      (Logical p values before input (emitted ++ RowSquareCanonical.entries (data values kind)) R)
      (StrictGeneratedBytes.timeBound W kind) :=
  (StrictGeneratedBytes.hoareTime p.index values W hW kind before input emitted R).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.safe, hr.registers, hr.extra⟩)
    (fun _ _ _ ⟨hc, hs, hr, hx⟩ => ⟨hc, ⟨hs, hr, hx⟩⟩) le_rfl

def increments (p : Ports w) : TM w :=
  seqTM (BinaryIncrementMachine.machine (p.index 0)) (BinaryIncrementMachine.machine (p.index 1))

def machine (p : Ports w) (kind : Kind) : TM w := seqTM (StrictGeneratedBytes.machine p.index kind) (increments p)
def timeBound (W : ℕ) (kind : Kind) : ℕ := StrictGeneratedBytes.timeBound W kind + 4 * W + 10

theorem increments_hoareTime (p : Ports w) (values : Fin 2 → ℕ) (W : ℕ)
    (hW : ∀ i, (values i).bits.length ≤ W) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable p R) :
    (increments p).HoareTime (Logical p values before input emitted R)
      (Logical p (advance values) before input emitted R) (4 * W + 9) := by
  have h0 := increment_hoareTime p values 0 W (hW 0) before input emitted R hR
  have h1 := increment_hoareTime p (Function.update values 0 (values 0 + 1)) 1 W
    (by simpa only [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] using hW 1) before input emitted R hR
  have h := seqTM_hoareTime _ _ h0 (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) h1
  apply h.consequence (fun _ _ _ hh => hh)
  · intro inp work out hh
    simpa only [updates] using hh
  · omega

theorem hoareTime (p : Ports w) (values : Fin 2 → ℕ) (W : ℕ)
    (hW : ∀ i, (values i).bits.length ≤ W) (kind : Kind) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable p R) :
    (machine p kind).HoareTime (Logical p values before input emitted R)
      (Logical p (advance values) before input (emitted ++ RowSquareCanonical.entries (data values kind)) R)
      (timeBound W kind) := by
  have he := emit_hoareTime p values W hW kind before input emitted R
  have hi := increments_hoareTime p values W hW before input (emitted ++ RowSquareCanonical.entries (data values kind)) R hR
  have h := seqTM_hoareTime _ _ he (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hi
  exact h.mono_bound (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.GeneratedEnergyStep

#print axioms JointThermoComplexity.Complexity.GeneratedEnergyStep.increment_hoareTime
#print axioms JointThermoComplexity.Complexity.GeneratedEnergyStep.hoareTime
