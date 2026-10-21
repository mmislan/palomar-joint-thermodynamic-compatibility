module
public import proofs.JointThermoComplexity.Complexity.BoundedOccurrenceControl
public import proofs.JointThermoComplexity.Complexity.WorkSymbolBranch

set_option autoImplicit false
@[expose] public section

/-! The capacity is a finite list of physical data/marker ports fixed before
input. Each retained marker records whether that position was visited. An
additional end marker detects overflow without loading a fifth reference. -/

namespace JointThermoComplexity.Complexity.BoundedOccurrenceMachine
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
variable {w : ℕ}
abbrev Port (w : ℕ) := Fin (w + 1) × Fin (w + 1)

def Touches (slots : List (Port w)) (ending flag j : Fin (w + 1)) : Prop :=
  j = ending ∨ j = flag ∨ ∃ p ∈ slots, j = p.1 ∨ j = p.2

structure HeadSeparate (p : Port w) (slots : List (Port w)) (ending flag : Fin (w + 1)) : Prop where
  data_marker : p.1 ≠ p.2
  data_end : p.1 ≠ ending
  data_flag : p.1 ≠ flag
  marker_end : p.2 ≠ ending
  marker_flag : p.2 ≠ flag
  data_data : ∀ q ∈ slots, p.1 ≠ q.1
  data_markers : ∀ q ∈ slots, p.1 ≠ q.2
  marker_data : ∀ q ∈ slots, p.2 ≠ q.1
  marker_markers : ∀ q ∈ slots, p.2 ≠ q.2

def Separate : List (Port w) → Fin (w + 1) → Fin (w + 1) → Prop
  | [], ending, flag => ending ≠ flag
  | p :: slots, ending, flag => HeadSeparate p slots ending flag ∧ Separate slots ending flag

theorem HeadSeparate.data_untouched {p : Port w} {slots : List (Port w)} {ending flag : Fin (w + 1)}
    (h : HeadSeparate p slots ending flag) : ¬Touches slots ending flag p.1 := by
  rintro (he | hf | ⟨q, hq, hq' | hq'⟩)
  · exact h.data_end he
  · exact h.data_flag hf
  · exact h.data_data q hq hq'
  · exact h.data_markers q hq hq'

theorem HeadSeparate.marker_untouched {p : Port w} {slots : List (Port w)} {ending flag : Fin (w + 1)}
    (h : HeadSeparate p slots ending flag) : ¬Touches slots ending flag p.2 := by
  rintro (he | hf | ⟨q, hq, hq' | hq'⟩)
  · exact h.marker_end he
  · exact h.marker_flag hf
  · exact h.marker_data q hq hq'
  · exact h.marker_markers q hq hq'

theorem touches_tail {slots : List (Port w)} {p : Port w} {ending flag j : Fin (w + 1)}
    (h : Touches slots ending flag j) : Touches (p :: slots) ending flag j := by
  rcases h with he | hf | ⟨q, hq, hj⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr ⟨q, List.mem_cons_of_mem _ hq, hj⟩)

def Ready (L : ℕ) (slots : List (Port w)) (ending flag : Fin (w + 1))
    (work : Fin (w + 1) → Tape) : Prop :=
  (∀ p ∈ slots, Reusable L (work p.1) ∧ (work p.2).head = 1) ∧
    (work ending).head = 1 ∧ (work flag).head = 1

def Loaded : List (Port w) → Fin (w + 1) → Fin (w + 1) → List Bool → (Fin (w + 1) → Tape) → Prop
  | [], ending, flag, input, work =>
    (work ending).read = Γ.ofBool (SourceBitRead.value input) ∧
      (work flag).read = Γ.ofBool (BooleanMachine.accepted input)
  | p :: slots, ending, flag, input, work =>
    (work p.2).read = Γ.ofBool (SourceBitRead.value input) ∧
      if SourceBitRead.value input then
        BinaryIncrementRun.Register (NaturalCanonicalLoad.value (BooleanMachine.suffix input)) (work p.1) ∧
          Loaded slots ending flag (NaturalRawControl.scan (BooleanMachine.suffix input)).rest work
      else (work flag).read = Γ.ofBool (BooleanMachine.accepted input)

def machine : List (Port w) → Fin (w + 1) → Fin (w + 1) → TM (w + 1)
  | [], ending, flag => SourceBitRead.machine ending flag
  | p :: slots, ending, flag =>
    seqTM (SourceBitRead.machine p.2 flag)
      (WorkSymbolBranch.machine Γ.one p.2
        (seqTM (NaturalCanonicalLoad.machine p.1) (machine slots ending flag)) (emitBitsTM []))

theorem ready_tail {L : ℕ} {p : Port w} {slots : List (Port w)} {ending flag : Fin (w + 1)}
    {work : Fin (w + 1) → Tape} (h : Ready L (p :: slots) ending flag work) :
    Ready L slots ending flag work :=
  ⟨fun q hq => h.1 q (List.mem_cons_of_mem p hq), h.2⟩

theorem noop_hoareTime (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM [] : TM (w + 1)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ R work) 0 := by
  intro inp work out hp
  exact ⟨⟨(emitBitsTM []).qhalt, inp, work, out⟩, 0, le_rfl, .zero, rfl, hp⟩

end JointThermoComplexity.Complexity.BoundedOccurrenceMachine

#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceMachine.machine
#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceMachine.noop_hoareTime
