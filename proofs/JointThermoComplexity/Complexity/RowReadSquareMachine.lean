module
public import proofs.JointThermoComplexity.Complexity.EquationRowMachine
public import proofs.JointThermoComplexity.Complexity.RowSquareMachine

set_option autoImplicit false
@[expose] public section

/-! A real source-row reader followed by the row-square emitter. The extra
scale word and emitter auxiliaries survive parsing; arbitrary external work
outside the twenty-eight ports survives both machines.
-/

namespace JointThermoComplexity.Complexity.RowReadSquareMachine
open _root_.Complexity _root_.Complexity.TM BoxBufferState EquationRowControl
open RowSquareFrame (Ports Ready Logical)
open HeaderAt (Cursor)
variable {w : ℕ}

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ k, (∀ a, k ≠ p.index a) → work' k = work k) → R work → R work'

theorem reader_stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    EquationRowFrame.Stable p.row R := by
  intro work next he hr
  apply hR work next _ hr
  intro k hk
  exact he k (fun a => hk ⟨a.val, by omega⟩)

theorem emitter_stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    RowSquareFrame.Stable p R := by
  intro work next he hr
  exact hR work next (fun k hk => he k (hk 25) (hk 26)) hr

theorem scale_row (p : Ports w) (a : Fin 25) : p.scale ≠ p.row.index a :=
  p.separate _ _ (by dsimp; omega)

def Extra (p : Ports w) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  (work p.scale).HasBinaryString scaleBits ∧ (work p.scale).cells 0 = Γ.start ∧
    scaleBits.length ≤ W ∧ 4 * B ≤ W ∧ Reusable B (work p.constant) ∧
    (work p.compare).head = 1 ∧ R work

theorem extra_stable (p : Ports w) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    EquationRowFrame.Stable p.row (Extra p scaleBits B W R) := by
  intro work next he h
  rcases h with ⟨hs, hz, hl, hb, hc, hf, hr⟩
  exact ⟨by simpa only [he p.scale (scale_row p)] using hs,
    by simpa only [he p.scale (scale_row p)] using hz, hl, hb,
    by simpa only [he p.constant p.constant_row] using hc,
    by simpa only [he p.compare p.compare_row] using hf,
    reader_stable p R hR work next he hr⟩

theorem to_reader (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape)
    (h : Ready p s scaleBits B W R work) :
    EquationRowFrame.Ready p.row s B (Extra p scaleBits B W R) work := by
  exact { h.saved with extra := ⟨h.scale, h.scale_zero, h.scale_length,
    h.word_bound, h.constant, h.compare_head, h.saved.extra⟩ }

theorem from_reader (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape)
    (h : EquationRowFrame.Ready p.row s B (Extra p scaleBits B W R) work) :
    Ready p s scaleBits B W R work := by
  rcases h.extra with ⟨hs, hz, hl, hb, hc, hf, hr⟩
  exact ⟨{ h with extra := hr }, hs, hz, hl, hb, hc, hf⟩

theorem read_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (hB : 2 ≤ B) (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (EquationRowMachine.machine p.row).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p (parse B s) scaleBits B W emitted R) (EquationRowMachine.timeBound B) :=
  (EquationRowMachine.hoareTime p.row s B hB hlen emitted (Extra p scaleBits B W R)
    (extra_stable p scaleBits B W R hR)).consequence
    (fun _ work _ ⟨hc, hr⟩ => ⟨hc, to_reader p s scaleBits B W R work hr⟩)
    (fun _ work _ ⟨hc, hr⟩ => ⟨hc, from_reader p (parse B s) scaleBits B W R work hr⟩) le_rfl

def machine (p : Ports w) : TM (w + 1) :=
  seqTM (EquationRowMachine.machine p.row) (RowSquareMachine.machine p)

def timeBound (B W : ℕ) : ℕ := EquationRowMachine.timeBound B + RowSquareMachine.timeBound B W + 1

theorem hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (hB : 2 ≤ B) (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p (parse B s) scaleBits B W
        (emitted ++ RowSquareControl.output (parse B s) scaleBits) R) (timeBound B W) := by
  have hread := read_hoareTime p s scaleBits B W hB hlen emitted R hR
  have hemit := RowSquareMachine.hoareTime p (parse B s) scaleBits B W hB emitted R (emitter_stable p R hR)
  have h := seqTM_hoareTime (EquationRowMachine.machine p.row) (RowSquareMachine.machine p) hread (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩)
    hemit
  exact h.mono_bound (by unfold timeBound; omega)

theorem encoded_hoareTime (p : Ports w) (s : State) (row : List (ℤ × List ℕ))
    (suffix scaleBits emitted : List Bool) (B W : ℕ) (hB : 2 ≤ B)
    (hlen : (code row ++ suffix).length ≤ B) (hr : row.length ≤ 3)
    (ha : ∀ a ∈ row, a.1.natAbs ≤ 5)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p { s with input := code row ++ suffix } scaleBits B W emitted R)
      (Logical p (expected s row suffix) scaleBits B W
        (emitted ++ RowSquareControl.output (expected s row suffix) scaleBits) R) (timeBound B W) := by
  have hf : ∀ a ∈ row, a.2.length + 1 ≤ B := by
    intro a hm
    have h := EquationRowMachine.code_monomial_length row a hm
    rw [List.length_append] at hlen
    omega
  simpa only [parse_code B s row suffix hr ha hf] using
    hoareTime p { s with input := code row ++ suffix } scaleBits B W hB hlen emitted R hR

end JointThermoComplexity.Complexity.RowReadSquareMachine

#print axioms JointThermoComplexity.Complexity.RowReadSquareMachine.read_hoareTime
#print axioms JointThermoComplexity.Complexity.RowReadSquareMachine.hoareTime
#print axioms JointThermoComplexity.Complexity.RowReadSquareMachine.encoded_hoareTime
