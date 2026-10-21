module
public import proofs.JointThermoComplexity.Complexity.RowPairEntry

set_option autoImplicit false
@[expose] public section

/-! Actual ordered flag dispatch for one Cartesian pair. Unused row slots and
unused degree flags are never consulted before their earlier markers succeed.
-/

namespace JointThermoComplexity.Complexity.RowPairSelect
open _root_.Complexity _root_.Complexity.TM EquationRowControl RowSquareFrame
open HeaderAt (Cursor)
variable {w : ℕ}

theorem branch_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W T : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (idx : Fin (w + 1)) (b : Bool)
    (hflag : ∀ work, Ready p s scaleBits B W R work → (work idx).read = Γ.ofBool b)
    (yes no : TM (w + 1)) (yesBits noBits : List Bool)
    (hy : yes.HoareTime (Logical p s scaleBits B W emitted R) (Logical p s scaleBits B W (emitted ++ yesBits) R) T)
    (hn : no.HoareTime (Logical p s scaleBits B W emitted R) (Logical p s scaleBits B W (emitted ++ noBits) R) T) :
    (WorkSymbolBranch.machine Γ.one idx yes no).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ if b then yesBits else noBits) R) (T + 2) := by
  cases b with
  | true =>
    have h := WorkSymbolBranch.yes_hoareTime Γ.one idx yes no s.before s.input emitted s.before s.input
      (emitted ++ yesBits) (Ready p s scaleBits B W R) (Ready p s scaleBits B W R) T hy
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      exact ⟨⟨hc, hr⟩, by simpa only [Γ.ofBool] using hflag work hr⟩
    · intro inp work out hh
      simpa only [↓reduceIte, Logical] using hh
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one idx yes no s.before s.input emitted s.before s.input
      (emitted ++ noBits) (Ready p s scaleBits B W R) (Ready p s scaleBits B W R) T hn
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      rw [hflag work hr]
      decide
    · intro inp work out hh
      simpa only [Bool.false_eq_true, ↓reduceIte, Logical] using hh
    · exact le_rfl

def degreeMachine (p : Ports w) (i : Fin 3) (body : Fin 3 → TM (w + 1)) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.row.flag i 0)
    (WorkSymbolBranch.machine Γ.one (p.row.flag i 1)
      (WorkSymbolBranch.machine Γ.one (p.row.flag i 2) (emitBitsTM []) (body 2)) (body 1)) (body 0)

theorem degree_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (i : Fin 3) (B W T : ℕ)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (body : Fin 3 → TM (w + 1)) (f : Fin 3 → List Bool)
    (hb : ∀ d, (body d).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ f d) R) T) :
    (degreeMachine p i body).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ RowSquareControl.degreeOutput (s.terms i) f) R) (T + 6) := by
  have hid := (literal_hoareTime p s scaleBits [] B W emitted R).mono_bound (show ([] : List Bool).length ≤ T by simp)
  have h2 := branch_hoareTime p s scaleBits B W T emitted R (p.row.flag i 2) ((s.terms i).flags 2)
    (fun work hr => (hr.saved.flags i 2).2) (emitBitsTM []) (body 2) [] (f 2) hid (hb 2)
  have h1 := branch_hoareTime p s scaleBits B W (T + 2) emitted R (p.row.flag i 1) ((s.terms i).flags 1)
    (fun work hr => (hr.saved.flags i 1).2) _ (body 1)
    (if (s.terms i).flags 2 then [] else f 2) (f 1) h2 ((hb 1).mono_bound (by omega))
  have h0 := branch_hoareTime p s scaleBits B W (T + 4) emitted R (p.row.flag i 0) ((s.terms i).flags 0)
    (fun work hr => (hr.saved.flags i 0).2) _ (body 0)
    (if (s.terms i).flags 1 then if (s.terms i).flags 2 then [] else f 2 else f 1) (f 0)
    h1 ((hb 0).mono_bound (by omega))
  have hpure : RowSquareControl.degreeOutput (s.terms i) f =
      (if (s.terms i).flags 0 then if (s.terms i).flags 1 then if (s.terms i).flags 2 then [] else f 2 else f 1 else f 0) := by
    unfold RowSquareControl.degreeOutput RowSquareControl.degree
    split_ifs <;> rfl
  simpa only [degreeMachine, hpure] using h0

def selectedMachine (p : Ports w) (i j : Fin 3) : TM (w + 1) :=
  degreeMachine p i (fun di => degreeMachine p j (fun dj => RowPairEntry.machine p i j di dj))

theorem selected_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (i j : Fin 3) (B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (selectedMachine p i j).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ RowSquareControl.selected s scaleBits i j) R)
      (RowPairEntry.timeBound B W + 12) :=
  degree_hoareTime p s scaleBits i B W (RowPairEntry.timeBound B W + 6) emitted R _ _ (fun di =>
    degree_hoareTime p s scaleBits j B W (RowPairEntry.timeBound B W) emitted R _ _
      (fun dj => RowPairEntry.hoareTime p s scaleBits i j di dj B W hB emitted R hR))

def gateMachine (p : Ports w) (body : TM (w + 1)) : List (Fin 3) → TM (w + 1)
  | [] => body
  | i :: rest => WorkSymbolBranch.machine Γ.one (p.row.presence i) (gateMachine p body rest) (emitBitsTM [])

theorem gate_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (flags : List (Fin 3)) (B W T : ℕ)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (body : TM (w + 1)) (bits : List Bool)
    (hb : body.HoareTime (Logical p s scaleBits B W emitted R) (Logical p s scaleBits B W (emitted ++ bits) R) T) :
    (gateMachine p body flags).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ if RowSquareControl.present s flags then bits else []) R)
      (T + 2 * flags.length) := by
  induction flags with
  | nil => simpa only [gateMachine, RowSquareControl.present, List.all_nil, ↓reduceIte, List.length_nil, Nat.mul_zero, Nat.add_zero] using hb
  | cons i rest ih =>
    have hid := (literal_hoareTime p s scaleBits [] B W emitted R).mono_bound
      (show ([] : List Bool).length ≤ T + 2 * rest.length by simp)
    have h := branch_hoareTime p s scaleBits B W (T + 2 * rest.length) emitted R (p.row.presence i)
      (s.terms i).present (fun work hr => (hr.saved.presence i).2) _ (emitBitsTM [])
      (if RowSquareControl.present s rest then bits else []) [] ih hid
    apply h.consequence (fun _ _ _ hh => hh)
    · intro inp work out hh
      cases hi : (s.terms i).present <;>
        simpa [RowSquareControl.present, hi, Logical] using hh
    · simp only [List.length_cons]
      omega

def machine (p : Ports w) (i j : Fin 3) : TM (w + 1) :=
  gateMachine p (selectedMachine p i j) (RowSquareControl.requirements i ++ RowSquareControl.requirements j)

def timeBound (B W : ℕ) : ℕ := RowPairEntry.timeBound B W + 24

theorem hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (i j : Fin 3) (B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p i j).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ RowSquareControl.pair s scaleBits i j) R) (timeBound B W) := by
  have h := gate_hoareTime p s scaleBits (RowSquareControl.requirements i ++ RowSquareControl.requirements j)
    B W (RowPairEntry.timeBound B W + 12) emitted R (selectedMachine p i j) (RowSquareControl.selected s scaleBits i j)
    (selected_hoareTime p s scaleBits i j B W hB emitted R hR)
  exact h.mono_bound (by simp only [timeBound, List.length_append, RowSquareControl.requirements_length]; omega)

end JointThermoComplexity.Complexity.RowPairSelect

#print axioms JointThermoComplexity.Complexity.RowPairSelect.degree_hoareTime
#print axioms JointThermoComplexity.Complexity.RowPairSelect.gate_hoareTime
#print axioms JointThermoComplexity.Complexity.RowPairSelect.hoareTime
