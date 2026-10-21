module
public import proofs.JointThermoComplexity.Complexity.EquationRowControl
public import proofs.JointThermoComplexity.Complexity.EquationProductReplay
public import proofs.JointThermoComplexity.Complexity.WordPolynomialProgram

set_option autoImplicit false
@[expose] public section

/-! Literal Cartesian row-square output control. Presence checks precede degree
checks, and each homogenized term contributes two coordinates in source order.
Entry streams contain no final polynomial terminator.
-/

namespace JointThermoComplexity.Complexity.RowSquareControl
open EquationRowControl

def wordSlot (i : Fin 3) (j : Fin 2) : Fin 7 := ⟨2 * i.val + j.val, by omega⟩
def scaleSlot : Fin 7 := 6

def values (s : State) (scaleBits : List Bool) : Fin 7 → List Bool :=
  ![(s.terms 0).words 0, (s.terms 0).words 1, (s.terms 1).words 0, (s.terms 1).words 1,
    (s.terms 2).words 0, (s.terms 2).words 1, scaleBits]

theorem values_word (s : State) (scaleBits : List Bool) (i : Fin 3) (j : Fin 2) :
    values s scaleBits (wordSlot i j) = (s.terms i).words j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem values_scale (s : State) (scaleBits : List Bool) : values s scaleBits scaleSlot = scaleBits := rfl

def template (i : Fin 3) (d : Fin 3) : List (WordPolynomialProgram.Ref 7) :=
  if d.val = 0 then [.paired false scaleSlot, .paired false scaleSlot]
  else if d.val = 1 then [.paired false (wordSlot i 0), .paired false scaleSlot]
  else [.paired false (wordSlot i 0), .paired false (wordSlot i 1)]

def program (i j di dj : Fin 3) : List (WordCodeProgram.Instr 7) :=
  WordPolynomialProgram.monomial (template i di ++ template j dj)

theorem template_length (i d : Fin 3) : (template i d).length = 2 := by
  unfold template
  split
  · rfl
  · split <;> rfl

theorem program_time (i j di dj : Fin 3) (W : ℕ) : WordCodeProgram.timeBound W (program i j di dj) = 12 * W + 62 := by
  fin_cases di <;> fin_cases dj <;>
    simp [program, template, WordPolynomialProgram.monomial, WordPolynomialProgram.marked,
      WordPolynomialProgram.instruction, WordCodeProgram.timeBound, WordCodeProgram.atomTime] <;> omega

def degree (t : Term) : Option (Fin 3) :=
  if t.flags 0 then if t.flags 1 then if t.flags 2 then none else some 2 else some 1 else some 0

def degreeOutput (t : Term) (f : Fin 3 → List Bool) : List Bool :=
  match degree t with
  | none => []
  | some d => f d

def requirements (i : Fin 3) : List (Fin 3) := List.ofFn (fun j : Fin (i.val + 1) => ⟨j.val, by omega⟩)

theorem requirements_length (i : Fin 3) : (requirements i).length = i.val + 1 := by simp only [requirements, List.length_ofFn]

def present (s : State) (flags : List (Fin 3)) : Bool := flags.all (fun i => (s.terms i).present)

def entry (s : State) (scaleBits : List Bool) (i j di dj : Fin 3) : List Bool :=
  true :: (EquationProductReplay.output (s.terms i).coefficient (s.terms j).coefficient ++
    WordCodeProgram.output (values s scaleBits) (program i j di dj))

def selected (s : State) (scaleBits : List Bool) (i j : Fin 3) : List Bool :=
  degreeOutput (s.terms i) (fun di => degreeOutput (s.terms j) (fun dj => entry s scaleBits i j di dj))

def pair (s : State) (scaleBits : List Bool) (i j : Fin 3) : List Bool :=
  if present s (requirements i ++ requirements j) then selected s scaleBits i j else []

def pairs : List (Fin 3 × Fin 3) := (List.finRange 3).flatMap (fun i => (List.finRange 3).map (fun j => (i, j)))

theorem pairs_length : pairs.length = 9 := by decide

def output (s : State) (scaleBits : List Bool) : List Bool := pairs.flatMap (fun ij => pair s scaleBits ij.1 ij.2)

end JointThermoComplexity.Complexity.RowSquareControl

#print axioms JointThermoComplexity.Complexity.RowSquareControl.program_time
#print axioms JointThermoComplexity.Complexity.RowSquareControl.pairs_length
