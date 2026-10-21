module
public import proofs.JointThermoComplexity.Complexity.RowSquareControl

set_option autoImplicit false
@[expose] public section

/-! Exact word-data Cartesian interpretation of the stored-row output control.
Each source slot contributes zero or one term; this singleton property preserves
the literal pair order when moving from slot pairs to retained term pairs.
-/

namespace JointThermoComplexity.Complexity.RowSquareWords
open EquationRowControl RowSquareControl

abbrev WordTerm := List Bool × List (List Bool)

def coordinates (s : State) (scaleBits : List Bool) (i d : Fin 3) : List (List Bool) :=
  (template i d).map (WordPolynomialProgram.refCode (values s scaleBits))

def piece (s : State) (scaleBits : List Bool) (i : Fin 3) : Option WordTerm :=
  if present s (requirements i) then (degree (s.terms i)).map (fun d => ((s.terms i).coefficient, coordinates s scaleBits i d))
  else none

def fromSlots (s : State) (scaleBits : List Bool) (slots : List (Fin 3)) : List WordTerm :=
  slots.flatMap (fun i => (piece s scaleBits i).toList)

def pieces (s : State) (scaleBits : List Bool) : List WordTerm := fromSlots s scaleBits (List.finRange 3)

def entryWords (a b : WordTerm) : List Bool :=
  true :: (EquationProductReplay.output a.1 b.1 ++ RowWordCodec.monomial (a.2 ++ b.2))

def cartesian (xs ys : List WordTerm) : List Bool := xs.flatMap (fun a => ys.flatMap (fun b => entryWords a b))

theorem entry_eq (s : State) (scaleBits : List Bool) (i j di dj : Fin 3) :
    RowSquareControl.entry s scaleBits i j di dj =
      entryWords ((s.terms i).coefficient, coordinates s scaleBits i di)
        ((s.terms j).coefficient, coordinates s scaleBits j dj) := by
  simp only [RowSquareControl.entry, RowSquareControl.program, WordPolynomialProgram.monomial_output,
    List.map_append, entryWords, coordinates]

theorem pair_eq (s : State) (scaleBits : List Bool) (i j : Fin 3) :
    RowSquareControl.pair s scaleBits i j = cartesian (piece s scaleBits i).toList (piece s scaleBits j).toList := by
  have hp : present s (requirements i ++ requirements j) = (present s (requirements i) && present s (requirements j)) :=
    List.all_append
  unfold RowSquareControl.pair
  rw [hp]
  unfold piece cartesian RowSquareControl.selected RowSquareControl.degreeOutput
  cases hpi : present s (requirements i) <;> cases hpj : present s (requirements j) <;>
    cases hdi : degree (s.terms i) <;> cases hdj : degree (s.terms j) <;> simp_all
  apply entry_eq

theorem cartesian_append (xs ys zs : List WordTerm) : cartesian (xs ++ ys) zs = cartesian xs zs ++ cartesian ys zs :=
  List.flatMap_append

theorem cross_piece (s : State) (scaleBits : List Bool) (i : Fin 3) (slots : List (Fin 3)) :
    slots.flatMap (fun j => cartesian (piece s scaleBits i).toList (piece s scaleBits j).toList) =
      cartesian (piece s scaleBits i).toList (fromSlots s scaleBits slots) := by
  cases piece s scaleBits i with
  | none => simp [cartesian]
  | some a =>
    simp only [cartesian, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, fromSlots]
    rw [List.flatMap_assoc]

def outputOn (s : State) (scaleBits : List Bool) (left right : List (Fin 3)) : List Bool :=
  left.flatMap (fun i => right.flatMap (fun j => RowSquareControl.pair s scaleBits i j))

theorem outputOn_eq (s : State) (scaleBits : List Bool) (left right : List (Fin 3)) :
    outputOn s scaleBits left right = cartesian (fromSlots s scaleBits left) (fromSlots s scaleBits right) := by
  induction left with
  | nil => simp only [outputOn, fromSlots, List.flatMap_nil, cartesian]
  | cons i rest ih =>
    change right.flatMap (fun j => RowSquareControl.pair s scaleBits i j) ++ outputOn s scaleBits rest right =
      cartesian ((piece s scaleBits i).toList ++ fromSlots s scaleBits rest) (fromSlots s scaleBits right)
    rw [cartesian_append, ← ih]
    congr 1
    simp_rw [pair_eq]
    exact cross_piece s scaleBits i right

theorem output_eq (s : State) (scaleBits : List Bool) :
    RowSquareControl.output s scaleBits = cartesian (pieces s scaleBits) (pieces s scaleBits) := by
  have h := outputOn_eq s scaleBits (List.finRange 3) (List.finRange 3)
  simpa only [RowSquareControl.output, RowSquareControl.pairs, outputOn, pieces,
    List.flatMap_assoc, List.flatMap_map] using h

end JointThermoComplexity.Complexity.RowSquareWords

#print axioms JointThermoComplexity.Complexity.RowSquareWords.pair_eq
#print axioms JointThermoComplexity.Complexity.RowSquareWords.output_eq
