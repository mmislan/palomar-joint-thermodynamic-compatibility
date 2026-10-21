module
public import proofs.JointThermoComplexity.Complexity.RationalBranchData
public import proofs.JointThermoComplexity.Complexity.NetworkCodec
public import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
@[expose] public section

/-! Executable finite literal networks with two supplied motifs. All complexes,
rational factors, boxes and finite numberings are explicit input data. -/

namespace JointThermoComplexity.Complexity.RationalLiteralNetwork
open RationalBranchData

abbrev Species (e n m : ℕ) := Fin (n + 2) ⊕ (Fin e ⊕ Fin m)
abbrev Reaction (n m : ℕ) := Fin (n + 2) ⊕ Fin (m + 2)
def speciesCount (e n m : ℕ) : ℕ := (n + 2) + (e + m)
def reactionCount (n m : ℕ) : ℕ := (n + 2) + (m + 2)

def speciesNumbering (e n m : ℕ) : Species e n m ≃ Fin (speciesCount e n m) :=
  (Equiv.sumCongr (Equiv.refl (Fin (n + 2)))
    (finSumFinEquiv : Fin e ⊕ Fin m ≃ Fin (e + m))).trans finSumFinEquiv

def reactionNumbering (n m : ℕ) : Reaction n m ≃ Fin (reactionCount n m) := finSumFinEquiv

variable {e n m : ℕ}

def leftVertex (i : Fin (n + 2)) : Species e n m := .inl i
def external (a : Fin e) : Species e n m := .inr (.inl a)
def rightVertex (i : Fin (m + 2)) : Species e n m :=
  if h0 : i.val = 0 then .inl ⟨0, by omega⟩ else
  if h1 : i.val = 1 then .inl ⟨1, by omega⟩ else .inr (.inr ⟨i.val - 2, by omega⟩)

def atom (a : Species e n m) (k : ℕ) (s : Species e n m) : ℕ := if s = a then k else 0
def padding (γ : Fin e → ℕ) (s : Species e n m) : ℕ :=
  match s with | .inr (.inl a) => γ a | _ => 0
def gain (k : ℕ) (i : Fin (k + 2)) : ℕ := if i = Fin.last (k + 1) then 2 else 1

def reactantRaw (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) (s : Species e n m) : ℕ :=
  match r with
  | .inl i => atom (leftVertex i) 1 s + padding (L.powers i) s
  | .inr i => atom (rightVertex i) 1 s + padding (R.powers i) s

def productRaw (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) (s : Species e n m) : ℕ :=
  match r with
  | .inl i => atom (leftVertex (finRotate (n + 2) i)) (gain n i) s + padding (L.powers i) s
  | .inr i => atom (rightVertex (finRotate (m + 2) i)) (gain m i) s + padding (R.powers i) s

def numeratorRaw (L : Data (Fin e) n) (R : Data (Fin e) m) : Reaction n m → ℕ :=
  Sum.elim L.numeratorAt R.numeratorAt
def denominatorRaw (L : Data (Fin e) n) (R : Data (Fin e) m) : Reaction n m → ℕ :=
  Sum.elim L.denominatorAt R.denominatorAt

theorem numeratorRaw_pos (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) :
    0 < numeratorRaw L R r := by
  cases r with
  | inl i => exact L.numeratorAt_pos i
  | inr i => exact R.numeratorAt_pos i

theorem denominatorRaw_pos (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) :
    0 < denominatorRaw L R r := by
  cases r with
  | inl i => exact L.denominatorAt_pos i
  | inr i => exact R.denominatorAt_pos i

def reaction (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Fin (reactionCount n m)) :
    ReactionCircuit.Reaction (speciesCount e n m) where
  reactant s := reactantRaw L R ((reactionNumbering n m).symm r) ((speciesNumbering e n m).symm s)
  product s := productRaw L R ((reactionNumbering n m).symm r) ((speciesNumbering e n m).symm s)
  numerator := numeratorRaw L R ((reactionNumbering n m).symm r)
  denominator := denominatorRaw L R ((reactionNumbering n m).symm r)
  numerator_pos := numeratorRaw_pos L R _
  denominator_pos := denominatorRaw_pos L R _

def leftMotif (e n m : ℕ) : NetworkData.Motif (speciesCount e n m) (reactionCount n m) where
  species := Finset.univ.image (fun i : Fin (n + 2) => speciesNumbering e n m (leftVertex i))
  reactions := Finset.univ.image (fun i : Fin (n + 2) => reactionNumbering n m (.inl i))

def rightMotif (e n m : ℕ) : NetworkData.Motif (speciesCount e n m) (reactionCount n m) where
  species := Finset.univ.image (fun i : Fin (m + 2) => speciesNumbering e n m (rightVertex i))
  reactions := Finset.univ.image (fun i : Fin (m + 2) => reactionNumbering n m (.inr i))

def internalBox : NetworkData.ClosedBox :=
  ⟨⟨1, 4, by decide⟩, ⟨1, 2, by decide⟩⟩
def externalBox : NetworkData.ClosedBox :=
  ⟨⟨1, 2, by decide⟩, ⟨1, 1, by decide⟩⟩

def boxes (boxed : Bool) (s : Fin (speciesCount e n m)) : Option NetworkData.ClosedBox :=
  if boxed then
    match (speciesNumbering e n m).symm s with
    | .inr (.inl _) => some externalBox
    | _ => some internalBox
  else none

def network (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    NetworkData.Network (speciesCount e n m) (reactionCount n m) 2 where
  reactions := reaction L R
  motifs a := if a.val = 0 then leftMotif e n m else rightMotif e n m
  forward _ := true
  boxes := boxes boxed

def input (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) : NetworkCodec.Input :=
  ⟨speciesCount e n m, reactionCount n m, 2, network boxed L R⟩

def code (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) : List Bool := (input boxed L R).code

theorem decode_code (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    NetworkCodec.decode (code boxed L R) = some (input boxed L R) := NetworkCodec.decode_code _

theorem network_left (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    (network boxed L R).motifs 0 = leftMotif e n m := rfl
theorem network_right (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    (network boxed L R).motifs 1 = rightMotif e n m := rfl
theorem network_forward (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Fin (reactionCount n m)) :
    (network boxed L R).forward r = true := rfl

end JointThermoComplexity.Complexity.RationalLiteralNetwork

#print axioms JointThermoComplexity.Complexity.RationalLiteralNetwork.reaction
#print axioms JointThermoComplexity.Complexity.RationalLiteralNetwork.network
#print axioms JointThermoComplexity.Complexity.RationalLiteralNetwork.code
#print axioms JointThermoComplexity.Complexity.RationalLiteralNetwork.decode_code
