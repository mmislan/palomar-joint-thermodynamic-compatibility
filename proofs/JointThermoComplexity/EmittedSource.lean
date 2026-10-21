module
public import proofs.JointThermoComplexity.CycleMinimality
public import proofs.JointThermoComplexity.LiteralPath
public import proofs.JointThermoComplexity.SpectatorPadding
public import proofs.ThermoCoreCompatibility.Hypergraph.TriangleSource

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open ThermoCoreCompatibility ThermoCoreCompatibility.Hypergraph
open scoped BigOperators
noncomputable section

abbrev Species (E : Type*) (n m : ℕ) := Fin (n+2) ⊕ (E ⊕ Fin m)
abbrev Reaction (n m : ℕ) := Fin (n+2) ⊕ Fin (m+2)

def leftVertex {E : Type*} {n m : ℕ} (i : Fin (n+2)) : Species E n m := .inl i
def external {E : Type*} {n m : ℕ} (e : E) : Species E n m := .inr (.inl e)
def rightVertex {E : Type*} {n m : ℕ} (i : Fin (m+2)) : Species E n m :=
  if h0 : i.val=0 then .inl ⟨0,by omega⟩ else
  if h1 : i.val=1 then .inl ⟨1,by omega⟩ else .inr (.inr ⟨i.val-2,by omega⟩)

theorem rightVertex_injective {E : Type*} {n m : ℕ} :
    Function.Injective (@rightVertex E n m) := by
  let decode : Species E n m → ℕ := fun s => match s with
    | .inl i => i.val
    | .inr (.inl _) => 0
    | .inr (.inr j) => j.val+2
  have hd (i : Fin (m+2)) : decode (rightVertex i)=i.val := by
    unfold rightVertex
    split_ifs with h0 h1
    · exact h0.symm
    · exact h1.symm
    · change i.val-2+2=i.val
      omega
  intro i j h
  apply Fin.ext
  have hh:=congrArg decode h
  simpa only [hd] using hh

structure Branch (E : Type*) (n : ℕ) where
  coefficient : Fin (n+1) → ℝ
  coefficient_pos : ∀ i,0<coefficient i
  exponent : Fin (n+1) → E → ℕ

def Branch.weight {E : Type*} [Fintype E] {n : ℕ}
    (b : Branch E n) (u : E → ℝ) (i : Fin (n+1)) : ℝ :=
  b.coefficient i / ∏ e, u e ^ b.exponent i e

def Branch.barrier {E : Type*} {n : ℕ} (b : Branch E n) (i : Fin (n+2)) : ℝ :=
  if h : i.val=0 then 1 else 1/b.coefficient ⟨i.val-1,by omega⟩

def Branch.powers {E : Type*} {n : ℕ} (b : Branch E n) (i : Fin (n+2)) (e : E) : ℕ :=
  if h : i.val=0 then 0 else b.exponent ⟨i.val-1,by omega⟩ e

def padding {E : Type*} {n m : ℕ} (γ : E→ℕ) : Complex (Species E n m) :=
  fun s => match s with | .inr (.inl e) => γ e | _ => 0

def source {E : Type*} [DecidableEq E] {n m : ℕ} (L : Branch E n) (R : Branch E m) :
    ReversibleCRN (Species E n m) (Reaction n m) where
  reactant := fun r => match r with
    | .inl i => fun s => atom (leftVertex i) 1 s+padding (L.powers i) s
    | .inr i => fun s => atom (rightVertex i) 1 s+padding (R.powers i) s
  product := fun r => match r with
    | .inl i => fun s => atom (leftVertex (finRotate (n+2) i)) (cycleGain n i) s+padding (L.powers i) s
    | .inr i => fun s => atom (rightVertex (finRotate (m+2) i)) (cycleGain m i) s+padding (R.powers i) s
  barrier := Sum.elim L.barrier R.barrier
  barrier_pos := by
    intro r
    cases r with
    | inl i =>
      dsimp [Branch.barrier]
      split_ifs
      · norm_num
      · exact one_div_pos.mpr (L.coefficient_pos _)
    | inr i =>
      dsimp [Branch.barrier]
      split_ifs
      · norm_num
      · exact one_div_pos.mpr (R.coefficient_pos _)

theorem padding_left {E : Type*} {n m : ℕ} (γ : E → ℕ) (i : Fin (n+2)) :
    @padding E n m γ (leftVertex i)=0 := rfl

theorem padding_right {E : Type*} {n m : ℕ} (γ : E → ℕ) (i : Fin (m+2)) :
    @padding E n m γ (rightVertex i)=0 := by
  unfold rightVertex
  split_ifs <;> rfl

def leftCycle {E : Type*} [DecidableEq E] {n m : ℕ} (L : Branch E n) (R : Branch E m) :
    CycleIn (source L R) n where
  vertex := leftVertex
  edge := Sum.inl
  vertex_injective := Sum.inl_injective
  edge_injective := Sum.inl_injective
  reactant_on := by intro i j; simp only [source, padding, add_zero, atom, leftVertex, Sum.inl.injEq]
  product_on := by intro i j; simp only [source, padding, add_zero, atom, leftVertex, Sum.inl.injEq]

def rightCycle {E : Type*} [DecidableEq E] {n m : ℕ} (L : Branch E n) (R : Branch E m) :
    CycleIn (source L R) m where
  vertex := rightVertex
  edge := Sum.inr
  vertex_injective := rightVertex_injective
  edge_injective := Sum.inr_injective
  reactant_on := by
    intro i j
    simp only [source, padding_right, add_zero, atom, rightVertex_injective.eq_iff]
  product_on := by
    intro i j
    simp only [source, padding_right, add_zero, atom, rightVertex_injective.eq_iff]

theorem supplied_cores_are_PACs {E : Type*} [DecidableEq E] {n m : ℕ}
    (L : Branch E n) (R : Branch E m) :
    (leftCycle L R).motif.IsPAC ∧ (rightCycle L R).motif.IsPAC :=
  ⟨(leftCycle L R).isPAC,(rightCycle L R).isPAC⟩

end
end JointThermoComplexity.Emitted


#print axioms JointThermoComplexity.Emitted.rightVertex_injective

#print axioms JointThermoComplexity.Emitted.supplied_cores_are_PACs
