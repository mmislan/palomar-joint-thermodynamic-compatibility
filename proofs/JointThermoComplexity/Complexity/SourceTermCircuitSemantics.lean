module
public import proofs.JointThermoComplexity.Complexity.SourceTermCircuitData
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

/- Adapted from DInstabilityComplexity/TermCircuitSemantics.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Every term circuit extends each input and forces the correct output -/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open RealSyntax MvPolynomial

def EquationsHold (ps : List (MvPolynomial V ℤ)) (x : V → ℝ) : Prop :=
  ∀ p ∈ ps, p.eval₂ (Int.castRingHom ℝ) x = 0

theorem equationsHold_append (ps qs : List (MvPolynomial V ℤ)) (x : V → ℝ) :
    EquationsHold (ps ++ qs) x ↔ EquationsHold ps x ∧ EquationsHold qs x := by
  simp only [EquationsHold, List.mem_append, or_imp, forall_and]

theorem equationsHold_singleton (p : MvPolynomial V ℤ) (x : V → ℝ) :
    EquationsHold [p] x ↔ p.eval₂ (Int.castRingHom ℝ) x = 0 := by
  simp only [EquationsHold, List.mem_singleton, forall_eq]

theorem equationsHold_rename (ps : List (MvPolynomial V ℤ)) (f : V → W) (x : W → ℝ) :
    EquationsHold (ps.map (rename f)) x ↔ EquationsHold ps (x ∘ f) := by
  constructor
  · intro h p hp
    have he := h _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa only [MvPolynomial.eval₂_rename] using he
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa only [MvPolynomial.eval₂_rename] using h q hq

theorem binaryLeft_assignment (s t : Term n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ (TermSlot s ⊕ TermSlot t) → ℝ) :
    (Sum.elim ρ a) ∘ binaryLeft s t = Sum.elim ρ (fun v => a (.inr (.inl v))) := by
  funext v
  cases v <;> rfl

theorem binaryRight_assignment (s t : Term n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ (TermSlot s ⊕ TermSlot t) → ℝ) :
    (Sum.elim ρ a) ∘ binaryRight s t = Sum.elim ρ (fun v => a (.inr (.inr v))) := by
  funext v
  cases v <;> rfl

theorem unaryChild_assignment (s : Term n) (ρ : Fin n → ℝ) (a : Unit ⊕ TermSlot s → ℝ) :
    (Sum.elim ρ a) ∘ unaryChild s = Sum.elim ρ (fun v => a (.inr v)) := by
  funext v
  cases v <;> rfl

def termValues (ρ : Fin n → ℝ) : (t : Term n) → TermSlot t → ℝ
  | .int z, _ => z
  | .var v, _ => ρ v
  | .add s t, .inl _ => s.eval ρ + t.eval ρ
  | .add s _, .inr (.inl a) => termValues ρ s a
  | .add _ t, .inr (.inr a) => termValues ρ t a
  | .mul s t, .inl _ => s.eval ρ * t.eval ρ
  | .mul s _, .inr (.inl a) => termValues ρ s a
  | .mul _ t, .inr (.inr a) => termValues ρ t a
  | .neg s, .inl _ => -s.eval ρ
  | .neg s, .inr a => termValues ρ s a

theorem termValues_root (ρ : Fin n → ℝ) (t : Term n) : termValues ρ t (termRoot t) = t.eval ρ := by
  cases t <;> rfl

theorem termEquations_sound (t : Term n) (ρ : Fin n → ℝ) (a : TermSlot t → ℝ)
    (h : EquationsHold (termEquations t) (Sum.elim ρ a)) : a (termRoot t) = t.eval ρ := by
  induction t with
  | int z =>
    simpa only [termEquations, equationsHold_singleton, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, Sum.elim_inr, termRoot, Term.eval,
      sub_eq_zero, Int.coe_castRingHom] using h
  | var v =>
    simpa only [termEquations, equationsHold_singleton, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, Sum.elim_inr, Sum.elim_inl, termRoot, Term.eval,
      sub_eq_zero] using h
  | add s t hs ht =>
    rcases (equationsHold_append _ _ _).mp h with ⟨hlr, hout⟩
    rcases (equationsHold_append _ _ _).mp hlr with ⟨hl, hr⟩
    have hl' := (equationsHold_rename _ _ _).mp hl
    have hr' := (equationsHold_rename _ _ _).mp hr
    rw [binaryLeft_assignment] at hl'
    rw [binaryRight_assignment] at hr'
    have hs' := hs (fun v => a (.inr (.inl v))) hl'
    have ht' := ht (fun v => a (.inr (.inr v))) hr'
    have he := (equationsHold_singleton _ _).mp hout
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X,
      Sum.elim_inr, sub_eq_zero] at he
    change a (.inl ()) = s.eval ρ + t.eval ρ
    exact he.trans (congrArg₂ (· + ·) hs' ht')
  | mul s t hs ht =>
    rcases (equationsHold_append _ _ _).mp h with ⟨hlr, hout⟩
    rcases (equationsHold_append _ _ _).mp hlr with ⟨hl, hr⟩
    have hl' := (equationsHold_rename _ _ _).mp hl
    have hr' := (equationsHold_rename _ _ _).mp hr
    rw [binaryLeft_assignment] at hl'
    rw [binaryRight_assignment] at hr'
    have hs' := hs (fun v => a (.inr (.inl v))) hl'
    have ht' := ht (fun v => a (.inr (.inr v))) hr'
    have he := (equationsHold_singleton _ _).mp hout
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      Sum.elim_inr, sub_eq_zero] at he
    change a (.inl ()) = s.eval ρ * t.eval ρ
    exact he.trans (congrArg₂ (· * ·) hs' ht')
  | neg s hs =>
    rcases (equationsHold_append _ _ _).mp h with ⟨hl, hout⟩
    have hl' := (equationsHold_rename _ _ _).mp hl
    rw [unaryChild_assignment] at hl'
    have hs' := hs (fun v => a (.inr v)) hl'
    have he := (equationsHold_singleton _ _).mp hout
    simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, Sum.elim_inr] at he
    change a (.inl ()) = -s.eval ρ
    rw [← hs']
    linarith only [he]

theorem termEquations_extension (t : Term n) (ρ : Fin n → ℝ) :
    EquationsHold (termEquations t) (Sum.elim ρ (termValues ρ t)) := by
  induction t with
  | int z =>
    apply (equationsHold_singleton _ _).mpr
    change ((X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) ℤ) - C z).eval₂
      (Int.castRingHom ℝ) (Sum.elim ρ (termValues ρ (.int z))) = 0
    rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
    change (z : ℝ) - (Int.castRingHom ℝ) z = 0
    rw [Int.coe_castRingHom]
    exact sub_self _
  | var v => simp [termEquations, equationsHold_singleton, termValues]
  | add s t hs ht | mul s t hs ht =>
    apply (equationsHold_append _ _ _).mpr
    refine ⟨(equationsHold_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · apply (equationsHold_rename _ _ _).mpr
      rw [binaryLeft_assignment]
      exact hs
    · apply (equationsHold_rename _ _ _).mpr
      rw [binaryRight_assignment]
      exact ht
    · simp [equationsHold_singleton, termValues, termValues_root]
  | neg s hs =>
    apply (equationsHold_append _ _ _).mpr
    refine ⟨?_, ?_⟩
    · apply (equationsHold_rename _ _ _).mpr
      rw [unaryChild_assignment]
      exact hs
    · simp [equationsHold_singleton, termValues, termValues_root]

theorem term_circuit_exact (t : Term n) (ρ : Fin n → ℝ) (r : ℝ) :
    (∃ a : TermSlot t → ℝ, EquationsHold (termEquations t) (Sum.elim ρ a) ∧ a (termRoot t) = r) ↔
      r = t.eval ρ := by
  constructor
  · rintro ⟨a, ha, hr⟩
    exact hr.symm.trans (termEquations_sound t ρ a ha)
  · intro hr
    exact ⟨termValues ρ t, termEquations_extension t ρ, (termValues_root ρ t).trans hr.symm⟩

#print axioms termEquations_sound
#print axioms termEquations_extension
#print axioms term_circuit_exact

end JointThermoComplexity.Complexity.QuadraticCircuit
