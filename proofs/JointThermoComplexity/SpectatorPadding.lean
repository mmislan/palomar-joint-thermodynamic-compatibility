module
public import proofs.ThermoCoreCompatibility.Source
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity
open ThermoCoreCompatibility
open scoped BigOperators

variable {S R : Type*} [DecidableEq S] [DecidableEq R]

/- Equality only on the selected internal species suffices; external complexes may change. -/
omit [DecidableEq S] [DecidableEq R] in
theorem restricted_autocatalytic_iff (Q Q' : ReversibleCRN S R) (C D : Motif Q)
    (hs : D.species ⊆ C.species) (hr : D.reactions ⊆ C.reactions)
    (ha : ∀ r ∈ C.reactions, ∀ s ∈ C.species, Q'.reactant r s = Q.reactant r s)
    (hb : ∀ r ∈ C.reactions, ∀ s ∈ C.species, Q'.product r s = Q.product r s) :
    (D.rebase Q').IsAutocatalyticMotif ↔ D.IsAutocatalyticMotif := by
  have hside : (D.rebase Q').SideIncident ↔ D.SideIncident := by
    simp only [Motif.SideIncident, Motif.rebase]
    constructor <;> rintro ⟨hne₁,hne₂,h⟩ <;> refine ⟨hne₁,hne₂,?_⟩ <;> intro r hmem
    · obtain ⟨⟨s,hs',ha'⟩,⟨t,ht',hb'⟩⟩ := h r hmem
      exact ⟨⟨s,hs',by simpa [ha r (hr hmem) s (hs hs')] using ha'⟩,
        ⟨t,ht',by simpa [hb r (hr hmem) t (hs ht')] using hb'⟩⟩
    · obtain ⟨⟨s,hs',ha'⟩,⟨t,ht',hb'⟩⟩ := h r hmem
      exact ⟨⟨s,hs',by simpa [ha r (hr hmem) s (hs hs')] using ha'⟩,
        ⟨t,ht',by simpa [hb r (hr hmem) t (hs ht')] using hb'⟩⟩
  have hprod (v : R → ℝ) : (D.rebase Q').Productive v ↔ D.Productive v := by
    have he (s : S) (hmem : s ∈ D.species) :
        (∑ r ∈ D.reactions, (Q'.stoich s r : ℝ)*v r) =
        ∑ r ∈ D.reactions, (Q.stoich s r : ℝ)*v r := by
      apply Finset.sum_congr rfl
      intro r hmemr
      simp only [ReversibleCRN.stoich, ha r (hr hmemr) s (hs hmem),
        hb r (hr hmemr) s (hs hmem)]
    simp only [Motif.Productive, Motif.rebase]
    constructor <;> intro hp s hmem
    · rw [← he s hmem]; exact hp s hmem
    · rw [he s hmem]; exact hp s hmem
  simp only [Motif.IsAutocatalyticMotif, hside, hprod]

omit [DecidableEq S] [DecidableEq R] in
theorem restricted_isPAC (Q Q' : ReversibleCRN S R) (C : Motif Q)
    (ha : ∀ r ∈ C.reactions, ∀ s ∈ C.species, Q'.reactant r s = Q.reactant r s)
    (hb : ∀ r ∈ C.reactions, ∀ s ∈ C.species, Q'.product r s = Q.product r s)
    (hC : C.IsPAC) : (C.rebase Q').IsPAC := by
  constructor
  · exact (restricted_autocatalytic_iff Q Q' C C (by rfl) (by rfl) ha hb).2 hC.1
  · intro D hsub hauto
    let D₀ : Motif Q := { species := D.species, reactions := D.reactions }
    have hsub₀ : D₀.StrictSubmotif C := hsub
    apply hC.2 D₀ hsub₀
    exact (restricted_autocatalytic_iff Q Q' C D₀ hsub₀.1 hsub₀.2.1 ha hb).1 hauto

omit [DecidableEq S] in
theorem padded_complex_activity [Fintype S] (z : S → ℝ) (a W : Complex S) :
    ReversibleCRN.complexActivity z (fun s => a s+W s) =
      ReversibleCRN.complexActivity z a * ReversibleCRN.complexActivity z W := by
  simp [ReversibleCRN.complexActivity, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq S] in
theorem padded_current [Fintype S] (z : S → ℝ) (a b W : Complex S) (k : ℝ) :
    k * (ReversibleCRN.complexActivity z (fun s => a s+W s) -
      ReversibleCRN.complexActivity z (fun s => b s+W s)) =
    (k * ReversibleCRN.complexActivity z W) *
      (ReversibleCRN.complexActivity z a - ReversibleCRN.complexActivity z b) := by
  rw [padded_complex_activity, padded_complex_activity]
  ring

end JointThermoComplexity



#print axioms JointThermoComplexity.restricted_isPAC

#print axioms JointThermoComplexity.padded_current
