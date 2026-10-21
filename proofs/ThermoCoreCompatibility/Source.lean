module
public import proofs.ThermoCoreCompatibility.Reaction

set_option autoImplicit false
@[expose] public section

/-! Source-faithful PAC semantics from Definitions 1 and 2 of Kosc et al. -/

namespace ThermoCoreCompatibility

open scoped BigOperators

variable {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]

structure Motif (Q : ReversibleCRN Species Reaction) where
  species : Finset Species
  reactions : Finset Reaction

namespace Motif

variable {Q : ReversibleCRN Species Reaction}

/-- Reinterpret a motif on a network with the same species and reaction index
types. This is used to state formally that PAC status depends on reaction
chemistry, not on positive kinetic prefactors. -/
def rebase (C : Motif Q) (Q' : ReversibleCRN Species Reaction) : Motif Q' where
  species := C.species
  reactions := C.reactions

def SideIncident (C : Motif Q) : Prop :=
  C.species.Nonempty ∧ C.reactions.Nonempty ∧
    ∀ r ∈ C.reactions,
      (∃ s ∈ C.species, 0 < Q.reactant r s) ∧
      (∃ s ∈ C.species, 0 < Q.product r s)

def Productive (C : Motif Q) (v : Reaction → ℝ) : Prop :=
  ∀ s ∈ C.species,
    0 < ∑ r ∈ C.reactions, (Q.stoich s r : ℝ) * v r

def IsAutocatalyticMotif (C : Motif Q) : Prop :=
  C.SideIncident ∧ ∃ v : Reaction → ℝ, C.Productive v

def StrictSubmotif (small large : Motif Q) : Prop :=
  small.species ⊆ large.species ∧ small.reactions ⊆ large.reactions ∧
    (small.species ≠ large.species ∨ small.reactions ≠ large.reactions)

def IsPAC (C : Motif Q) : Prop :=
  C.IsAutocatalyticMotif ∧
    ∀ small : Motif Q, small.StrictSubmotif C → ¬ small.IsAutocatalyticMotif

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem stoich_eq_of_chemistry_eq
    {Q' : ReversibleCRN Species Reaction}
    (hreactant : Q'.reactant = Q.reactant)
    (hproduct : Q'.product = Q.product) : Q'.stoich = Q.stoich := by
  funext s r
  simp only [ReversibleCRN.stoich]
  rw [hreactant, hproduct]

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rebase_sideIncident_iff
    {Q' : ReversibleCRN Species Reaction} (C : Motif Q)
    (hreactant : Q'.reactant = Q.reactant)
    (hproduct : Q'.product = Q.product) :
    (C.rebase Q').SideIncident ↔ C.SideIncident := by
  simp only [SideIncident, rebase]
  rw [hreactant, hproduct]

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rebase_productive_iff
    {Q' : ReversibleCRN Species Reaction} (C : Motif Q) (v : Reaction → ℝ)
    (hreactant : Q'.reactant = Q.reactant)
    (hproduct : Q'.product = Q.product) :
    (C.rebase Q').Productive v ↔ C.Productive v := by
  simp only [Productive, rebase]
  rw [stoich_eq_of_chemistry_eq hreactant hproduct]

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rebase_isAutocatalyticMotif_iff
    {Q' : ReversibleCRN Species Reaction} (C : Motif Q)
    (hreactant : Q'.reactant = Q.reactant)
    (hproduct : Q'.product = Q.product) :
    (C.rebase Q').IsAutocatalyticMotif ↔ C.IsAutocatalyticMotif := by
  simp only [IsAutocatalyticMotif]
  rw [rebase_sideIncident_iff C hreactant hproduct]
  apply and_congr_right
  intro _
  apply exists_congr
  intro v
  exact rebase_productive_iff C v hreactant hproduct

omit [DecidableEq Species] [DecidableEq Reaction] in
theorem rebase_isPAC
    {Q' : ReversibleCRN Species Reaction} (C : Motif Q)
    (hreactant : Q'.reactant = Q.reactant)
    (hproduct : Q'.product = Q.product) (hC : C.IsPAC) :
    (C.rebase Q').IsPAC := by
  rcases hC with ⟨hauto, hminimal⟩
  constructor
  · exact (rebase_isAutocatalyticMotif_iff C hreactant hproduct).2 hauto
  · intro small' hstrict' hauto'
    let small : Motif Q := {
      species := small'.species
      reactions := small'.reactions }
    have hstrict : small.StrictSubmotif C := by
      simpa only [StrictSubmotif, small, rebase] using hstrict'
    apply hminimal small hstrict
    have hback : (small'.rebase Q).IsAutocatalyticMotif :=
      (rebase_isAutocatalyticMotif_iff small' hreactant.symm hproduct.symm).2 hauto'
    simpa only [small, rebase] using hback

end Motif

end ThermoCoreCompatibility

#print axioms ThermoCoreCompatibility.Motif.rebase_isPAC
