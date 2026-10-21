module
public import proofs.ThermoCoreCompatibility.Source

set_option autoImplicit false
@[expose] public section

/-! Interacting PAC families retain overlap cover and one reaction owner separately. -/

namespace ThermoCoreCompatibility

variable {Species Reaction Core : Type*}
  [DecidableEq Species] [DecidableEq Reaction] [Fintype Core]

structure CoreFamily (Q : ReversibleCRN Species Reaction) where
  core : Core → Motif Q
  core_isPAC : ∀ k, (core k).IsPAC
  orientation : Reaction → ℤ
  orientation_unit : ∀ r, orientation r = 1 ∨ orientation r = -1
  owner : Reaction → Core
  owner_mem : ∀ r, r ∈ (core (owner r)).reactions

namespace CoreFamily

variable {Q : ReversibleCRN Species Reaction}

def CoveredBy (F : CoreFamily (Core := Core) Q) (r : Reaction) : Finset Core :=
  Finset.univ.filter fun k => r ∈ (F.core k).reactions

def MultiPAC (F : CoreFamily (Core := Core) Q) : Prop :=
  ∃ v : Reaction → ℝ,
    (∀ r, 0 < (F.orientation r : ℝ) * v r) ∧
    ∀ k, (F.core k).Productive v

def MultiCAC [Fintype Species] (F : CoreFamily (Core := Core) Q) : Prop :=
  ∃ z : Species → ℝ,
    (∀ s, 0 < z s) ∧
    (∀ r, 0 < (F.orientation r : ℝ) * Q.current z r) ∧
    ∀ k, (F.core k).Productive (Q.current z)

end CoreFamily

end ThermoCoreCompatibility

#print axioms ThermoCoreCompatibility.CoreFamily.MultiCAC
