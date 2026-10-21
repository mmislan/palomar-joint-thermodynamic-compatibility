module
public import proofs.JointThermoComplexity.Complexity.LocalBranchQuery

set_option autoImplicit false
@[expose] public section

/-! Preparing local addresses preserves the query frame and the saved outer cursor. -/

namespace JointThermoComplexity.Complexity.LocalBranchPrepare
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryCounterInit LocalBranchState

def Extra (counts : Counts) (L p : ℕ) (R : Work → Prop) (work : Work) : Prop :=
  Basic counts L R work ∧
    (∀ j, ¬AddressCounterPlacement.InBlock j → j ≠ anchor → (work j).cells 0 = Γ.start) ∧
    IsReg p (work anchor)

theorem anchor_outside : ¬AddressCounterPlacement.InBlock anchor := by
  unfold AddressCounterPlacement.InBlock placeWorkInMiddle
  decide

theorem extra_stable (counts : Counts) (L p : ℕ) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    AddressCounterPlacement.Stable (Extra counts L p R) := by
  rintro work work' he ⟨hb, hm, hp⟩
  refine ⟨basic_transfer counts L R work work' hb (fun j hj => he j (basic_address j hj))
    (hR work work' (fun j hj => he j (protected_address j hj)) hb.frame), ?_, ?_⟩
  · intro j hj ha
    simpa only [he j hj] using hm j hj ha
  · simpa only [he anchor anchor_outside] using hp

theorem hoareTime (kind : LocalEquationTemplates.Kind) (counts : Counts) (values : Fin 9 → ℕ)
    (L p B : ℕ) (hv : ∀ i, values i ≤ B) (before input emitted : List Bool)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (PreparedLocalEquation.machine kind).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready counts values L R work)
      (fun inp work out => Cursor before input
        (emitted ++ RowEntriesCodec.entries (LocalEquationTemplates.wordRows kind (LocalAddressSetup.addressValues values)))
        inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧
          Ready counts (LocalAddressSetup.prepared values) L R work)
      (PreparedLocalEquation.timeBound B) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', ha', _, hb', hm', hp'⟩ :=
    PreparedLocalEquation.hoareTime kind values B hv before input emitted (Extra counts L p R)
      (extra_stable counts L p R hR) inp work out
      ⟨hc, hs, hr.addresses, hr.basic.scratchReg, hr.basic, fun j _ hj => hr.markers j hj, hp⟩
  have hm : ∀ j, j ≠ anchor → (d.work j).cells 0 = Γ.start := by
    intro j hj
    by_cases ha : AddressCounterPlacement.InBlock j
    · have he : AddressCounterPlacement.slot (placeWorkCoord (post := 4) 19 9 j ha) = j :=
        placeWorkIdx_placeWorkCoord (pre := 19) (post := 4) (n := 9) j ha
      rw [← he]
      exact (ha' _).cell0
    · exact hm' j ha hj
  exact ⟨d, t, ht, hd, hh, hc', hs', hp', hb', hm, ha'⟩

end JointThermoComplexity.Complexity.LocalBranchPrepare

#print axioms JointThermoComplexity.Complexity.LocalBranchPrepare.extra_stable
#print axioms JointThermoComplexity.Complexity.LocalBranchPrepare.hoareTime
