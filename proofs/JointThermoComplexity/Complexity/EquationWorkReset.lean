module
public import proofs.JointThermoComplexity.Complexity.MainEquationWork

set_option autoImplicit false
@[expose] public section

/-! Fixed resets make local scratch bounds independent of the number of prior emitted nodes. -/

namespace JointThermoComplexity.Complexity.EquationWorkReset
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit LocalBranchState
open HeaderAt (Cursor)
open DInstabilityComplexity.MachineConstruction

def program : CounterProgram 9 := [.clear 0, .clear 1, .clear 2, .clear 3, .clear 4, .clear 5, .clear 6, .clear 7, .clear 8]
def zeroValues : Fin 9 → ℕ := fun _ => 0
def zeroCounts : Counts := ⟨0, 0, 0⟩

theorem program_eval (values : Fin 9 → ℕ) : counterProgramEval program values = zeroValues := by
  funext i
  fin_cases i <;> simp [program, counterProgramEval, CounterInstruction.eval, zeroValues]

def addresses : TM 32 := AddressCounterPlacement.machine program
def machine : TM 32 := seqTM addresses QueryCounterInit.clear

theorem addresses_hoareTime (counts : Counts) (values : Fin 9 → ℕ) (L p B : ℕ)
    (hv : ∀ i, values i ≤ B) (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    addresses.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready counts values L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready counts zeroValues L R work) (counterIterTime 9 B) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', ha, hb, hm, hp'⟩ :=
    AddressCounterPlacement.bounded_hoareTime program values B hv before input emitted
      (LocalBranchPrepare.Extra counts L p R) (LocalBranchPrepare.extra_stable counts L p R hR)
      inp work out ⟨hc, hs, hr.addresses, hr.basic, fun j _ hj => hr.markers j hj, hp⟩
  have ha' : AddressCounterPlacement.Registers zeroValues d.work := by simpa only [program_eval] using ha
  have hm' : ∀ j, j ≠ anchor → (d.work j).cells 0 = Γ.start := by
    intro j hj
    by_cases hblock : AddressCounterPlacement.InBlock j
    · have he : AddressCounterPlacement.slot (placeWorkCoord (post := 4) 19 9 j hblock) = j :=
        placeWorkIdx_placeWorkCoord (pre := 19) (post := 4) (n := 9) j hblock
      rw [← he]
      exact (ha' _).cell0
    · exact hm j hblock hj
  exact ⟨d, t, ht, hd, hh, hc', hs', hp', hb, hm', ha'⟩

theorem counters_hoareTime (counts : Counts) (values : Fin 9 → ℕ) (L p : ℕ)
    (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    QueryCounterInit.clear.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready counts values L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready zeroCounts values L R work) (2 * counts.total + 17) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hpos, hr'⟩ :=
    QueryCounterInit.clear_hoareTime counts L 0 before input emitted (QueryExtra p values R)
      (query_extra_stable p values R hR) inp work out
      ⟨hc, hs, hr.basic.positionReg, to_query counts values L p R work hr hp⟩
  have hf := from_query zeroCounts values L p R d.work hr' hpos
  exact ⟨d, t, ht, hd, hh, hc', hs', hf.2, hf.1⟩

def timeBound (counts : Counts) (B : ℕ) : ℕ := counterIterTime 9 B + 2 * counts.total + 18

theorem hoareTime (counts : Counts) (values : Fin 9 → ℕ) (L p B : ℕ)
    (hv : ∀ i, values i ≤ B) (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready counts values L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready zeroCounts zeroValues L R work) (timeBound counts B) := by
  have ha := addresses_hoareTime counts values L p B hv before input emitted R hR
  have hc := counters_hoareTime counts zeroValues L p before input emitted R hR
  have hseq := seqTM_hoareTime addresses QueryCounterInit.clear ha (by
    rintro inp work out ⟨hcur, hs, hp, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hs, hp, hr⟩) hc
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by dsimp [timeBound]; omega)

end JointThermoComplexity.Complexity.EquationWorkReset

#print axioms JointThermoComplexity.Complexity.EquationWorkReset.program_eval
#print axioms JointThermoComplexity.Complexity.EquationWorkReset.hoareTime
