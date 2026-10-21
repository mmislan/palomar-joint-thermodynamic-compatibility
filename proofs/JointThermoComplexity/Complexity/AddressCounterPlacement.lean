module
public import proofs.Complexitylib.Models.TuringMachine.Placement.Internal
public import proofs.DInstabilityComplexity.CounterProgramBounds
public import proofs.JointThermoComplexity.Complexity.VirtualCursor
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! Place the checked finite counter compiler on address ports19..27 with an arbitrary outside frame. -/

namespace JointThermoComplexity.Complexity.AddressCounterPlacement
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DInstabilityComplexity.MachineConstruction

def slot (i : Fin 9) : Fin 32 := placeWorkIdx 19 4 i
def InBlock (j : Fin 32) : Prop := placeWorkInMiddle (post := 4) 19 9 j

def Registers (values : Fin 9 → ℕ) (work : Fin 32 → Tape) : Prop := ∀ i, IsReg (values i) (work (slot i))

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, ¬InBlock j → work' j = work j) → R work → R work'

def machine (program : CounterProgram 9) : TM 32 := placeWorkTM 19 4 (counterProgramMachine program)

theorem input_parked {before input emitted : List Bool} {inp out : Tape} {work : Fin 32 → Tape}
    (hc : Cursor before input emitted inp work out) : Parked inp :=
  ⟨by rw [hc.head]; omega, (VirtualCursor.input_safe hc).2⟩

theorem hoareTime (program : CounterProgram 9) (values : Fin 9 → ℕ) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    (machine program).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Registers values work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Registers (counterProgramEval program values) work ∧ R work) (counterProgramTime program values) := by
  rintro inp work out ⟨hc, hs, hv, hr⟩
  have hout : OutAcc emitted out := (FixedOutput.outAcc_iff emitted out).mpr ⟨hc.tapePrefix, hc.zero⟩
  obtain ⟨d, t, ht, hd, hh, hi, hw, ho⟩ :=
    counterProgramMachine_hoareTime program values inp emitted (input_parked hc)
      inp (counterValues values) out ⟨rfl, rfl, hout⟩
  let D := placeWorkCfg (counterProgramMachine program) 19 4 work d
  have hstart : placeWorkCfg (counterProgramMachine program) 19 4 work
      ⟨(counterProgramMachine program).qstart, inp, counterValues values, out⟩ =
        ⟨(machine program).qstart, inp, work, out⟩ := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      dsimp only [placeWorkCfg]
      split
      · rename_i hj
        have he := (hv (placeWorkCoord (post := 4) 19 9 j hj)).eq_regT
        rw [show slot (placeWorkCoord (post := 4) 19 9 j hj) = j from
          placeWorkIdx_placeWorkCoord (pre := 19) (post := 4) (n := 9) j hj] at he
        exact he.symm
      · rfl
    · rfl
  have hreach := placeWorkTM_reachesIn_placeWorkCfg_stable_internal (counterProgramMachine program) 19 4 work hd
    (fun j _ => (hs j).read_ne_start)
  rw [hstart] at hreach
  have hreg : Registers (counterProgramEval program values) D.work := by
    intro i
    change IsReg _ (if h : placeWorkInMiddle (post := 4) 19 9 (slot i) then d.work (placeWorkCoord (post := 4) 19 9 (slot i) h) else work (slot i))
    simp only [slot, placeWorkInMiddle_placeWorkIdx, ↓reduceDIte, placeWorkCoord_placeWorkIdx]
    rw [hw]
    exact reg_regT _
  have hother : ∀ j, ¬InBlock j → D.work j = work j := by
    intro j hj
    change (if h : placeWorkInMiddle (post := 4) 19 9 j then d.work (placeWorkCoord (post := 4) 19 9 j h) else work j) = _
    change ¬placeWorkInMiddle (post := 4) 19 9 j at hj
    simp only [hj, ↓reduceDIte]
  have hsafe : ∀ j, Parked (D.work j) := by
    intro j
    by_cases hj : InBlock j
    · have hk : slot (placeWorkCoord (post := 4) 19 9 j hj) = j :=
        placeWorkIdx_placeWorkCoord (pre := 19) (post := 4) (n := 9) j hj
      rw [← hk]
      exact (hreg _).parked
    · rw [hother j hj]
      exact hs j
  have hcur : Cursor before input emitted D.input D.work D.output :=
    ⟨by simpa only [D, placeWorkCfg, hi] using hc.cells, by simpa only [D, placeWorkCfg, hi] using hc.head,
      fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      (FixedOutput.outAcc_iff emitted d.output).mp ho |>.1, (FixedOutput.outAcc_iff emitted d.output).mp ho |>.2⟩
  exact ⟨D, t, ht, hreach, hh, hcur, hsafe, hreg, hR work D.work hother hr⟩

theorem bounded_hoareTime (program : CounterProgram 9) (values : Fin 9 → ℕ) (B : ℕ) (hv : ∀ i, values i ≤ B)
    (before input emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    (machine program).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Registers values work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Registers (counterProgramEval program values) work ∧ R work) (counterIterTime program.length B) :=
  (hoareTime program values before input emitted R hR).mono_bound (counterProgramTime_bound program values B hv)

end JointThermoComplexity.Complexity.AddressCounterPlacement

#print axioms JointThermoComplexity.Complexity.AddressCounterPlacement.hoareTime
#print axioms JointThermoComplexity.Complexity.AddressCounterPlacement.bounded_hoareTime
