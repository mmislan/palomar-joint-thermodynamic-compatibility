module
public import proofs.JointThermoComplexity.Complexity.SparseHeaderRaw
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset

set_option autoImplicit false
@[expose] public section

/-! Parse arity while retaining real output, then restore empty scratch. -/

namespace JointThermoComplexity.Complexity.SparseHeaderRouting
open _root_.Complexity _root_.Complexity.TM HeaderAt
open SparseHeaderRaw (arity flag sink Stable)

def machine : TM 33 := seqTM SparseHeaderRaw.machine (BinaryBufferReset.machine sink)

theorem hoareTime (before input emitted : List Bool) (R : (Fin 33 → Tape) → Prop) (hR : Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ IsReg 0 (work arity) ∧ (work flag).head = 1 ∧
          (work sink).HasBinaryString [] ∧ R work)
      (fun inp work out => Cursor (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) ∧
          IsReg (HeaderControl.count input) (work arity) ∧ (work flag).head = 1 ∧
            (work flag).read = Γ.ofBool (HeaderControl.valid input) ∧ IsReg 0 (work sink) ∧ R work)
      (5 * input.length + 15) := by
  let T : (Fin 33 → Tape) → Prop := fun work =>
    (∀ j, j ≠ sink → (work j).cells 0 = Γ.start) ∧ IsReg (HeaderControl.count input) (work arity) ∧
      (work flag).head = 1 ∧ (work flag).read = Γ.ofBool (HeaderControl.valid input) ∧ R work
  have hT : ∀ work next, (∀ j, j ≠ sink → next j = work j) → T work → T next := by
    rintro work next he ⟨hm, ha, hh, hv, hr⟩
    exact ⟨fun j hj => by rw [he j hj]; exact hm j hj,
      by rw [he arity (by decide)]; exact ha,
      by rw [he flag (by decide)]; exact hh,
      by rw [he flag (by decide)]; exact hv,
      hR work next (fun j _ _ hj => he j hj) hr⟩
  have hp := SparseHeaderRaw.hoareTime before input emitted R hR
  have hc := BinaryBufferReset.hoareTime sink (HeaderControl.copied input)
    (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted T hT
  have hs := seqTM_hoareTime _ _ hp (by
    rintro inp work out ⟨hcur, hsafe, hm, ha, hh, hv, hbuf, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hsafe, hbuf.2, hm sink, hbuf.1.le, (fun j _ => hm j), ha, hh, hv, hr⟩) hc
  apply hs.consequence
  · exact fun _ _ _ hp => hp
  · rintro inp work out ⟨hcur, hsafe, hz, hm, ha, hh, hv, hr⟩
    refine ⟨hcur, hsafe, ?_, ha, hh, hv, hz, hr⟩
    intro j
    by_cases hj : j = sink
    · subst j; exact hz.cell0
    · exact hm j hj
  · have hn := HeaderControl.count_le_length input
    have hb := HeaderControl.copied_length_le input
    omega

end JointThermoComplexity.Complexity.SparseHeaderRouting

#print axioms JointThermoComplexity.Complexity.SparseHeaderRouting.hoareTime
