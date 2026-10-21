module
public import proofs.JointThermoComplexity.Complexity.MotifMaskDirections

set_option autoImplicit false
@[expose] public section

/-! Actual mask loading and direction emission change only the three mask/orientation buffers and current address. -/

namespace JointThermoComplexity.Complexity.MotifPassFrame
open _root_.Complexity
open _root_.Complexity.TM

def Unchanged (m : ℕ) (work work' : Fin (m + 15) → Tape) : Prop :=
  ∀ j, j ≠ MotifBufferPorts.buffer m 0 → j ≠ MotifBufferPorts.buffer m 1 →
    j ≠ MotifBufferPorts.buffer m 2 → j ≠ MonomialPorts.species (m + 1) → work' j = work j

theorem of_mask (m : ℕ) (k : Fin 2) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ MotifBufferPorts.buffer m k.castSucc → work' j = work j) : Unchanged m work work' := by
  intro j h0 h1 _ _
  have hk : k = 0 ∨ k = 1 := by
    have hi := k.isLt
    rcases show k.val = 0 ∨ k.val = 1 by omega with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext he)
  rcases hk with rfl | rfl
  · exact hw j h0
  · exact hw j h1

theorem of_direction (m : ℕ) (work work' : Fin (m + 15) → Tape)
    (hw : MotifDirectionFrame.Unchanged m work work') : Unchanged m work work' :=
  fun j _ hm hf hc => hw j hm hf hc

theorem box (m : ℕ) (work work' : Fin (m + 15) → Tape) (hw : Unchanged m work work') :
    BoxState.Unchanged m work work' := fun j hn ha hp _ hc => hw j hn ha hp hc

theorem metadata (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape) (hw : Unchanged m work work') :
    MotifBufferMeta.State m input work → MotifBufferMeta.State m input work' := by
  rintro ⟨hk, hr⟩
  have hbox := box m work work' hw
  exact ⟨BoxPins.frame m input work work' hbox hk, BoxRegisters.frame m input work work' hbox hr⟩

theorem outside (m : ℕ) (work work' : Fin (m + 15) → Tape) (hw : Unchanged m work work')
    (j : Fin (m + 15)) (hj : j.val = 6 ∨ 8 ≤ j.val) : work' j = work j := by
  apply hw j
  · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega

theorem ready_and (m L idx : ℕ) (R S : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape) :
    BoxState.Ready m L idx (fun work => R work ∧ S work) work ↔ BoxState.Ready m L idx R work ∧ S work := by
  simp only [BoxState.Ready, and_assoc]

end JointThermoComplexity.Complexity.MotifPassFrame

#print axioms JointThermoComplexity.Complexity.MotifPassFrame.metadata
#print axioms JointThermoComplexity.Complexity.MotifPassFrame.outside
