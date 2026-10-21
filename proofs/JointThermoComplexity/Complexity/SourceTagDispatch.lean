module
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun
public import proofs.JointThermoComplexity.Complexity.SourceTagFlags

set_option autoImplicit false
@[expose] public section

/-! Finite tag dispatch through work flags, without emitting test bits. -/

namespace JointThermoComplexity.Complexity.SourceTagDispatch
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def machine : List (Fin w) → (List Bool → TM w) → TM w
  | [], branches => branches []
  | port :: ports, branches => FlagBranch.machine port
      (machine ports (fun bits => branches (true :: bits)))
      (machine ports (fun bits => branches (false :: bits)))

def Reads : List (Fin w) → List Bool → (Fin w → Tape) → Prop
  | [], [], _ => True
  | port :: ports, bit :: bits, work => (work port).read = Γ.ofBool bit ∧ Reads ports bits work
  | _, _, _ => False

theorem hoareTime (ports : List (Fin w)) (bits : List Bool) (hlen : bits.length = ports.length)
    (branches : List Bool → TM w) (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : (branches bits).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine ports branches).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work ∧ Reads ports bits work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (bound + 2 * ports.length) := by
  induction ports generalizing bits branches with
  | nil =>
    have hb : bits = [] := List.length_eq_zero_iff.mp hlen
    subst bits
    exact h.consequence (fun _ _ _ hp => ⟨hp.1, hp.2.1⟩) (fun _ _ _ hp => hp) (by simp)
  | cons port ports ih =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have hlen' : bits.length = ports.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen
      cases bit with
      | false =>
        have hbody := ih bits hlen' (fun bits => branches (false :: bits)) h
        have hb := FlagBranchRun.no_hoareTime port
          (machine ports (fun bits => branches (true :: bits)))
          (machine ports (fun bits => branches (false :: bits)))
          before input emitted before' input' emitted' (fun work => P work ∧ Reads ports bits work) Q
          (bound + 2 * ports.length) hbody
        exact hb.consequence (by
          rintro inp work out ⟨hc, hp, hf, hr⟩
          exact ⟨⟨hc, hp, hr⟩, hf⟩) (fun _ _ _ hp => hp) (by simp only [List.length_cons]; omega)
      | true =>
        have hbody := ih bits hlen' (fun bits => branches (true :: bits)) h
        have hb := FlagBranchRun.yes_hoareTime port
          (machine ports (fun bits => branches (true :: bits)))
          (machine ports (fun bits => branches (false :: bits)))
          before input emitted before' input' emitted' (fun work => P work ∧ Reads ports bits work) Q
          (bound + 2 * ports.length) hbody
        exact hb.consequence (by
          rintro inp work out ⟨hc, hp, hf, hr⟩
          exact ⟨⟨hc, hp, hr⟩, hf⟩) (fun _ _ _ hp => hp) (by simp only [List.length_cons]; omega)

end JointThermoComplexity.Complexity.SourceTagDispatch

#print axioms JointThermoComplexity.Complexity.SourceTagDispatch.hoareTime
