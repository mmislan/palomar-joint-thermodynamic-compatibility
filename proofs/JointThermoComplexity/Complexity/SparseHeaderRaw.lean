module
public import proofs.JointThermoComplexity.Complexity.HeaderAt
public import proofs.JointThermoComplexity.Complexity.VirtualCursor
public import proofs.JointThermoComplexity.Complexity.OutputRoute

set_option autoImplicit false
@[expose] public section

/-! Parse source arity16 with flag11, copying the header to temporary scratch32.
The routing proof follows RoutedEquationHeader; original sources are preserved. -/

namespace JointThermoComplexity.Complexity.SparseHeaderRaw
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)

def permutation : Fin 32 ≃ Fin 32 := (Equiv.swap 30 16).trans (Equiv.swap 31 11)
def arity : Fin 33 := 16
def flag : Fin 33 := 11
def sink : Fin 33 := Fin.last 32

theorem counter_permutation : HeaderAt.counter permutation = 16 := by decide
theorem flag_permutation : HeaderAt.flag permutation = 11 := by decide
theorem cast_counter : (16 : Fin 32).castSucc = arity := by decide
theorem cast_flag : (11 : Fin 32).castSucc = flag := by decide

def machine : TM 33 := (HeaderAt.machine permutation).retargetOutput
def Stable (R : (Fin 33 → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, j ≠ arity → j ≠ flag → j ≠ sink → work' j = work j) → R work → R work'

theorem hoareTime (before input emitted : List Bool) (R : (Fin 33 → Tape) → Prop) (hR : Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ IsReg 0 (work arity) ∧ (work flag).head = 1 ∧
          (work sink).HasBinaryString [] ∧ R work)
      (fun inp work out => Cursor (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) ∧
          IsReg (HeaderControl.count input) (work arity) ∧ (work flag).head = 1 ∧
            (work flag).read = Γ.ofBool (HeaderControl.valid input) ∧
              (work sink).HasBinaryPrefix (HeaderControl.copied input) ∧ R work)
      (2 * HeaderControl.count input + 5) := by
  rintro inp work out ⟨hc, hs, hm, hz, hf, hb, hr⟩
  let inner : Fin 32 → Tape := fun j => work j.castSucc
  let C : (Fin 32 → Tape) → Prop := fun work' =>
    ∀ j, j ≠ HeaderAt.counter permutation → j ≠ HeaderAt.flag permutation → work' j = inner j
  have hC : ∀ work' work'', (∀ j, j ≠ HeaderAt.counter permutation → j ≠ HeaderAt.flag permutation → work'' j = work' j) →
      C work' → C work'' := by
    intro work' work'' he hh j hc hf
    exact (he j hc hf).trans (hh j hc hf)
  have hvirtual : Cursor before input [] inp inner (work sink) :=
    ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, ⟨hb.1, hb.2⟩, hm sink⟩
  have hheader := HeaderAt.hoareTime permutation before input [] C hC
  have hroute := OutputRoute.hoareTime (HeaderAt.machine permutation) _ _ _ (fun t => t = out) hheader
  obtain ⟨d, t, ht, hd, hh, _, hout, hcur, hreg, hfh, hfr, he⟩ :=
    hroute inp work out ⟨hc.output_read, rfl, hvirtual,
      by simpa only [counter_permutation, cast_counter] using hz,
      by simpa only [flag_permutation, cast_flag] using hf, fun _ _ _ => rfl⟩
  simp only [List.nil_append] at hcur
  have hmarkers := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hm j, (hs j).2⟩) (VirtualCursor.output_safe hc)
  have hcast (j : Fin 33) (hj : j ≠ sink) : j.val < 32 := by
    by_contra hn
    apply hj
    apply Fin.ext
    change j.val = 32
    omega
  have hhead : ∀ j, 1 ≤ (d.work j).head := by
    intro j
    by_cases hj : j = sink
    · subst j
      change 1 ≤ (d.work (Fin.last (30 + 2))).head
      rw [hcur.tapePrefix.1]
      omega
    · let k : Fin 32 := ⟨j.val, hcast j hj⟩
      have hk : k.castSucc = j := by apply Fin.ext; rfl
      simpa only [hk] using (hcur.works k).2
  have hsafe : ∀ j, Parked (d.work j) := fun j => ⟨hhead j, (hmarkers.2.1 j).2⟩
  have hother : ∀ j, j ≠ arity → j ≠ flag → j ≠ sink → d.work j = work j := by
    intro j h18 h14 h31
    let k : Fin 32 := ⟨j.val, hcast j h31⟩
    have hk : k.castSucc = j := by apply Fin.ext; rfl
    have hkc : k ≠ HeaderAt.counter permutation := by
      rw [counter_permutation]
      intro hh
      apply h18
      apply Fin.ext
      change j.val = 16
      exact congrArg (fun z : Fin 32 => z.val) hh
    have hkf : k ≠ HeaderAt.flag permutation := by
      rw [flag_permutation]
      intro hh
      apply h14
      apply Fin.ext
      change j.val = 11
      exact congrArg (fun z : Fin 32 => z.val) hh
    simpa only [inner, hk] using he k hkc hkf
  have hcursor : Cursor (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted d.input d.work d.output :=
    ⟨hcur.cells, hcur.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [hout] using hc.tapePrefix, by simpa only [hout] using hc.zero⟩
  exact ⟨d, t, ht, hd, hh, hcursor, hsafe, fun j => (hmarkers.2.1 j).1,
    by simpa only [counter_permutation, cast_counter] using hreg,
    by simpa only [flag_permutation, cast_flag] using hfh,
    by simpa only [flag_permutation, cast_flag] using hfr,
    by simpa only [sink] using hcur.tapePrefix, hR work d.work hother hr⟩

end JointThermoComplexity.Complexity.SparseHeaderRaw

#print axioms JointThermoComplexity.Complexity.SparseHeaderRaw.hoareTime
