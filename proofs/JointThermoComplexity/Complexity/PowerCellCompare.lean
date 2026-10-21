module
public import proofs.JointThermoComplexity.Complexity.RetainedBinaryEquality

set_option autoImplicit false
@[expose] public section

/-! Static lists of binary comparisons retain the loaded values and accumulated flags. -/

namespace JointThermoComplexity.Complexity.PowerCellCompare
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def machine : List (Ports w) → TM (w + 1)
  | [] => emitBitsTM []
  | p :: rest => seqTM (BinaryEqualityFlag.machine p) (machine rest)

def Separated (ps : List (Ports w)) : Prop :=
  ∀ p ∈ ps, ∀ q ∈ ps, p.operand ≠ q.flag ∧ p.constant ≠ q.flag

def Unique (ps : List (Ports w)) : Prop := ps.Pairwise (fun p q => p.flag ≠ q.flag)

def Ready (ps : List (Ports w)) (values : Fin (w + 1) → ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ p ∈ ps, Register (values p.operand) (work p.operand) ∧
    Register (values p.constant) (work p.constant) ∧ (work p.flag).head = 1

def Flags (ps : List (Ports w)) (values : Fin (w + 1) → ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ p ∈ ps, (work p.flag).read = Γ.ofBool (decide (values p.operand ≠ values p.constant))

def Same (ps : List (Ports w)) (work next : Fin (w + 1) → Tape) : Prop :=
  ∀ j, (∀ p ∈ ps, j ≠ p.flag) → next j = work j

def Stable (ps : List (Ports w)) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, Same ps work next → R work → R next

theorem run (ps : List (Ports w)) (values : Fin (w + 1) → ℕ) (B : ℕ)
    (hsep : Separated ps) (hu : Unique ps)
    (hbits : ∀ p ∈ ps, (values p.operand).bits.length ≤ B ∧ (values p.constant).bits.length ≤ B)
    (before input emitted : List Bool) (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j))
    (hr : Ready ps values work) :
    ∃ d t, t ≤ ps.length * (24 * B + 22) ∧
      (machine ps).reachesIn t ⟨(machine ps).qstart, inp, work, out⟩ d ∧ (machine ps).halted d ∧
      Cursor before input emitted d.input d.work d.output ∧ (∀ j, Parked (d.work j)) ∧
      Ready ps values d.work ∧ Flags ps values d.work ∧ Same ps work d.work := by
  induction ps generalizing inp work out with
  | nil =>
    exact ⟨⟨(machine []).qhalt, inp, work, out⟩, 0, Nat.zero_le _, .zero, rfl, hc, hs,
      by simp [Ready], by simp [Flags], fun _ _ => rfl⟩
  | cons p rest ih =>
    have hpair := List.pairwise_cons.mp hu
    let C : (Fin (w + 1) → Tape) → Prop := fun next => ∀ j, j ≠ p.flag → next j = work j
    have hC : RetainedBinaryEquality.Stable p C := by
      intro old next he ho j hj
      exact (he j hj).trans (ho j hj)
    have hp := hr p List.mem_cons_self
    have hb := hbits p List.mem_cons_self
    obtain ⟨c, tc, htc, hcr, hch, ⟨hcc, hcs, _, _, hcf, hcC⟩, hcv⟩ :=
      RetainedBinaryEquality.hoareTime p (values p.operand) (values p.constant) B hb.1 hb.2
        before input emitted C hC inp work out ⟨hc, hs, hp.1, hp.2.1, hp.2.2, fun _ _ => rfl⟩
    have hrestsep : Separated rest := fun q hq r hh =>
      hsep q (List.mem_cons_of_mem _ hq) r (List.mem_cons_of_mem _ hh)
    have hrestbits : ∀ q ∈ rest, (values q.operand).bits.length ≤ B ∧ (values q.constant).bits.length ≤ B :=
      fun q hq => hbits q (List.mem_cons_of_mem _ hq)
    have hready : Ready rest values c.work := by
      intro q hq
      have hqall := List.mem_cons_of_mem p hq
      have hqsep := hsep q hqall p List.mem_cons_self
      have hqflag : q.flag ≠ p.flag := Ne.symm (hpair.1 q hq)
      rw [hcC q.operand hqsep.1, hcC q.constant hqsep.2, hcC q.flag hqflag]
      exact hr q hqall
    obtain ⟨d, td, htd, hdr, hdh, hdc, hds, hdrdy, hdflags, hdsame⟩ :=
      ih hrestsep hpair.2 hrestbits c.input c.work c.output hcc hcs hready
    have hpkeep : d.work p.flag = c.work p.flag := hdsame p.flag hpair.1
    have hsame : Same (p :: rest) work d.work := by
      intro j hj
      exact (hdsame j (fun q hq => hj q (List.mem_cons_of_mem _ hq))).trans (hcC j (hj p List.mem_cons_self))
    have hreadyall : Ready (p :: rest) values d.work := by
      intro q hq
      refine ⟨?_, ?_, ?_⟩
      · rw [hsame q.operand (fun r hh => (hsep q hq r hh).1)]
        exact (hr q hq).1
      · rw [hsame q.constant (fun r hh => (hsep q hq r hh).2)]
        exact (hr q hq).2.1
      · rcases List.mem_cons.mp hq with he | hq
        · subst q
          simpa only [hpkeep] using hcf
        · exact (hdrdy q hq).2.2
    have hflags : Flags (p :: rest) values d.work := by
      intro q hq
      rcases List.mem_cons.mp hq with he | hq
      · subst q
        simpa only [hpkeep] using hcv
      · exact hdflags q hq
    obtain ⟨hi, hw, ho⟩ := hcc.phase
    have hrr : (machine rest).reachesIn td
        ⟨(machine rest).qstart, transitionInput c.input,
          (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
      rw [hi, hw, ho]
      exact hdr
    have hreach := seqTM_reachesIn_of_reachesIn (BinaryEqualityFlag.machine p) (machine rest) hcr hch hrr
    exact ⟨phase2Wrap (BinaryEqualityFlag.machine p) (machine rest) d, tc + 1 + td,
      by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega,
      hreach, (phase2Wrap_halted_iff _ _ d).mpr hdh, hdc, hds, hreadyall, hflags, hsame⟩

theorem hoareTime (ps : List (Ports w)) (values : Fin (w + 1) → ℕ) (B : ℕ)
    (hsep : Separated ps) (hu : Unique ps)
    (hbits : ∀ p ∈ ps, (values p.operand).bits.length ≤ B ∧ (values p.constant).bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable ps R) :
    (machine ps).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready ps values work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Ready ps values work ∧ Flags ps values work ∧ R work) (ps.length * (24 * B + 22)) := by
  rintro inp work out ⟨hc, hs, hr, hx⟩
  obtain ⟨d, t, ht, hdr, hdh, hdc, hds, hdrdy, hdf, hsame⟩ :=
    run ps values B hsep hu hbits before input emitted inp work out hc hs hr
  exact ⟨d, t, ht, hdr, hdh, hdc, hds, hdrdy, hdf, hR work d.work hsame hx⟩

end JointThermoComplexity.Complexity.PowerCellCompare

#print axioms JointThermoComplexity.Complexity.PowerCellCompare.run
#print axioms JointThermoComplexity.Complexity.PowerCellCompare.hoareTime
