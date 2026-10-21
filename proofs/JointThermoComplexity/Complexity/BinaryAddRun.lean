module
public import proofs.JointThermoComplexity.Complexity.BinaryAddScan
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun

set_option autoImplicit false
@[expose] public section

/-! Addition followed by source rewinds. Every original work tape is restored,
so arbitrary work predicates survive, including predicates on both sources. -/

namespace JointThermoComplexity.Complexity.BinaryAddRun
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def machine (left right : Fin w) : TM w :=
  seqTM (seqTM (BinaryAddMachine.machine left right) (rewindWorkTM left)) (rewindWorkTM right)

theorem string_eq {t u : Tape} {bits : List Bool} (ht : t.HasBinaryString bits) (hzt : t.cells 0 = Γ.start)
    (hu : u.HasBinaryString bits) (hzu : u.cells 0 = Γ.start) : t = u := by
  apply Tape.ext (ht.1.trans hu.1.symm)
  exact (BinaryTape.cells_of_content ht.2 hzt).trans (BinaryTape.cells_of_content hu.2 hzu).symm

theorem raw_hoareTime (left right : Fin w) (hne : left ≠ right) (xs ys before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work left).HasBinaryString xs ∧ (work left).cells 0 = Γ.start ∧
        (work right).HasBinaryString ys ∧ (work right).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BinaryAddControl.add false xs ys) inp work out ∧
        (∀ j, Parked (work j)) ∧ (work left).HasBinaryString xs ∧ (work left).cells 0 = Γ.start ∧
        (work right).HasBinaryString ys ∧ (work right).cells 0 = Γ.start ∧ R work)
      (2 * (xs.length + ys.length) + 9) := by
  rintro inp work out ⟨hc, hsafe, hleft, hzl, hright, hzr, hx⟩
  obtain ⟨d, td, htd, hd, hdh, hdi, hdlc, hdlh, hdrc, hdrh, hdo, hdp, hdz⟩ :=
    BinaryAddScan.scan xs ys [] [] emitted left right false ⟨.scan false, inp, work, out⟩
      hne rfl hleft.2 hleft.1 hright.2 hright.1 hc.input_read
      (fun j _ _ => (hc.works j).1) hc.tapePrefix hc.zero
  have hdl : (d.work left).HasBinaryPrefix xs :=
    ⟨by simpa only [List.length_nil, Nat.zero_add] using hdlh,
      by simpa only [Tape.HasBinaryContent, hdlc] using hleft.2⟩
  have hdr : (d.work right).HasBinaryPrefix ys :=
    ⟨by simpa only [List.length_nil, Nat.zero_add] using hdrh,
      by simpa only [Tape.HasBinaryContent, hdrc] using hright.2⟩
  have hdzl : (d.work left).cells 0 = Γ.start := by rw [hdlc]; exact hzl
  have hdzr : (d.work right).cells 0 = Γ.start := by rw [hdrc]; exact hzr
  have hdsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hjl : j = left
    · subst j
      exact ⟨by rw [hdl.1]; omega, (show (d.work left).HasBinaryContent xs from hdl.2).cells_ne_start⟩
    · by_cases hjr : j = right
      · subst j
        exact ⟨by rw [hdr.1]; omega, (show (d.work right).HasBinaryContent ys from hdr.2).cells_ne_start⟩
      · rw [hdo j hjl hjr]; exact hsafe j
  have hcurd : Cursor before input (emitted ++ BinaryAddControl.add false xs ys) d.input d.work d.output :=
    ⟨by simpa only [hdi] using hc.cells, by simpa only [hdi] using hc.head,
      fun j => ⟨(hdsafe j).read_ne_start, (hdsafe j).1⟩, hdp, hdz⟩
  let S : (Fin w → Tape) → Prop := fun next => ∀ j, j ≠ left → next j = d.work j
  have hS : ∀ old next, (∀ j, j ≠ left → next j = old j) → S old → S next := by
    intro old next he ho j hj
    exact (he j hj).trans (ho j hj)
  obtain ⟨e, te, hte, he, heh, hcure, hesafe, hel, hezl, heo⟩ :=
    BinaryPrefixRewind.hoareTime left xs before input (emitted ++ BinaryAddControl.add false xs ys) S hS
      d.input d.work d.output ⟨hcurd, hdsafe, hdl, hdzl, fun _ _ => rfl⟩
  have heleft : e.work left = work left := string_eq hel hezl hleft hzl
  have her : (e.work right).HasBinaryPrefix ys := by rw [heo right hne.symm]; exact hdr
  have hezr : (e.work right).cells 0 = Γ.start := by rw [heo right hne.symm]; exact hdzr
  let T : (Fin w → Tape) → Prop := fun next => ∀ j, j ≠ right → next j = e.work j
  have hT : ∀ old next, (∀ j, j ≠ right → next j = old j) → T old → T next := by
    intro old next he ho j hj
    exact (he j hj).trans (ho j hj)
  obtain ⟨f, tf, htf, hf, hfh, hcurf, hfsafe, hfr, hfzr, hfo⟩ :=
    BinaryPrefixRewind.hoareTime right ys before input (emitted ++ BinaryAddControl.add false xs ys) T hT
      e.input e.work e.output ⟨hcure, hesafe, her, hezr, fun _ _ => rfl⟩
  have hfright : f.work right = work right := string_eq hfr hfzr hright hzr
  have hwork : f.work = work := by
    funext j
    by_cases hjr : j = right
    · subst j; exact hfright
    · rw [hfo j hjr]
      by_cases hjl : j = left
      · subst j; exact heleft
      · exact (heo j hjl).trans (hdo j hjl hjr)
  have he' : (rewindWorkTM left).reachesIn te
      ⟨(rewindWorkTM left).qstart, transitionInput d.input, (fun j => transitionTape (d.work j)), transitionTape d.output⟩ e := by
    obtain ⟨hi, hw, ho⟩ := hcurd.phase
    rw [hi, hw, ho]
    exact he
  let first := seqTM (BinaryAddMachine.machine left right) (rewindWorkTM left)
  have hfirst := seqTM_reachesIn_of_reachesIn (BinaryAddMachine.machine left right) (rewindWorkTM left) hd hdh he'
  have hfirsthalt := (phase2Wrap_halted_iff (BinaryAddMachine.machine left right) (rewindWorkTM left) e).mpr heh
  have hf' : (rewindWorkTM right).reachesIn tf
      ⟨(rewindWorkTM right).qstart, transitionInput e.input, (fun j => transitionTape (e.work j)), transitionTape e.output⟩ f := by
    obtain ⟨hi, hw, ho⟩ := hcure.phase
    rw [hi, hw, ho]
    exact hf
  have hfull := seqTM_reachesIn_of_reachesIn first (rewindWorkTM right) hfirst hfirsthalt hf'
  refine ⟨phase2Wrap first (rewindWorkTM right) f, (td + 1 + te) + 1 + tf, by omega,
    hfull, (phase2Wrap_halted_iff first (rewindWorkTM right) f).mpr hfh,
    hcurf, hfsafe, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [phase2Wrap, hwork] using hleft
  · simpa only [phase2Wrap, hwork] using hzl
  · simpa only [phase2Wrap, hwork] using hright
  · simpa only [phase2Wrap, hwork] using hzr
  · simpa only [phase2Wrap, hwork] using hx

theorem natural_hoareTime (left right : Fin w) (hne : left ≠ right) (m n : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        BinaryIncrementRun.Register m (work left) ∧ BinaryIncrementRun.Register n (work right) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BinaryAddControl.add false m.bits n.bits) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register m (work left) ∧
        BinaryIncrementRun.Register n (work right) ∧ R work)
      (2 * (m.bits.length + n.bits.length) + 9) := by
  apply (raw_hoareTime left right hne m.bits n.bits before input emitted R).consequence
  · rintro inp work out ⟨hc, hs, hl, hr, hx⟩
    exact ⟨hc, hs, hl.1, hl.2, hr.1, hr.2, hx⟩
  · rintro inp work out ⟨hc, hs, hl, hzl, hr, hzr, hx⟩
    exact ⟨hc, hs, ⟨hl, hzl⟩, ⟨hr, hzr⟩, hx⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.BinaryAddRun

#print axioms JointThermoComplexity.Complexity.BinaryAddRun.machine
#print axioms JointThermoComplexity.Complexity.BinaryAddRun.raw_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryAddRun.natural_hoareTime
