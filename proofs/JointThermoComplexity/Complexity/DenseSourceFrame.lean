module
public import proofs.JointThermoComplexity.Complexity.DenseFourTemplatePacket

set_option autoImplicit false
@[expose] public section

/-! A reusable source-pass boundary. Every source buffer remains reusable;
all four power heads are explicit fields, and loop fuel can be framed exactly. -/

namespace JointThermoComplexity.Complexity.DenseSourceFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun BoxBufferState
open BoundedOccurrenceMachine

def Outside (j : Fin 64) : Prop := 12 ≤ j.val ∧ DenseRowFrame.Outside j
def Stable (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, Outside j → next j = work j) → R work → R next
def Parser (L : ℕ) (work : Fin 64 → Tape) : Prop :=
  Reusable L (work 0) ∧ (work 1).head = 1 ∧
    Ready L DenseParserPorts.layout.Physical DenseParserPorts.layout.ending.castSucc DenseParserPorts.layout.flag.castSucc work

structure Core (n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop where
  adjusted : (work 12).head = 1
  arity : IsReg n (work 16)
  total : IsReg N (work 33)
  branch : IsReg (N + 2) (work 34)
  position : Register current (work 38)
  next : ∃ u, u ≤ N + 1 ∧ Register u (work 41)
  cell : Register 0 (work 39)
  comparison : (work 42).head = 1
  ending : Register (N + 1) (work 40)
  lastHead : (work 43).head = 1
  powers : ∀ i : Fin 4, (work (DensePowerPorts.flag 4 (by decide) i)).head = 1
  scratch : BinaryCopyRegister.Empty (work 63)
  frame : R work

def Work (L n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Parser L work ∧ Core n N current R work
def Pre (L n N current : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Work L n N current R work

theorem parser_transfer (L : ℕ) (work next : Fin 64 → Tape) (he : ∀ j, j.val < 12 → next j = work j)
    (hp : Parser L work) : Parser L next := by
  obtain ⟨hb, hh, hr⟩ := hp
  refine ⟨by rw [he 0 (by decide)]; exact hb, by rw [he 1 (by decide)]; exact hh, ?_, ?_, ?_⟩
  · intro p hmem
    have hm : p ∈ ([(2, 6), (3, 7), (4, 8), (5, 9)] : List (Fin 64 × Fin 64)) := hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have hd : p.1.val < 12 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    have hf : p.2.val < 12 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    rw [he p.1 hd, he p.2 hf]
    exact hr.1 p hmem
  · rw [he DenseParserPorts.layout.ending.castSucc (by decide)]; exact hr.2.1
  · rw [he DenseParserPorts.layout.flag.castSucc (by decide)]; exact hr.2.2

theorem row_low (j : Fin 64) (hj : j.val < 12) : DenseRowFrame.Outside j := by
  have hn (k : Fin 64) (hk : 12 ≤ k.val) : j ≠ k := by
    intro hh
    have hv := congrArg Fin.val hh
    omega
  exact ⟨hn 12 (by decide), hn 16 (by decide), hn 33 (by decide), hn 34 (by decide), hn 38 (by decide),
    hn 39 (by decide), hn 41 (by decide), hn 42 (by decide), hn 43 (by decide), hn 63 (by decide), Or.inl (by omega)⟩

def PacketR (L : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop := Parser L work ∧ R work
theorem packet_stable (L : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : DenseRowFrame.Stable (PacketR L R) := by
  rintro work next he ⟨hp, hr⟩
  exact ⟨parser_transfer L work next (fun j hj => he j (row_low j hj)) hp, hR work next (fun j hj => he j hj.2) hr⟩

theorem core_transfer (n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (work next : Fin 64 → Tape)
    (he : ∀ j, 12 ≤ j.val → next j = work j) (hp : Core n N current R work) : Core n N current R next := by
  obtain ⟨u, hu, hn⟩ := hp.next
  refine ⟨by rw [he 12 (by decide)]; exact hp.adjusted, by rw [he 16 (by decide)]; exact hp.arity,
    by rw [he 33 (by decide)]; exact hp.total, by rw [he 34 (by decide)]; exact hp.branch,
    by rw [he 38 (by decide)]; exact hp.position, ⟨u, hu, by rw [he 41 (by decide)]; exact hn⟩,
    by rw [he 39 (by decide)]; exact hp.cell, by rw [he 42 (by decide)]; exact hp.comparison,
    by rw [he 40 (by decide)]; exact hp.ending, by rw [he 43 (by decide)]; exact hp.lastHead, ?_,
    by rw [he 63 (by decide)]; exact hp.scratch, hR work next (fun j hj => he j hj.1) hp.frame⟩
  intro i
  rw [he (DensePowerPorts.flag 4 (by decide) i) (by change 12 ≤ 44 + i.val; omega)]
  exact hp.powers i

theorem core_parser_stable (n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    ∀ work next, (∀ j, j ≠ DenseParserPorts.layout.idx.castSucc → j ≠ DenseParserPorts.layout.sign.castSucc →
      ¬DenseParserPorts.layout.Touches j → next j = work j) → Core n N current R work → Core n N current R next := by
  intro work next he hp
  apply core_transfer n N current R hR work next _ hp
  intro j hj
  have hx := DenseParserPorts.parse_outside j hj
  exact he j hx.1 hx.2.1 hx.2.2

theorem bank_high (m : ℕ) (j : Fin 64) (hj : 12 ≤ j.val) : j ∉ DenseReferenceBank.unused m := by
  intro hm
  have hh := List.mem_of_mem_drop hm
  change j ∈ ([2, 3, 4, 5] : List (Fin 64)) at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl <;> contradiction

theorem core_bank_stable (m n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    DenseReferenceClear.Stable (DenseReferenceBank.unused m) (Core n N current R) := by
  intro work next he hp
  exact core_transfer n N current R hR work next (fun j hj => he j (bank_high m j hj)) hp

structure Keep (L v : ℕ) (negative : Bool) (work : Fin 64 → Tape) : Prop where
  coefficient : Reusable L (work 0)
  signHead : (work 1).head = 1
  markers : (work 6).head = 1 ∧ (work 7).head = 1 ∧ (work 8).head = 1 ∧
    (work 9).head = 1 ∧ (work 10).head = 1 ∧ (work 11).head = 1
  value : Register v (work 0)
  sign : (work 1).read = Γ.ofBool negative

theorem keep_of_parser (L v : ℕ) (negative : Bool) (work : Fin 64 → Tape) (hp : Parser L work)
    (hv : Register v (work 0)) (hn : (work 1).read = Γ.ofBool negative) : Keep L v negative work := by
  exact ⟨hp.1, hp.2.1, ⟨(hp.2.2.1 (2, 6) (by decide)).2,
    (hp.2.2.1 (3, 7) (by decide)).2, (hp.2.2.1 (4, 8) (by decide)).2,
    (hp.2.2.1 (5, 9) (by decide)).2, hp.2.2.2.1, hp.2.2.2.2⟩, hv, hn⟩

theorem ref_ready (L : ℕ) (work : Fin 64 → Tape) (hp : Parser L work) : DenseReferenceClear.Ready L DenseReferenceBank.slots work := by
  intro j hj
  change j ∈ ([2, 3, 4, 5] : List (Fin 64)) at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl
  · exact (hp.2.2.1 (2, 6) (by decide)).1
  · exact (hp.2.2.1 (3, 7) (by decide)).1
  · exact (hp.2.2.1 (4, 8) (by decide)).1
  · exact (hp.2.2.1 (5, 9) (by decide)).1

theorem parser_of_bank (L v : ℕ) (negative : Bool) (vs : List ℕ) (work : Fin 64 → Tape)
    (hb : DenseReferenceBank.Bank L vs work) (hk : Keep L v negative work) : Parser L work := by
  refine ⟨hk.coefficient, hk.signHead, ?_, hk.markers.2.2.2.2.1, hk.markers.2.2.2.2.2⟩
  intro p hp
  have hm : p ∈ ([(2, 6), (3, 7), (4, 8), (5, 9)] : List (Fin 64 × Fin 64)) := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨(hb 0).2, hk.markers.1⟩
  · exact ⟨(hb 1).2, hk.markers.2.1⟩
  · exact ⟨(hb 2).2, hk.markers.2.2.1⟩
  · exact ⟨(hb 3).2, hk.markers.2.2.2.1⟩

theorem keep_bank_stable (m L v : ℕ) (negative : Bool) : DenseReferenceClear.Stable (DenseReferenceBank.unused m) (Keep L v negative) := by
  rintro work next he hk
  have keep (j : Fin 64) (hj : j ∉ DenseReferenceBank.slots) : next j = work j :=
    he j (fun hh => hj (List.mem_of_mem_drop hh))
  refine ⟨by rw [keep 0 (by decide)]; exact hk.coefficient, by rw [keep 1 (by decide)]; exact hk.signHead, ?_,
    by rw [keep 0 (by decide)]; exact hk.value, by rw [keep 1 (by decide)]; exact hk.sign⟩
  rw [keep 6 (by decide), keep 7 (by decide), keep 8 (by decide), keep 9 (by decide), keep 10 (by decide), keep 11 (by decide)]
  exact hk.markers

theorem packet_pre (L n N current v : ℕ) (negative : Bool) (vs : List ℕ) (R : (Fin 64 → Tape) → Prop)
    (before input emitted : List Bool) (inp : Tape) (work : Fin 64 → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j))
    (hb : DenseReferenceBank.Bank L vs work) (hk : Keep L v negative work) (hp : Core n N current R work) :
    DensePacketControl.Pre current 4 (by decide) (DenseRawReady.values vs) n N v negative before input emitted (PacketR L R) inp work out := by
  obtain ⟨u, hu, hn⟩ := hp.next
  have href : PowerVectorUnit.Refs (DensePowerPorts.cellLayout 4 (by decide)) (DenseRawReady.values vs) work := by
    apply DensePowerPorts.refs
    · intro i; exact (hb i).1
    · exact hp.powers
  exact ⟨hc, hs, u, hu, hp.position, hn,
    ⟨hp.cell, hp.comparison, hp.total, hp.branch, href, hp.arity,
      hk.value, hk.sign, hp.adjusted, parser_of_bank L v negative vs work hb hk, hp.frame⟩,
    hp.ending, hp.lastHead, hp.scratch⟩

theorem packet_post (L n N current v : ℕ) (negative : Bool) (values : Fin 64 → ℕ) (R : (Fin 64 → Tape) → Prop)
    (before input emitted : List Bool) :
    ∀ inp work out, DensePacketControl.Pre current 4 (by decide) values n N v negative before input emitted (PacketR L R) inp work out →
      Pre L n N current before input emitted R inp work out := by
  rintro inp work out ⟨hc, hs, u, hu, hi, hn, ⟨hz, hcomp, hN, hb, href, ha, _hv, _hsign, hadj, hp, hr⟩, hend, hhead, ht⟩
  refine ⟨hc, hs, hp, ⟨hadj, ha, hN, hb, hi, ⟨u, hu, hn⟩, hz, hcomp, hend, hhead, ?_, ht, hr⟩⟩
  intro i
  exact (href (DensePowerPorts.comparison 4 (by decide) i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).2

end JointThermoComplexity.Complexity.DenseSourceFrame

#print axioms JointThermoComplexity.Complexity.DenseSourceFrame.packet_pre
#print axioms JointThermoComplexity.Complexity.DenseSourceFrame.packet_post
