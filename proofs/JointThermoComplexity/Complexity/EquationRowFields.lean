module
public import proofs.JointThermoComplexity.Complexity.EquationRowFrame

set_option autoImplicit false
@[expose] public section

/-! Actual row-field operations with exact retained tapes. Each operation
frames every tape outside its own ports, including surrounding emitter data.
-/

namespace JointThermoComplexity.Complexity.EquationRowFields
open _root_.Complexity _root_.Complexity.TM BoxBufferState EquationRowControl EquationRowFrame
open HeaderAt (Cursor)
variable {w : ℕ}

theorem read_flags (s : State) (i k j : Fin 3) : ((EquationRowControl.read s i).terms k).flags j = (s.terms k).flags j := by
  by_cases hk : k = i <;> simp [EquationRowControl.read, hk]
theorem read_words (s : State) (i k : Fin 3) (j : Fin 2) : ((EquationRowControl.read s i).terms k).words j = (s.terms k).words j := by
  by_cases hk : k = i <;> simp [EquationRowControl.read, hk]
theorem read_coefficient (s : State) (i k : Fin 3) : ((EquationRowControl.read s i).terms k).coefficient = (s.terms k).coefficient := by
  by_cases hk : k = i <;> simp [EquationRowControl.read, hk]
theorem coefficient_presence (s : State) (i k : Fin 3) : ((EquationRowControl.coefficient s i).terms k).present = (s.terms k).present := by
  by_cases hk : k = i <;> simp [EquationRowControl.coefficient, hk]
theorem coefficient_flags (s : State) (i k j : Fin 3) : ((EquationRowControl.coefficient s i).terms k).flags j = (s.terms k).flags j := by
  by_cases hk : k = i <;> simp [EquationRowControl.coefficient, hk]
theorem coefficient_words (s : State) (i k : Fin 3) (j : Fin 2) : ((EquationRowControl.coefficient s i).terms k).words j = (s.terms k).words j := by
  by_cases hk : k = i <;> simp [EquationRowControl.coefficient, hk]
theorem monomial_presence (fuel : ℕ) (s : State) (i k : Fin 3) : ((monomial fuel s i).terms k).present = (s.terms k).present := by
  by_cases hk : k = i <;> simp [monomial, hk]
theorem monomial_coefficient (fuel : ℕ) (s : State) (i k : Fin 3) : ((monomial fuel s i).terms k).coefficient = (s.terms k).coefficient := by
  by_cases hk : k = i <;> simp [monomial, hk]

theorem read_hoareTime (p : Ports w) (s : State) (i : Fin 3) (B : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (SourceBitRead.machine (p.presence i) p.available).HoareTime
      (Logical p s B emitted R) (Logical p (EquationRowControl.read s i) B emitted R) 1 := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next => ∀ k, k ≠ p.presence i → k ≠ p.available → next k = work k
  have hC : ∀ a b, (∀ k, k ≠ p.presence i → k ≠ p.available → b k = a k) → C a → C b := by
    intro a b he ha k hi hv
    exact (he k hi hv).trans (ha k hi hv)
  obtain ⟨d, time, ht, hd, hh, hc', hs, hp, hv, hread, havail, he⟩ :=
    SourceBitRead.hoareTime (p.presence i) p.available (p.presence_available i) s.before s.input emitted C hC
      inp work out ⟨hc, hr.safe, (hr.presence i).1, hr.available_head, fun _ _ _ => rfl⟩
  refine ⟨d, time, ht, hd, hh, hc', ?_⟩
  refine ⟨hs, ?_, ?_, ?_, ?_, hv, havail, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = i
    · subst k
      simpa only [EquationRowControl.read, Function.update_self] using And.intro hp hread
    · simpa only [EquationRowControl.read, Function.update_of_ne hk,
        he _ (p.presence_ne hk) (p.presence_available k)] using hr.presence k
  · intro k j
    rw [read_flags, he (p.flag k j) (p.slot_presence k _ i) (p.slot_available k _)]
    exact hr.flags k j
  · intro k j
    rw [read_words, he (p.word k j) (p.slot_presence k _ i) (p.slot_available k _)]
    exact hr.words k j
  · intro k
    rw [read_coefficient, he (p.coefficient k) (p.slot_presence k 5 i) (p.slot_available k 5)]
    exact hr.coefficients k
  · simpa only [he _ (p.presence_loop i).symm (p.separate 22 21 (by decide))] using hr.loop_head
  · simpa only [he p.scratch (p.separate 23 (Ports.presenceIndex i) (by dsimp [Ports.presenceIndex]; omega))
      (p.separate 23 21 (by decide))] using hr.scratch
  · simpa only [he p.fuel (p.separate 24 (Ports.presenceIndex i) (by dsimp [Ports.presenceIndex]; omega))
      (p.separate 24 21 (by decide))] using hr.fuel
  · exact hR work d.work (fun k hk => he k (hk _) (hk _)) hr.extra

theorem coefficient_hoareTime (p : Ports w) (s : State) (i : Fin 3) (B : ℕ) (hB : 2 ≤ B)
    (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (EquationCoefficientLoad.machine (p.coefficient i)).HoareTime
      (Logical p s B emitted R) (Logical p (EquationRowControl.coefficient s i) B emitted R) (13 * B + 40) := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next => ∀ k, k ≠ p.coefficient i → next k = work k
  have hC : ∀ a b, (∀ k, k ≠ p.coefficient i → b k = a k) → C a → C b := by
    intro a b he ha k hi
    exact (he k hi).trans (ha k hi)
  have hb := hr.coefficients i
  have hreusable : Reusable B (work (p.coefficient i)) :=
    ⟨(s.terms i).coefficient, hb.2.2, hb.1.2, hb.2.1, by rw [hb.1.1]; omega⟩
  obtain ⟨d, time, ht, hd, hh, hc', hs, hb', hreuse, he⟩ :=
    EquationCoefficientLoad.hoareTime B hB (p.coefficient i) s.before s.input emitted C hC
      inp work out ⟨hc, hr.safe, hreusable, fun _ _ => rfl⟩
  obtain ⟨_, _, _, hz, _⟩ := hreuse
  have hcur : Cursor (EquationRowControl.coefficient s i).before (EquationRowControl.coefficient s i).input emitted d.input d.work d.output := by
    simpa only [EquationRowControl.coefficient, EquationCoefficientControl.signed_taken, EquationCoefficientControl.signed_rest] using hc'
  refine ⟨d, time, by omega, hd, hh, hcur, ?_⟩
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR work d.work (fun k hk => he k (hk _)) hr.extra⟩
  · intro k
    rw [coefficient_presence, he _ (p.slot_presence i 5 k).symm]
    exact hr.presence k
  · intro k j
    rw [coefficient_flags, he (p.flag k j) (p.slot_ne (Or.inr (by intro h; have := congrArg (fun a : Fin 6 => a.val) h; dsimp at this; omega)))]
    exact hr.flags k j
  · intro k j
    rw [coefficient_words, he (p.word k j) (p.slot_ne (Or.inr (by intro h; have := congrArg (fun a : Fin 6 => a.val) h; dsimp at this; omega)))]
    exact hr.words k j
  · intro k
    by_cases hk : k = i
    · subst k
      refine ⟨?_, hz, ?_⟩
      · simpa only [EquationRowControl.coefficient, Function.update_self] using hb'
      · simp only [EquationRowControl.coefficient, Function.update_self]
        have := EquationCoefficientLoad.output_length s.input
        omega
    · rw [show ((EquationRowControl.coefficient s i).terms k).coefficient = (s.terms k).coefficient by
        simp only [EquationRowControl.coefficient, Function.update_of_ne hk], he (p.coefficient k) (p.slot_ne (Or.inl hk))]
      exact hr.coefficients k
  · simpa only [he _ (p.slot_available i 5).symm] using hr.available_head
  · simpa only [he _ (p.slot_available i 5).symm, EquationRowControl.coefficient] using hr.available_read
  · simpa only [he _ (p.slot_loop i 5).symm] using hr.loop_head
  · simpa only [he _ (p.slot_scratch i 5).symm] using hr.scratch
  · simpa only [he _ (p.slot_fuel i 5).symm] using hr.fuel

theorem monomial_hoareTime (p : Ports w) (s : State) (i : Fin 3) (B : ℕ)
    (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (MonomialPrefixMachine.machine (p.prefixPorts i)).HoareTime
      (Logical p s B emitted R) (Logical p (monomial B s i) B emitted R) (MonomialPrefixMachine.timeBound B) := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next => ∀ k, (∀ a, k ≠ (p.prefixPorts i).index a) → next k = work k
  have hC : MonomialPrefixMachine.Stable (p.prefixPorts i) C := by
    intro a b he ha k hk
    exact (he k hk).trans (ha k hk)
  have hready : MonomialPrefixMachine.Ready (p.prefixPorts i) (prefixState s i) B C work := by
    refine ⟨hr.safe, ?_, ?_, hr.available_head, hr.available_read, hr.loop_head, hr.scratch, hr.fuel, fun _ _ => rfl⟩
    · intro j
      simpa only [Ports.prefix_flag, prefixState] using hr.flags i j
    · intro j
      simpa only [Ports.prefix_word, prefixState] using hr.words i j
  obtain ⟨d, time, ht, hd, hh, hc', htapes⟩ :=
    MonomialPrefixMachine.hoareTime (p.prefixPorts i) (prefixState s i) B hlen emitted C hC inp work out ⟨hc, hready⟩
  have he := htapes.extra
  refine ⟨d, time, ht, hd, hh, hc', ?_⟩
  refine ⟨htapes.safe, ?_, ?_, ?_, ?_, htapes.available_head, htapes.available_read,
    htapes.loop_head, htapes.scratch, htapes.fuel,
    hR work d.work (fun k hk => he k (fun a => hk (Ports.prefixIndex i a))) hr.extra⟩
  · intro k
    rw [monomial_presence, he _ (p.presence_prefix i k)]
    exact hr.presence k
  · intro k j
    by_cases hk : k = i
    · subst k
      simpa only [monomial, Function.update_self, Ports.prefix_flag] using htapes.flags j
    · rw [show ((monomial B s i).terms k).flags j = (s.terms k).flags j by
        simp only [monomial, Function.update_of_ne hk], he (p.flag k j) (p.other_slot_prefix i k _ hk)]
      exact hr.flags k j
  · intro k j
    by_cases hk : k = i
    · subst k
      simpa only [monomial, Function.update_self, Ports.prefix_word] using htapes.words j
    · rw [show ((monomial B s i).terms k).words j = (s.terms k).words j by
        simp only [monomial, Function.update_of_ne hk], he (p.word k j) (p.other_slot_prefix i k _ hk)]
      exact hr.words k j
  · intro k
    rw [monomial_coefficient, he _ (p.coefficient_prefix i k)]
    exact hr.coefficients k

def bodyMachine (p : Ports w) (i : Fin 3) : TM (w + 1) :=
  seqTM (EquationCoefficientLoad.machine (p.coefficient i)) (MonomialPrefixMachine.machine (p.prefixPorts i))

theorem body_hoareTime (p : Ports w) (s : State) (i : Fin 3) (B : ℕ) (hB : 2 ≤ B)
    (hlen : s.input.length ≤ B) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (bodyMachine p i).HoareTime (Logical p s B emitted R) (Logical p (body B s i) B emitted R)
      (13 * B + MonomialPrefixMachine.timeBound B + 41) := by
  have h := seqTM_hoareTime _ _ (coefficient_hoareTime p s i B hB hlen emitted R hR) (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩)
    (monomial_hoareTime p (EquationRowControl.coefficient s i) i B ((coefficient_length s i).trans hlen) emitted R hR)
  exact h.mono_bound (by omega)

end JointThermoComplexity.Complexity.EquationRowFields

#print axioms JointThermoComplexity.Complexity.EquationRowFields.read_hoareTime
#print axioms JointThermoComplexity.Complexity.EquationRowFields.coefficient_hoareTime
#print axioms JointThermoComplexity.Complexity.EquationRowFields.monomial_hoareTime
#print axioms JointThermoComplexity.Complexity.EquationRowFields.body_hoareTime
