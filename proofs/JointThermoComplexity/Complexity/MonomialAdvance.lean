module
public import proofs.JointThermoComplexity.Complexity.MonomialPower
public import proofs.JointThermoComplexity.Complexity.MonomialProduct
public import proofs.JointThermoComplexity.Complexity.MonomialAdvanceCode

set_option autoImplicit false
@[expose] public section

/-! One actual monomial step consumes its exponent and appends the full semantic circuit extension. -/

namespace JointThermoComplexity.Complexity.MonomialAdvance
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CircuitSerialization PowerAddressCircuit MonomialInputCircuit

def machine (m : ℕ) : TM (m + 14) := seqTM (MonomialPower.machine m) (MonomialProduct.machine m)

def timeBound (L : ℕ) : ℕ := 192 * L ^ 3 + 552 * L ^ 2 + 578 * L + 215

theorem hoareTime {n : ℕ} (m offset arity L oldAcc oldPower : ℕ) (ha : arity ≤ 4 * L)
    (s : MonomialCircuit.State n) (item : Fin n × ℕ) (inputs : Fin n → Fin arity)
    (h : offset + (s.advance item).size ≤ arity) (hlen : item.2.bits.length ≤ L)
    (hacc : oldAcc ≤ 4 * L) (hpower : oldPower ≤ 4 * L)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode item.2 ++ tail)
        (initial ++ equationStream s.circuit inputs
          (index offset _ arity (by have hs := s.advance_size_ge item; omega))) inp work out ∧
        PowerAddressFrame.Ready (m + 1) (temporary offset oldAcc oldPower s.circuit) R work ∧
        IsReg (offset + s.accumulator.val) (work (previous m)) ∧ IsReg (inputs item.1).val (work (species m)))
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode item.2) tail
        (initial ++ equationStream (s.advance item).circuit inputs (index offset _ arity h)) inp work out ∧
        PowerAddressFrame.Ready (m + 1) (MonomialAdvanceCode.afterState offset s item) R work ∧
        IsReg (offset + (s.advance item).accumulator.val) (work (previous m)) ∧
        IsReg (inputs item.1).val (work (species m))) (timeBound L) := by
  have hpRoom : offset + (MonomialAdvanceCode.power s item).size < arity := by
    rw [MonomialAdvanceCode.advance_size] at h
    omega
  have hold : offset + s.accumulator.val < arity := by
    have hi := s.accumulator.isLt
    have hs := s.advance_size_ge item
    omega
  have hac : offset + (MonomialAdvanceCode.power s item).accumulator.val < arity := by
    have hi := (MonomialAdvanceCode.power s item).accumulator.isLt
    omega
  let P : (Fin (m + 14) → Tape) → Prop := fun work => IsReg (offset + s.accumulator.val) (work (previous m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hp, hr⟩
    have he := hw (previous m) (previous_ne_next m) (previous_ne_accumulator m) (previous_ne_power m) (previous_ne_flag m)
    exact ⟨by simpa only [he] using hp, hR work work' (fun j hn ha hp hf _ => hw j hn ha hp hf) hr⟩
  have hpow := MonomialPower.hoareTime m offset arity L oldAcc oldPower ha s.circuit item.1 item.2 inputs
    hpRoom.le hlen hacc hpower before tail initial P hP
  let S : (Fin (m + 14) → Tape) → Prop := fun work => IsReg (inputs item.1).val (work (species m)) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ previous m → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hi, hr⟩
    have he := hw (species m) (species_ne_next m) (previous_ne_species m).symm
    exact ⟨by simpa only [he] using hi, hR work work' (fun j hn _ _ _ hp => hw j hn hp) hr⟩
  have hprod := MonomialProduct.hoareTime m arity L ha (ofState offset (MonomialAdvanceCode.power s item))
    hpRoom hac (⟨offset + s.accumulator.val, hold⟩ : Fin arity) (before ++ BitCodec.naturalCode item.2) tail
    (initial ++ equationStream (MonomialAdvanceCode.power s item).circuit inputs (index offset _ arity hpRoom.le)) S hS
  have hseq := seqTM_hoareTime (MonomialPower.machine m) (MonomialProduct.machine m) hpow (by
    rintro inp work out ⟨hc, ⟨hs, hz, hn, ha, hp, ho, hr⟩, hi⟩
    obtain ⟨hip, hw, hout⟩ := hc.phase
    rw [hip, hw, hout]
    exact ⟨hc, ⟨hs, hz, hn, ha, hp, hi, hr⟩, ho⟩) hprod
  exact hseq.consequence (by
    rintro inp work out ⟨hc, ⟨hs, hz, hn, ha, hp, hr⟩, ho, hi⟩
    exact ⟨hc, ⟨hs, hz, hn, ha, hp, ho, hr⟩, hi⟩) (by
    rintro inp work out ⟨hc, ⟨hs, hz, hn, ha, hp, hi, hr⟩, ho⟩
    refine ⟨?_, ?_, ?_, hi⟩
    · rw [MonomialAdvanceCode.advance_stream offset arity s item inputs h]
      simpa only [ofState, List.append_assoc] using hc
    · rw [← MonomialAdvanceCode.after_eq]
      exact ⟨hs, hz, hn, ha, hp, hr⟩
    · simpa only [ofState, MonomialAdvanceCode.advance_accumulator] using ho)
    (by unfold timeBound MonomialPower.timeBound; omega)

end JointThermoComplexity.Complexity.MonomialAdvance

#print axioms JointThermoComplexity.Complexity.MonomialAdvance.hoareTime
