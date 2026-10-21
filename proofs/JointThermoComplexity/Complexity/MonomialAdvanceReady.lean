module
public import proofs.JointThermoComplexity.Complexity.MonomialReady

set_option autoImplicit false
@[expose] public section

/-! Hide temporary power addresses behind the bounded invariant while retaining exact circuit and result references. -/

namespace JointThermoComplexity.Complexity.MonomialAdvanceReady
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady CircuitSerialization PowerAddressCircuit

theorem hoareTime {n : ℕ} (m L offset arity idx : ℕ) (ha : arity ≤ 4 * L)
    (s : MonomialCircuit.State n) (item : Fin n × ℕ) (inputs : Fin n → Fin arity)
    (h : offset + (s.advance item).size ≤ arity) (hlen : item.2.bits.length ≤ L) (hidx : (inputs item.1).val = idx)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → work' j = work j) → R work → R work') :
    (MonomialAdvance.machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode item.2 ++ tail)
        (initial ++ equationStream s.circuit inputs (index offset _ arity (by have hs := s.advance_size_ge item; omega))) inp work out ∧
        Ready m L offset s idx R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode item.2) tail
        (initial ++ equationStream (s.advance item).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (s.advance item) idx R work) (MonomialAdvance.timeBound L) := by
  rintro inp work out ⟨hc, hs, hi, hz, hn, ho, ht, hr⟩
  obtain ⟨a, p, ha', hp', har, hpr⟩ := ht
  obtain ⟨d, t, htime, hreach, hhalt, hd, ⟨hds, hdz, hdn, hda, hdp, hdr⟩, hdo, hdi⟩ :=
    MonomialAdvance.hoareTime m offset arity L a p ha s item inputs h hlen ha' hp' before tail initial R hR
      inp work out ⟨hc, ⟨hs, hz, hn, har, hpr, hr⟩, ho, by simpa only [hidx] using hi⟩
  have hpSize : offset + (MonomialAdvanceCode.power s item).size < arity := by
    rw [MonomialAdvanceCode.advance_size] at h
    omega
  have hab : offset + (MonomialAdvanceCode.power s item).accumulator.val ≤ 4 * L := by
    have hi := (MonomialAdvanceCode.power s item).accumulator.isLt
    omega
  have hpb : offset + (MonomialAdvanceCode.power s item).power.val ≤ 4 * L := by
    have hi := (MonomialAdvanceCode.power s item).power.isLt
    omega
  exact ⟨d, t, htime, hreach, hhalt, hd, hds, by simpa only [hidx] using hdi,
    hdz, hdn, hdo, ⟨offset + (MonomialAdvanceCode.power s item).accumulator.val,
      offset + (MonomialAdvanceCode.power s item).power.val, hab, hpb, hda, hdp⟩, hdr⟩

end JointThermoComplexity.Complexity.MonomialAdvanceReady

#print axioms JointThermoComplexity.Complexity.MonomialAdvanceReady.hoareTime
