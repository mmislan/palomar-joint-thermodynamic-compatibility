module
public import proofs.JointThermoComplexity.Complexity.NetworkBody
public import proofs.JointThermoComplexity.Complexity.NetworkInputControl

set_option autoImplicit false
@[expose] public section

/-!
# A uniform literal-network parser from fresh binary input

Three header registers control all record loops. A distinct retained flag
accumulates header/field validity and an actual final step rejects trailing data.
The output is the consumed input prefix, not the existential-real formula.
-/

namespace JointThermoComplexity.Complexity.NetworkParser
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def count (n : ℕ) (j : Fin 3) : Fin (n + 5) := DimensionMachine.slot (n + 1) j
def master (n : ℕ) : Fin (n + 5) := (Fin.last n).castAdd 4
def flag (n : ℕ) : Fin (n + 5) := NaturalMachine.flagIndex (n + 4)

theorem count_ne_flag (n : ℕ) (j : Fin 3) : count n j ≠ flag n := by
  exact DimensionMachine.slot_ne_flag (n + 1) j

theorem count_ne_master (n : ℕ) (j : Fin 3) : count n j ≠ master n :=
  (DimensionEntry.free_ne_slot (n + 1) (Fin.last n) j).symm

theorem master_ne_flag (n : ℕ) : master n ≠ flag n := DimensionEntry.free_ne_flag (n + 1) (Fin.last n)

theorem count_ne_count (n : ℕ) (j k : Fin 3) (h : j ≠ k) : count n j ≠ count n k :=
  fun he => h (DimensionMachine.slot_injective (n + 1) he)

def body (n : ℕ) : TM (n + 5) := NetworkBody.machine (count n 0) (count n 1) (count n 2) (master n)
def machine (n : ℕ) : TM (n + 5) := seqTM (DimensionEntry.machine (n + 1)) (body n)

def recordTime (input : List Bool) : ℕ := NetworkScanner.timeBound
  (DimensionHeaders.species input) (DimensionHeaders.reactions input) (DimensionHeaders.cores input)
  (DimensionHeaders.tail₃ input).length

def timeBound (L : ℕ) : ℕ := 2 * L + 25 +
  ((L * (2 * (L * L) + 16 * L + 17) + (L + 2) + 1 + (L * (8 * L + 15) + (L + 2))) + 1 +
    ((4 * L + 6) + 1 + (L * (4 * L + 24) + (L + 2))))

theorem recordTime_le (input : List Bool) : 2 * input.length + 25 + recordTime input ≤ timeBound input.length := by
  have hsum := DimensionHeaders.count_sum_bound input
  have hsplit := congrArg List.length (DimensionHeaders.prefix_and_suffix input)
  simp only [List.length_append] at hsplit
  have hs : DimensionHeaders.species input ≤ input.length := by omega
  have hr : DimensionHeaders.reactions input ≤ input.length := by omega
  have hc : DimensionHeaders.cores input ≤ input.length := by omega
  have ht : (DimensionHeaders.tail₃ input).length ≤ input.length := by omega
  have hbound := NetworkScanner.time_bound_in_total_length hs hr hc ht
  exact Nat.add_le_add_left hbound (2 * input.length + 25)

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine n).reachesIn t ((machine n).initCfg input) d ∧
      (machine n).halted d ∧
      Cursor (NetworkInputControl.copied input) (NetworkInputControl.rest input) (NetworkInputControl.copied input)
        d.input d.work d.output ∧ (d.work (master n)).head = 1 ∧
      (d.work (master n)).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
      NetworkScanner.Env (count n 0) (count n 1) (count n 2)
        (DimensionHeaders.species input) (DimensionHeaders.reactions input) (DimensionHeaders.cores input) d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hcur, hs, hr, hc, hf, hv, hfree⟩ := DimensionEntry.run (n + 1) input
  have hmhead : (c.work (master n)).head = 1 := by rw [master, hfree (Fin.last n)]; rfl
  have hbody := NetworkBody.hoareTime (count n 0) (count n 1) (count n 2) (master n)
    (count_ne_flag n 0) (count_ne_flag n 1) (count_ne_flag n 2) (master_ne_flag n)
    (count_ne_master n 0) (count_ne_master n 1) (count_ne_master n 2)
    (count_ne_count n 0 1 (by decide)) (count_ne_count n 0 2 (by decide)) (count_ne_count n 1 2 (by decide))
    (DimensionHeaders.species input) (DimensionHeaders.reactions input) (DimensionHeaders.cores input)
    (DimensionHeaders.accepted input) (DimensionEntry.consumed input) (DimensionHeaders.tail₃ input) (DimensionEntry.consumed input)
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, _, hdmh, hdmv, henv⟩ :=
    hbody c.input c.work c.output ⟨hcur, hmhead, hf, hv, hs, hr, hc⟩
  obtain ⟨hi, hw, ho⟩ := hcur.phase
  have hreach₂ : (body n).reachesIn td
      ⟨(body n).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho, body] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (DimensionEntry.machine (n + 1)) (body n) hcreach hchalt hreach₂
  have hstart : phase1Wrap (DimensionEntry.machine (n + 1)) (body n)
      ((DimensionEntry.machine (n + 1)).initCfg input) = (machine n).initCfg input := rfl
  rw [hstart] at hreach
  have htime : tc + 1 + td ≤ timeBound input.length := by
    have hraw : tc + 1 + td ≤ 2 * input.length + 25 + recordTime input := by
      change td ≤ recordTime input + 6 at htd
      omega
    exact hraw.trans (recordTime_le input)
  refine ⟨phase2Wrap (DimensionEntry.machine (n + 1)) (body n) d, tc + 1 + td, htime, hreach,
    (phase2Wrap_halted_iff _ _ d).mpr hdhalt, ?_, hdmh, ?_, henv⟩
  · simpa only [phase2Wrap, NetworkInputControl.copied, NetworkInputControl.rest, NetworkInputControl.records] using hdcur
  · simpa only [phase2Wrap, NetworkInputControl.accepted, NetworkInputControl.records,
      NetworkRecords.accepted, Bool.and_assoc] using hdmv

theorem input_cells_preserved {n : ℕ} {input : List Bool} {inp out : Tape} {work : Fin (n + 5) → Tape}
    (h : Cursor (NetworkInputControl.copied input) (NetworkInputControl.rest input)
      (NetworkInputControl.copied input) inp work out) : inp.cells = (Tape.init (input.map Γ.ofBool)).cells := by
  simpa only [NetworkInputControl.consumed_split] using h.cells

theorem codec_status_iff (input : List Bool) {value : Γ}
    (h : value = Γ.ofBool (NetworkInputControl.accepted input)) :
    value = Γ.one ↔ ∃ Q, NetworkCodec.decode input = some Q := by
  rw [h, ← NetworkInputControl.status_iff_decode]
  cases NetworkInputControl.accepted input <;> simp [Γ.ofBool]

theorem computesInTime (n : ℕ) :
    (machine n).ComputesInTime NetworkInputControl.copied timeBound := by
  intro input
  obtain ⟨d, t, ht, hreach, hhalt, hcur, _⟩ := run n input
  exact ⟨d, t, ht, hreach, hhalt, hcur.tapePrefix.2.1, hcur.tapePrefix.2.2 _ le_rfl⟩

end JointThermoComplexity.Complexity.NetworkParser

#print axioms JointThermoComplexity.Complexity.NetworkParser.run
#print axioms JointThermoComplexity.Complexity.NetworkParser.codec_status_iff
#print axioms JointThermoComplexity.Complexity.NetworkParser.computesInTime
