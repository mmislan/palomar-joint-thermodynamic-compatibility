module
public import proofs.JointThermoComplexity.Complexity.ReactionArray
public import proofs.JointThermoComplexity.Complexity.MotifArray
public import proofs.JointThermoComplexity.Complexity.BoxArray

set_option autoImplicit false
@[expose] public section

/-!
# Complete fixed-dimension literal-network scanner

The TM's finite control depends only on five tape addresses. Its three declared
dimensions are supplied as parked unary header registers, while all numeric
fields retain their binary encodings. This scanner validates and copies record
data; constructing the real formula is a separate machine obligation.
-/

namespace JointThermoComplexity.Complexity.NetworkScanner
open _root_.Complexity
open _root_.Complexity.TM
open ScannerSpec

variable {n : ℕ}

def machine (species reactions cores master : Fin (n + 1)) : TM (n + 1) :=
  seqTM (seqTM (ReactionArray.machine species reactions master) (MotifArray.machine species reactions cores master))
    (seqTM (MaskScanner.machine reactions master) (BoxArray.machine species master))

def Env (species reactions cores : Fin (n + 1)) (ns nr nc : ℕ) (work : Fin (n + 1) → Tape) : Prop :=
  IsReg ns (work species) ∧ IsReg nr (work reactions) ∧ IsReg nc (work cores)

def timeBound (ns nr nc L : ℕ) : ℕ :=
  (ReactionArray.timeBound ns nr L + 1 + MotifArray.timeBound ns nr nc) + 1 +
    ((4 * nr + 6) + 1 + BoxArray.timeBound ns L)

theorem runs (species reactions cores master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hr : reactions ≠ NaturalMachine.flagIndex n)
    (hc : cores ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n)
    (hsm : species ≠ master) (hrm : reactions ≠ master) (hcm : cores ≠ master)
    (hsr : species ≠ reactions) (hsc : species ≠ cores) (hrc : reactions ≠ cores) (ns nr nc : ℕ) :
    Runs (RecordControl.network ns nr nc) (machine species reactions cores master) master (NaturalMachine.flagIndex n)
      (Env species reactions cores ns nr nc) (timeBound ns nr nc) := by
  have hEnv : ∀ (work work' : Fin (n + 1) → Tape),
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) →
      Env species reactions cores ns nr nc work → Env species reactions cores ns nr nc work' := by
    rintro work work' h ⟨hss, hrr, hcc⟩
    exact ⟨by simpa only [h species hsm hs] using hss, by simpa only [h reactions hrm hr] using hrr,
      by simpa only [h cores hcm hc] using hcc⟩
  have hreactions := ScannerEnv.strengthen (ReactionArray.runs species reactions master hs hm hsm hr hrm hsr ns nr)
    (fun _ h => ⟨h.1, h.2.1⟩ : ∀ work, Env species reactions cores ns nr nc work →
      IsReg ns (work species) ∧ IsReg nr (work reactions)) hEnv
  have hmotifs := ScannerEnv.strengthen (MotifArray.runs species reactions cores master hs hm hsm hr hrm hc hcm hsc hrc ns nr nc)
    (fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩ : ∀ work, Env species reactions cores ns nr nc work →
      (IsReg ns (work species) ∧ IsReg nr (work reactions)) ∧ IsReg nc (work cores)) hEnv
  have hdirections := ScannerEnv.strengthen (MaskScanner.runs_booleans reactions master hr hm hrm nr)
    (fun _ h => h.2.1 : ∀ work, Env species reactions cores ns nr nc work → IsReg nr (work reactions)) hEnv
  have hboxes := ScannerEnv.strengthen (BoxArray.runs species master hs hsm hm ns)
    (fun _ h => ⟨True.intro, h.1⟩ : ∀ work, Env species reactions cores ns nr nc work → True ∧ IsReg ns (work species)) hEnv
  have hboxmono : Monotone (BoxArray.timeBound ns) := by
    intro a b h
    exact Nat.add_le_add_right (Nat.mul_le_mul_left ns (Nat.add_le_add_right (BoxArray.optionalTime_mono h) 2)) (ns + 2)
  have hleft := product_runs hreactions hmotifs (by intro a b h; rfl)
  have hright := product_runs hdirections hboxes hboxmono
  have hrightmono : Monotone (fun L => (4 * nr + 6) + 1 + BoxArray.timeBound ns L) := by
    intro a b h
    exact Nat.add_le_add_left (hboxmono h) ((4 * nr + 6) + 1)
  exact transport_runs (DataCodec.networkEquiv ns nr nc) (product_runs hleft hright hrightmono)

theorem codec_status_iff (ns nr nc : ℕ) (input : List Bool) (initial : Bool) {value : Γ}
    (h : value = Γ.ofBool (initial && (RecordControl.network ns nr nc).valid input)) :
    value = Γ.one ↔ initial = true ∧ ∃ Q tail, (DataCodec.network ns nr nc).parse input = some (Q, tail) := by
  have hv : Γ.ofBool (initial && (RecordControl.network ns nr nc).valid input) = Γ.one ↔
      initial = true ∧ (RecordControl.network ns nr nc).valid input = true := by
    cases initial <;> cases (RecordControl.network ns nr nc).valid input <;> simp [Γ.ofBool]
  rw [h, hv, RecordControl.network_status_iff]

theorem time_bound_in_total_length {ns nr nc L : ℕ} {input : List Bool}
    (hs : ns ≤ L) (hr : nr ≤ L) (hc : nc ≤ L) (hi : input.length ≤ L) :
    timeBound ns nr nc input.length ≤
      (L * (2 * (L * L) + 16 * L + 17) + (L + 2) + 1 + (L * (8 * L + 15) + (L + 2))) + 1 +
        ((4 * L + 6) + 1 + (L * (4 * L + 24) + (L + 2))) := by
  have hreaction := ReactionArray.time_bound_in_total_length hs hr hi
  have hmotif := MotifArray.time_bound_in_total_length hs hr hc
  have hbox := BoxArray.time_bound_in_total_length hs hi
  dsimp [timeBound]
  omega

end JointThermoComplexity.Complexity.NetworkScanner

#print axioms JointThermoComplexity.Complexity.NetworkScanner.runs
#print axioms JointThermoComplexity.Complexity.NetworkScanner.codec_status_iff
