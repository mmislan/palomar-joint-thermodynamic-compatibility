module

public import proofs.Complexitylib.Models.TuringMachine.Registers.ForReg

@[expose] public section

/-! # Exact unary-code emission by a fixed-register Turing machine -/

namespace DInstabilityComplexity.MachineConstruction

open Complexity Complexity.TM

variable {n : ℕ}

def emitUnaryCodeTM (r : Fin n) : TM n :=
  seqTM (forRegTM (emitBitsTM [true]) r) (emitBitsTM [false])

theorem emitUnaryCodeTM_hoareTime (r : Fin n) (v : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀) (hwork : ∀ j, Parked (work₀ j)) (hr : work₀ r = regTape v) :
    (emitUnaryCodeTM r).HoareTime (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀ (ys ++ (List.replicate v true ++ [false]))) (4 * v + 4) := by
  let Y := fun i => ys ++ List.replicate i true
  have hbody (i : ℕ) (_hi : i < v) : (emitBitsTM (n := n) [true]).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update work₀ r ⟨i + 2, regCells v⟩ ∧ OutAcc (Y i) out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update work₀ r ⟨i + 2, regCells v⟩ ∧ OutAcc (Y (i + 1)) out) 1 := by
    let wi := Function.update work₀ r (⟨i + 2, regCells v⟩ : Tape)
    have hwi (j : Fin n) : Parked (wi j) := by
      by_cases hj : j = r
      · subst j
        simpa only [wi, Function.update_self] using
          (parked_regCells (v := v) (h := i + 2) (by omega))
      · simpa only [wi, Function.update_of_ne hj] using hwork j
    have hword : Y i ++ [true] = Y (i + 1) := by
      dsimp only [Y]
      rw [List.replicate_add, List.append_assoc]
      rfl
    have he := emitBitsTM_hoareTime [true] inp₀ wi (Y i) hinp hwi
    simpa only [EmitPred, hword, List.length_cons, List.length_nil] using he
  have hl := forRegTM_hoareTime (emitBitsTM [true]) r v inp₀
    (fun _ => work₀) Y 1 hinp (fun _ => hr) (fun _ j _ => hwork j) hbody
  have hl' : (forRegTM (emitBitsTM [true]) r).HoareTime
      (EmitPred inp₀ work₀ ys) (EmitPred inp₀ work₀ (ys ++ List.replicate v true))
      (v * (1 + 2) + (v + 2)) := by
    simpa only [Y, List.replicate_zero, List.append_nil] using hl
  have he := emitBitsTM_hoareTime [false] inp₀ work₀ (ys ++ List.replicate v true) hinp hwork
  have hall := seqTM_hoareTime (forRegTM (emitBitsTM [true]) r) (emitBitsTM [false]) hl'
    (emitPred_transition hinp hwork (ys ++ List.replicate v true)) he
  have hbound : v * (1 + 2) + (v + 2) + 1 + [false].length ≤ 4 * v + 4 := by
    simp only [List.length_cons, List.length_nil]
    omega
  refine (hall.mono_bound hbound).strengthen_post ?_
  rintro inp work out ⟨hi, hw, hout⟩
  refine ⟨hi, hw, ?_⟩
  simpa only [List.append_assoc] using hout

#print axioms emitUnaryCodeTM_hoareTime

end DInstabilityComplexity.MachineConstruction
