module
public import proofs.JointThermoComplexity.CycleMinimality
public import proofs.JointThermoComplexity.LiteralPath

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity
noncomputable section

def cycleValues {n : ℕ} (A : ℝ) (x : ℕ → ℝ) (i : Fin (n+2)) : ℝ :=
  if i.val=0 then A else x (i.val-1)

def cycleTrace {n : ℕ} (p : Fin (n+2) → ℝ) (k : ℕ) : ℝ :=
  if h : k<n+1 then p ⟨k+1,by omega⟩ else (p 0)^2

def cycleFlux {n : ℕ} (w : Fin (n+1) → ℝ) (p : Fin (n+2) → ℝ) (i : Fin (n+2)) : ℝ :=
  if h : i.val=0 then p 0-p 1 else
    (p i-(p (finRotate (n+2) i))^(cycleGain n i))/w ⟨i.val-1,by omega⟩

theorem cycleFlux_zero {n : ℕ} (w : Fin (n+1) → ℝ) (p : Fin (n+2) → ℝ) :
    cycleFlux w p 0=p 0-p 1 := by simp [cycleFlux]

theorem cycleTrace_zero {n : ℕ} (p : Fin (n+2) → ℝ) : cycleTrace p 0=p 1 := by
  simp [cycleTrace]

theorem cycleTrace_end {n : ℕ} (p : Fin (n+2) → ℝ) : cycleTrace p (n+1)=(p 0)^2 := by
  simp [cycleTrace]

theorem cycleFlux_succ {n : ℕ} (w : Fin (n+1) → ℝ) (p : Fin (n+2) → ℝ) (i : Fin (n+1)) :
    cycleFlux w p i.succ=pathCurrent w (cycleTrace p) i := by
  have hi : i.val<n+1 := i.isLt
  simp only [cycleFlux, Fin.val_succ, Nat.add_sub_cancel]
  simp only [Nat.succ_ne_zero, ↓reduceDIte]
  dsimp [pathCurrent]
  congr 1
  have hstart : cycleTrace p i.val=p i.succ := by
    simp only [cycleTrace,hi, ↓reduceDIte]
    rfl
  rw [hstart]
  congr 1
  by_cases hl : i=Fin.last n
  · subst i
    have he : (Fin.last n).succ=Fin.last (n+1) := rfl
    rw [he,finRotate_last]
    norm_num [cycleGain,cycleTrace]
  · have hil : i.val<n := by
      have hh : i.val ≠ n := fun h=>hl (Fin.ext h)
      omega
    have hr : finRotate (n+2) i.succ = ⟨i.val+2,by omega⟩ := finRotate_of_lt (by simpa using Nat.succ_lt_succ hil)
    have hlast : i.succ ≠ Fin.last (n+1) := by intro h; apply hl; apply Fin.ext; have hh:=congrArg Fin.val h; simpa using hh
    rw [hr]
    simp only [cycleGain,ite_eq_right hlast,pow_one]
    simp [cycleTrace,show i.val+1<n+1 by omega]

theorem cycleValues_zero {n : ℕ} (A : ℝ) (x : ℕ→ℝ) : @cycleValues n A x 0=A := by simp [cycleValues]
theorem cycleValues_succ {n : ℕ} (A : ℝ) (x : ℕ→ℝ) (i : Fin (n+1)) :
    cycleValues A x i.succ=x i.val := by simp [cycleValues]

theorem cycleTrace_values {n : ℕ} (A : ℝ) (x : ℕ→ℝ) (hx : x (n+1)=A^2) (k : ℕ) (hk : k≤n+1) :
    cycleTrace (@cycleValues n A x) k=x k := by
  by_cases h : k<n+1
  · simp [cycleTrace,h,cycleValues]
  · have he : k=n+1 := by omega
    subst k
    simp [cycleTrace,cycleValues,hx]

theorem chain_bounds {n : ℕ} (f : Fin (n+2)→ℝ) (hanti : StrictAnti f)
    (hgain : f 0<2*f (Fin.last (n+1))) :
    0<f 0 ∧ ∀ i : Fin (n+1), f 0/2<f i.succ ∧ f i.succ<f 0 := by
  have hl : f (Fin.last (n+1))<f 0 := hanti (by change 0<n+1; omega)
  constructor
  · linarith
  · intro i
    have hle : f (Fin.last (n+1))≤f i.succ := hanti.antitone (Fin.le_last _)
    exact ⟨by linarith,hanti (by simp)⟩

theorem productive_cycle_to_path {n : ℕ} (w : Fin (n+1)→ℝ) (p : Fin (n+2)→ℝ)
    (hp : ∀ i,0<p i) (hanti : StrictAnti (cycleFlux w p))
    (hg : cycleFlux w p 0<2*cycleFlux w p (Fin.last (n+1))) :
    LiteralPath w (p 0) (p 1) (cycleTrace p) := by
  obtain ⟨hj,hb⟩:=chain_bounds _ hanti hg
  refine ⟨cycleTrace_zero p,cycleTrace_end p,?_,?_,?_,?_⟩
  · intro k hk
    unfold cycleTrace
    split_ifs
    · exact hp _
    · exact sq_pos_of_pos (hp 0)
  · simpa only [cycleFlux_zero] using hj
  · intro i
    simpa only [cycleFlux_zero,cycleFlux_succ] using hb i
  · intro i j hij
    rw [← cycleFlux_succ,← cycleFlux_succ]
    exact hanti (by simpa using hij)

theorem path_to_productive_cycle {n : ℕ} (w : Fin (n+1)→ℝ) (A B : ℝ) (x : ℕ→ℝ)
    (hA : 0<A) (hx : LiteralPath w A B x) :
    (∀ i : Fin (n+2),0<cycleValues A x i) ∧ StrictAnti (cycleFlux w (cycleValues A x)) ∧
    cycleFlux w (cycleValues A x) 0 < 2*cycleFlux w (cycleValues A x) (Fin.last (n+1)) := by
  obtain ⟨hx0,hxe,hpos,hj,hb,ha⟩:=hx
  have hcurr (i : Fin (n+1)) : cycleFlux w (cycleValues A x) i.succ=pathCurrent w x i := by
    rw [cycleFlux_succ]
    dsimp [pathCurrent]
    rw [cycleTrace_values A x hxe i.val (by omega),cycleTrace_values A x hxe (i.val+1) (by omega)]
  have hzero : cycleFlux w (cycleValues A x) 0=A-B := by
    rw [cycleFlux_zero,cycleValues_zero]
    have hv : cycleValues A x (1 : Fin (n+2))=x 0 := by simp [cycleValues]
    rw [hv,hx0]
  refine ⟨?_,?_,?_⟩
  · intro i
    unfold cycleValues
    split_ifs
    · exact hA
    · exact hpos _ (by omega)
  · intro i j hij
    by_cases hi : i=0
    · subst i
      obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt hij)
      rw [hzero,hcurr]
      exact (hb k).2
    · obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr hi
      have hj0 : j ≠ 0 := by intro h; subst j; simp at hij
      obtain ⟨l,rfl⟩ := Fin.exists_succ_eq.mpr hj0
      rw [hcurr,hcurr]
      exact ha (by simpa using hij)
  · have he : Fin.last (n+1)=(Fin.last n).succ := rfl
    rw [hzero,he,hcurr]
    linarith [(hb (Fin.last n)).1]

end
end JointThermoComplexity

#print axioms JointThermoComplexity.productive_cycle_to_path

#print axioms JointThermoComplexity.path_to_productive_cycle
