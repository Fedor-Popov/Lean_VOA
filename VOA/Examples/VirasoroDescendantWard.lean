/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaEigenspaces

/-!
# Finite coefficient Ward operators for descendant fields

A coefficient sequence lives in actual Verma levels. Its positive Ward
operators measure failure of primary covariance. The first two descendant
operators are constructed from finite sums of actual negative modes.
The commutation identities retain the Ward defects rather than assuming
that a primary sequence already exists. No fusion rule is assumed.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- Each coefficient is an actual state of its indicated relative level. -/
def WardLevel (c h : ℂ) (f : ℕ → Verma c h) : Prop :=
  ∀ r, f r∈sortedSpan c h r

/-- The finite sum of negative modes contributing to the second descendant.
At each coefficient only finitely many earlier states are used. -/
noncomputable def wardSource (c h : ℂ) (f : ℕ → Verma c h) (r : ℕ) : Verma c h :=
  ∑ j : Fin r, vermaMode c h ((j:ℤ)-(r:ℤ)) (f j)

/-- The first positive Ward defect: zero means the L₁ primary covariance
identity holds at this coefficient. Parameter a is the field weight and b
is the incoming highest weight; h is the outgoing highest weight. -/
noncomputable def wardPositive1 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) : Verma c h :=
  vermaMode c h 1 (f (r+1))-(h-b+a+(r:ℂ)) • f r

/-- The raw L₂ covariance defect, before subtracting the L₁ descendant. -/
noncomputable def wardCovariance2 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) : Verma c h :=
  vermaMode c h 2 (f (r+2))-(h-b+2*a+(r:ℂ)) • f r

/-- The actual second positive descendant operator. The factor three is the
binomial coefficient multiplying the first descendant in L₂ covariance. -/
noncomputable def wardPositive2 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) : Verma c h :=
  wardCovariance2 c h b a f r-(3:ℂ) • wardPositive1 c h b a f r

/-- Differentiating the field multiplies coefficient r by its exponent
h-b-a+r. This sign is derived from the exponent, not imported from a formula. -/
noncomputable def wardDescendant1 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) : Verma c h :=
  (h-b-a+(r:ℂ)) • f r

/-- The second negative descendant is a finite negative-mode sum plus its
incoming-weight correction. Its diagonal term is 2b+a-h-r. -/
noncomputable def wardDescendant2 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) : Verma c h :=
  wardSource c h f r+(2*b+a-h-(r:ℂ)) • f r

/-- The source construction preserves sums of coefficient sequences. -/
theorem wardSource_add (c h : ℂ) (f g : ℕ → Verma c h) (r : ℕ) :
    wardSource c h (f+g) r=wardSource c h f r+wardSource c h g r := by
  simp [wardSource,Finset.sum_add_distrib]

/-- Constant scalar multiplication commutes with the source construction. -/
theorem wardSource_smul (c h z : ℂ) (f : ℕ → Verma c h) (r : ℕ) :
    wardSource c h (z • f) r=z • wardSource c h f r := by
  simp [wardSource,Finset.smul_sum]

/-- Source terms all return to the same actual level. -/
theorem wardSource_level (c h : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) :
    WardLevel c h (wardSource c h f) := by
  intro r
  apply Submodule.sum_mem
  intro j hj
  exact verma_mode_mem_level c h j r (f j) (hf j) ((j:ℤ)-(r:ℤ)) (by omega)

/-- The first Ward defect remains in the indicated actual level. -/
theorem wardPositive1_level (c h b a : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) :
    WardLevel c h (wardPositive1 c h b a f) := by
  intro r
  exact Submodule.sub_mem _
    (verma_mode_mem_level c h (r+1) r _ (hf _) 1 (by omega)) (Submodule.smul_mem _ _ (hf r))

/-- The raw second covariance defect also preserves actual levels. -/
theorem wardCovariance2_level (c h b a : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) :
    WardLevel c h (wardCovariance2 c h b a f) := by
  intro r
  exact Submodule.sub_mem _
    (verma_mode_mem_level c h (r+2) r _ (hf _) 2 (by omega)) (Submodule.smul_mem _ _ (hf r))

/-- The second positive descendant stays in the same level sequence. -/
theorem wardPositive2_level (c h b a : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) :
    WardLevel c h (wardPositive2 c h b a f) := by
  intro r
  exact Submodule.sub_mem _ (wardCovariance2_level c h b a f hf r)
    (Submodule.smul_mem _ _ (wardPositive1_level c h b a f hf r))

/-- The first negative descendant only rescales each level. -/
theorem wardDescendant1_level (c h b a : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) :
    WardLevel c h (wardDescendant1 c h b a f) := fun r => Submodule.smul_mem _ _ (hf r)

/-- The second negative descendant preserves each level through its source
term and its scalar correction. -/
theorem wardDescendant2_level (c h b a : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) :
    WardLevel c h (wardDescendant2 c h b a f) := fun r =>
  Submodule.add_mem _ (wardSource_level c h f hf r) (Submodule.smul_mem _ _ (hf r))

/-- The first positive and first negative descendants have commutator 2a,
including the shift of field weight in each composition. -/
theorem wardPositive1_descendant1 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) :
    wardPositive1 c h b (a+1) (wardDescendant1 c h b a f) r-
      wardDescendant1 c h b (a-1) (wardPositive1 c h b a f) r= (2*a) • f r := by
  simp only [wardPositive1,wardDescendant1,map_smul,Nat.cast_add,Nat.cast_one]
  module

/-- The second positive descendant and first negative descendant have
commutator three times the first positive descendant. -/
theorem wardPositive2_descendant1 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) :
    wardPositive2 c h b (a+1) (wardDescendant1 c h b a f) r-
      wardDescendant1 c h b (a-2) (wardPositive2 c h b a f) r=
      (3:ℂ) • wardPositive1 c h b a f r := by
  simp only [wardPositive2,wardCovariance2,wardPositive1,wardDescendant1,map_smul,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  module



/-- L₁ commutation through the finite source retains the whole defect
sequence, plus the telescoping scalar and the actual L₀ boundary term. -/
theorem wardSource_L1 (c h b a : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) (r : ℕ) :
    vermaMode c h 1 (wardSource c h f (r+1))=
      wardSource c h (wardPositive1 c h b a f) r+
      ((r:ℂ)+2+(h-b+a)) • wardSource c h f r+(2*(h+(r:ℂ))) • f r := by
  classical
  have hcomm (j : Fin (r+1)) :
      vermaMode c h 1 (vermaMode c h ((j:ℤ)-((r:ℤ)+1)) (f j))=
        vermaMode c h ((j:ℤ)-((r:ℤ)+1)) (vermaMode c h 1 (f j))+
          ((r:ℂ)+2-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j) := by
    have hh := vermaMode_comm_apply c h 1 ((j:ℤ)-((r:ℤ)+1)) (f j)
    norm_num at hh
    convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+1), vermaMode c h ((j:ℤ)-((r:ℤ)+1)) (vermaMode c h 1 (f j)))=
      wardSource c h (wardPositive1 c h b a f) r+
      ∑ j : Fin r, ((j:ℂ)+(h-b+a)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,verma_mode_above_level c h 0 (f 0) (hf 0) 1 (by norm_num),
      map_zero,zero_add]
    rw [wardSource,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hr : vermaMode c h 1 (f (j+1))=wardPositive1 c h b a f j+
        ((j:ℂ)+(h-b+a)) • f j := by
      unfold wardPositive1
      module
    simp only [Fin.val_succ]
    rw [hr,map_add,map_smul]
    have he : ((j:ℕ)+1:ℤ)-((r:ℤ)+1)=(j:ℤ)-(r:ℤ) := by push_cast; ring
    push_cast
    simp only [show (j:ℤ)+1-((r:ℤ)+1)=(j:ℤ)-(r:ℤ) by omega]
  have hB : (∑ j : Fin (r+1), ((r:ℂ)+2-(j:ℂ)) •
      vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))=
      (∑ j : Fin r, ((r:ℂ)+2-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))+
        (2*(h+(r:ℂ))) • f r := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,sub_self,
      (verma_mem_level_iff_eigen c h r (f r)).mp (hf r),smul_smul]
    congr 1
    congr 1
    ring
  have hS : (∑ j : Fin r, ((j:ℂ)+(h-b+a)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))+
      (∑ j : Fin r, ((r:ℂ)+2-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))=
      ((r:ℂ)+2+(h-b+a)) • wardSource c h f r := by
    rw [← Finset.sum_add_distrib,wardSource,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    module
  simp only [wardSource,Nat.cast_add,Nat.cast_one,map_sum,hcomm,Finset.sum_add_distrib]
  rw [hA,hB]
  have hh := hS
  simp only [wardSource] at hh
  rw [← hh]
  simp only [wardSource]
  abel

/-- The L₁ commutator with the second negative descendant is exactly three
times the first negative descendant. Defects are carried through explicitly. -/
theorem wardPositive1_descendant2 (c h b a : ℂ) (f : ℕ → Verma c h)
    (hf : WardLevel c h f) (r : ℕ) :
    wardPositive1 c h b (a+2) (wardDescendant2 c h b a f) r-
      wardDescendant2 c h b (a-1) (wardPositive1 c h b a f) r=
      (3:ℂ) • wardDescendant1 c h b a f r := by
  simp only [wardPositive1,wardDescendant2,map_add,map_smul,Nat.cast_add,Nat.cast_one]
  rw [wardSource_L1 c h b a f hf r]
  simp only [wardPositive1,wardDescendant1]
  module



/-- The second source telescope keeps both positive Ward defects. Its
central boundary term is c/2, from commuting L₂ past L₋₂. -/
theorem wardSource_L2 (c h b a : ℂ) (f : ℕ → Verma c h) (hf : WardLevel c h f) (r : ℕ) :
    vermaMode c h 2 (wardSource c h f (r+2))=
      wardSource c h (wardCovariance2 c h b a f) r+
      ((r:ℂ)+4+(h-b+2*a)) • wardSource c h f r+
      (7*(r:ℂ)+4*h+3*(h-b+a)+c/2) • f r+(3:ℂ) • wardPositive1 c h b a f r := by
  classical
  have hcomm (j : Fin (r+2)) :
      vermaMode c h 2 (vermaMode c h ((j:ℤ)-((r:ℤ)+2)) (f j))=
        vermaMode c h ((j:ℤ)-((r:ℤ)+2)) (vermaMode c h 2 (f j))+
          ((r:ℂ)+4-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j)+
          (if j.val=r then c/2 else 0) • f j := by
    have hh := vermaMode_comm_apply c h 2 ((j:ℤ)-((r:ℤ)+2)) (f j)
    rw [show (2:ℤ)+((j:ℤ)-((r:ℤ)+2))=(j:ℤ)-(r:ℤ) by ring] at hh
    have hi : ((j:ℤ)-(r:ℤ)=0) ↔ j.val=r := by omega
    simp only [hi] at hh
    split_ifs at hh ⊢ <;> simp only [LinearMap.smul_apply,Module.End.one_apply,zero_smul] at hh ⊢
    all_goals convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+2), vermaMode c h ((j:ℤ)-((r:ℤ)+2)) (vermaMode c h 2 (f j)))=
      wardSource c h (wardCovariance2 c h b a f) r+
      ∑ j : Fin r, ((j:ℂ)+(h-b+2*a)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j) := by
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.cast_zero,Nat.zero_add,
      verma_mode_above_level c h 0 (f 0) (hf 0) 2 (by norm_num),
      verma_mode_above_level c h 1 (f 1) (hf 1) 2 (by norm_num),map_zero,zero_add]
    rw [wardSource,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hr : vermaMode c h 2 (f (j+2))=wardCovariance2 c h b a f j+
        ((j:ℂ)+(h-b+2*a)) • f j := by unfold wardCovariance2; module
    rw [show j.val+1+1=j.val+2 by omega,hr,map_add,map_smul]
    push_cast
    simp only [show (j:ℤ)+2-((r:ℤ)+2)=(j:ℤ)-(r:ℤ) by omega]
  have hB : (∑ j : Fin (r+2), ((r:ℂ)+4-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))=
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))+
      (7*(r:ℂ)+4*h+3*(h-b+a)) • f r+(3:ℂ) • wardPositive1 c h b a f r := by
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one,sub_self,
      show (r:ℤ)+1-(r:ℤ)=1 by ring,(verma_mem_level_iff_eigen c h r (f r)).mp (hf r)]
    unfold wardPositive1
    module
  have hC : (∑ j : Fin (r+2), (if j.val=r then c/2 else 0) • f j)=(c/2) • f r := by
    rw [Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))]
    · simp
    · intro j hj hjr
      have he : j.val≠r := fun he => hjr (Fin.ext he)
      simp [he]
    · simp
  have hS : (∑ j : Fin r, ((j:ℂ)+(h-b+2*a)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))+
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f j))=
      ((r:ℂ)+4+(h-b+2*a)) • wardSource c h f r := by
    rw [← Finset.sum_add_distrib,wardSource,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    module
  simp only [wardSource,Nat.cast_add,Nat.cast_ofNat,map_sum,hcomm,Finset.sum_add_distrib]
  rw [hA,hB,hC]
  have hh := hS
  simp only [wardSource] at hh
  rw [← hh]
  simp only [wardSource]
  module

/-- The source is linear in the combination defining the second positive
operator, so its two raw defect terms recombine without an assumption. -/
theorem wardSource_positive2 (c h b a : ℂ) (f : ℕ → Verma c h) (r : ℕ) :
    wardSource c h (wardPositive2 c h b a f) r=
      wardSource c h (wardCovariance2 c h b a f) r-
      (3:ℂ) • wardSource c h (wardPositive1 c h b a f) r := by
  simp [wardSource,wardPositive2,Finset.sum_sub_distrib,Finset.smul_sum]

/-- The L₂/L₋₂ descendant commutator has exactly its Virasoro value 4a+c/2.
The central contribution and every nonprimary defect are accounted for. -/
theorem wardPositive2_descendant2 (c h b a : ℂ) (f : ℕ → Verma c h)
    (hf : WardLevel c h f) (r : ℕ) :
    wardPositive2 c h b (a+2) (wardDescendant2 c h b a f) r-
      wardDescendant2 c h b (a-2) (wardPositive2 c h b a f) r=
      (4*a+c/2) • f r := by
  change wardPositive2 c h b (a+2) (wardDescendant2 c h b a f) r-
    (wardSource c h (wardPositive2 c h b a f) r+
      (2*b+(a-2)-h-(r:ℂ)) • wardPositive2 c h b a f r)=_
  rw [wardSource_positive2]
  simp only [wardPositive2,wardCovariance2,wardPositive1,wardDescendant2,map_add,map_smul,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [wardSource_L2 c h b a f hf r,wardSource_L1 c h b a f hf r]
  simp only [wardPositive1,wardCovariance2]
  module

end VOA.InverseDS.VirasoroVerma
