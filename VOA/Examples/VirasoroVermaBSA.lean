/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaPolynomialWard
import VOA.Examples.VirasoroBSARecursion

/-!
# BSA Ward identities in general Verma modules

The vacuum BSA recursion is extended to nonzero highest weight and a free
parameter. This supplies the (1,N) family needed in the general fusion
recursion. The actual mode equations are derived from commutators, rather
than assumed from a singular-vector formula or a fusion rule.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- The free-parameter BSA recursion in the actual Verma module. The source
at the terminal level is kept separate from the zero terminal denominator. -/
noncomputable def vermaBSAState (c h t : ℂ) (N : ℕ) : ℕ → Verma c h
  | 0 => highestVector c h
  | r+1 => (-t / (((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) •
      ∑ j : Fin (r+1), vermaMode c h ((j:ℤ)-((r:ℤ)+1)) (vermaBSAState c h t N j)
termination_by r => r

/-- The source sum before division; its value at level N is the terminal
candidate. Unlike the vacuum case, the first intermediate state can be nonzero. -/
noncomputable def vermaBSASource (c h t : ℂ) (N r : ℕ) : Verma c h :=
  ∑ j : Fin r, vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j)

/-- Level zero is the actual highest vector. -/
@[simp] theorem vermaBSAState_zero (c h t : ℂ) (N : ℕ) :
    vermaBSAState c h t N 0=highestVector c h := by rw [vermaBSAState]

/-- At positive levels the recursion multiplies the source by its displayed
coefficient. Only intermediate levels are later divided by nonzero scalars. -/
theorem vermaBSAState_eq_source (c h t : ℂ) (N r : ℕ) (hr : 0<r) :
    vermaBSAState c h t N r=(-t/((r:ℂ)*((N:ℂ)-(r:ℂ)))) • vermaBSASource c h t N r := by
  cases r with
  | zero => omega
  | succ r => simp only [vermaBSAState,vermaBSASource,Nat.cast_add,Nat.cast_one]

/-- Commuting L₀ through a source raises the relative level by exactly r. -/
theorem vermaBSASource_L0 (c h t : ℂ) (N r : ℕ)
    (ih : ∀ j : Fin r, vermaMode c h 0 (vermaBSAState c h t N j)=
      (h+(j:ℂ)) • vermaBSAState c h t N j) :
    vermaMode c h 0 (vermaBSASource c h t N r)=
      (h+(r:ℂ)) • vermaBSASource c h t N r := by
  simp only [vermaBSASource,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [vermaMode_comm_apply,ih]
  simp only [show ¬ (j:ℤ)-(r:ℤ)=0 by omega,if_false,add_zero,
    map_smul,zero_add,Int.cast_sub,Int.cast_natCast,Int.cast_zero]
  module

/-- All recursively constructed states have actual L₀ weight h+r. -/
theorem vermaBSAState_L0 (c h t : ℂ) (N r : ℕ) :
    vermaMode c h 0 (vermaBSAState c h t N r)=
      (h+(r:ℂ)) • vermaBSAState c h t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r=0
    · subst r
      simpa [vermaMode] using verma_zero_acts c h
    · rw [vermaBSAState_eq_source c h t N r (by omega),map_smul,
        vermaBSASource_L0 c h t N r (fun j => ih j j.isLt),smul_comm]

/-- The charge on the generic (1,N) singular curve. -/
noncomputable def vermaBSACharge (t : ℂ) : ℂ := 13-6*t-6/t

/-- The nonzero highest weight along the generic (1,N) curve; it becomes
zero at t=(N+1)/2, recovering the already proved vacuum specialization. -/
noncomputable def vermaBSAWeight (N : ℕ) (t : ℂ) : ℂ :=
  ((N:ℂ)^2-1)/(4*t)-((N:ℂ)-1)/2

/-- Constant term in the L₁ recurrence; it vanishes at the vacuum parameter. -/
noncomputable def vermaBSAOffset1 (N : ℕ) (t : ℂ) : ℂ := t-((N:ℂ)+1)/2

/-- Constant term in the L₂ recurrence, with level indexed two steps below. -/
noncomputable def vermaBSAOffset2 (N : ℕ) (t : ℂ) : ℂ := 7*t/4-((N:ℂ)+2)/2

/-- L₁ telescoping with the highest-weight boundary term retained. -/
theorem vermaBSASource_L1_step (c h t : ℂ) (N r : ℕ) (a : ℂ)
    (hrec : ∀ j : Fin r, vermaMode c h 1 (vermaBSAState c h t N (j+1)) = ((j:ℂ)+a) • vermaBSAState c h t N j) :
    vermaMode c h 1 (vermaBSASource c h t N (r+1)) =
      ((r:ℂ)+2+a) • vermaBSASource c h t N r + (2*(h+(r:ℂ))) • vermaBSAState c h t N r := by
  classical
  have hcomm (j : Fin (r+1)) :
      vermaMode c h 1 (vermaMode c h ((j:ℤ)-((r:ℤ)+1)) (vermaBSAState c h t N j)) =
        vermaMode c h ((j:ℤ)-((r:ℤ)+1)) (vermaMode c h 1 (vermaBSAState c h t N j)) +
          ((r:ℂ)+2-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j) := by
    have hh := vermaMode_comm_apply c h 1 ((j:ℤ)-((r:ℤ)+1)) (vermaBSAState c h t N j)
    norm_num at hh
    convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+1), vermaMode c h ((j:ℤ)-((r:ℤ)+1)) (vermaMode c h 1 (vermaBSAState c h t N j))) =
      ∑ j : Fin r, ((j:ℂ)+a) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, vermaBSAState_zero, show vermaMode c h 1 (highestVector c h)=0 from verma_pos_annihilate c h 1 (by norm_num),
      map_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.val_succ]
    rw [hrec j, map_smul]
    congr 2
    simp
  have hB : (∑ j : Fin (r+1), ((r:ℂ)+2-(j:ℂ)) •
      vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j)) =
      (∑ j : Fin r, ((r:ℂ)+2-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j)) +
        (2*(h+(r:ℂ))) • vermaBSAState c h t N r := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, sub_self,
      vermaBSAState_L0 c h t N r, smul_smul]
    congr 1
    congr 1
    push_cast
    ring
  simp only [vermaBSASource, Nat.cast_add, Nat.cast_one, map_sum, hcomm, Finset.sum_add_distrib]
  rw [hA, hB, ← add_assoc, ← Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← add_smul]
  congr 1
  ring





/-- The first state includes the L₋₁ descendant, which need not vanish in a
Verma module. Its coefficient is nonzero when t and N-1 are nonzero. -/
theorem vermaBSAState_one (c h t : ℂ) (N : ℕ) :
    vermaBSAState c h t N 1=(-t/((N:ℂ)-1)) • vermaMode c h (-1) (highestVector c h) := by
  rw [vermaBSAState]
  simp

/-- Along the generic highest-weight curve, L₁ lowers every intermediate
state with an affine coefficient in its level. -/
theorem vermaBSAState_L1 (c t : ℂ) (N r : ℕ) (ht : t≠0) (hr : r+1<N) :
    vermaMode c (vermaBSAWeight N t) 1 (vermaBSAState c (vermaBSAWeight N t) t N (r+1))=
      ((r:ℂ)+vermaBSAOffset1 N t) • vermaBSAState c (vermaBSAWeight N t) t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hz : r=0
    · subst r
      rw [vermaBSAState_one,map_smul,vermaMode_comm_apply]
      norm_num [vermaMode,verma_pos_annihilate,verma_zero_acts,vermaBSAState_zero]
      simp only [smul_smul]
      have hn : (N:ℂ)-1≠0 := by exact_mod_cast (show (N:ℤ)-1≠0 by omega)
      congr 1
      unfold vermaBSAWeight vermaBSAOffset1
      field_simp
      <;> ring
    · have hs := vermaBSASource_L1_step c (vermaBSAWeight N t) t N r
        (vermaBSAOffset1 N t) (fun j => ih j (by omega) (by omega))
      rw [vermaBSAState_eq_source _ _ _ N (r+1) (by omega),map_smul,hs]
      rw [vermaBSAState_eq_source _ _ _ N r (by omega)]
      simp only [smul_add,smul_smul,← add_smul]
      congr 1
      have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
      have hd' := bsa_denominator_ne_zero N (r+1) (by omega) hr
      unfold vermaBSAWeight vermaBSAOffset1
      push_cast at hd' ⊢
      field_simp [ht,hd,hd',(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2,
        (mul_ne_zero_iff.mp hd').1,(mul_ne_zero_iff.mp hd').2]
      <;> ring

/-- The terminal source is killed by L₁ at every nonzero parameter on the
(1,N) highest-weight curve, independently of the central charge. -/
theorem vermaBSASource_L1_terminal (c t : ℂ) (N : ℕ) (ht : t≠0) (hN : 2≤N) :
    vermaMode c (vermaBSAWeight N t) 1 (vermaBSASource c (vermaBSAWeight N t) t N N)=0 := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  subst N
  rw [vermaBSASource_L1_step _ _ _ _ r (vermaBSAOffset1 (r+1) t)
      (fun j => vermaBSAState_L1 c t (r+1) j ht (by omega)),
    vermaBSAState_eq_source _ _ _ _ r (by omega),smul_smul,← add_smul]
  have hd : (r:ℂ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have he : ((r:ℂ)+2+vermaBSAOffset1 (r+1) t)+
      (2*(vermaBSAWeight (r+1) t+(r:ℂ)))*(-t/((r:ℂ)*(((r+1:ℕ):ℂ)-(r:ℂ))))=0 := by
    unfold vermaBSAOffset1 vermaBSAWeight
    push_cast
    field_simp
    <;> ring
  rw [he,zero_smul]



/-- L₂ kills the first intermediate state because the highest vector is
killed by L₁ and L₂. No vacuum translation relation is used. -/
theorem vermaBSAState_L2_one (c h t : ℂ) (N : ℕ) :
    vermaMode c h 2 (vermaBSAState c h t N 1)=0 := by
  rw [vermaBSAState_one,map_smul,vermaMode_comm_apply]
  norm_num [vermaMode,verma_pos_annihilate]

/-- L₂ telescoping, including the highest-weight and L₁ boundary terms. -/
theorem vermaBSASource_L2_step (c h t : ℂ) (N r : ℕ) (a b : ℂ)
    (h1 : vermaMode c h 1 (vermaBSAState c h t N (r+1)) = ((r:ℂ)+a) • vermaBSAState c h t N r)
    (h2 : ∀ j : Fin r, vermaMode c h 2 (vermaBSAState c h t N (j+2)) =
      ((j:ℂ)+b) • vermaBSAState c h t N j) :
    vermaMode c h 2 (vermaBSASource c h t N (r+2)) =
      ((r:ℂ)+4+b) • vermaBSASource c h t N r + (7*(r:ℂ)+4*h+3*a+c/2) • vermaBSAState c h t N r := by
  classical
  have hcomm (j : Fin (r+2)) :
      vermaMode c h 2 (vermaMode c h ((j:ℤ)-((r:ℤ)+2)) (vermaBSAState c h t N j)) =
        vermaMode c h ((j:ℤ)-((r:ℤ)+2)) (vermaMode c h 2 (vermaBSAState c h t N j)) +
          ((r:ℂ)+4-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j) +
          (if j.val=r then c/2 else 0) • vermaBSAState c h t N j := by
    have hh := vermaMode_comm_apply c h 2 ((j:ℤ)-((r:ℤ)+2)) (vermaBSAState c h t N j)
    have he : (2:ℤ)+((j:ℤ)-((r:ℤ)+2)) = (j:ℤ)-(r:ℤ) := by ring
    rw [he] at hh
    have hi : ((j:ℤ)-(r:ℤ)=0) ↔ j.val=r := by omega
    simp only [hi] at hh
    split_ifs at hh ⊢ <;> simp only [LinearMap.smul_apply,Module.End.one_apply,zero_smul] at hh ⊢
    all_goals convert hh using 1 <;> push_cast <;> ring
  have hA : (∑ j : Fin (r+2), vermaMode c h ((j:ℤ)-((r:ℤ)+2)) (vermaMode c h 2 (vermaBSAState c h t N j))) =
      ∑ j : Fin r, ((j:ℂ)+b) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.zero_add,
      vermaBSAState_zero, show vermaMode c h 2 (highestVector c h)=0 from verma_pos_annihilate c h 2 (by norm_num), vermaBSAState_L2_one,
      map_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show j.val+1+1=j.val+2 by omega, h2 j, map_smul]
    congr 2
    push_cast
    ring
  have hB : (∑ j : Fin (r+2), ((r:ℂ)+4-(j:ℂ)) •
      vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j)) =
      (∑ j : Fin r, ((r:ℂ)+4-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j)) +
        (7*(r:ℂ)+4*h+3*a) • vermaBSAState c h t N r := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one, sub_self,
      show (r:ℤ)+1-(r:ℤ)=1 by ring, h1,
      vermaBSAState_L0 c h t N r, smul_smul]
    push_cast
    module
  have hC : (∑ j : Fin (r+2), (if j.val=r then c/2 else 0) • vermaBSAState c h t N j) =
      (c/2) • vermaBSAState c h t N r := by
    rw [Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))]
    · simp
    · intro j hj hjr
      have he : j.val ≠ r := fun he => hjr (Fin.ext he)
      simp [he]
    · simp
  simp only [vermaBSASource, Nat.cast_add, Nat.cast_ofNat, map_sum, hcomm,
    Finset.sum_add_distrib]
  rw [hA,hB,hC]
  rw [← add_assoc, ← Finset.sum_add_distrib, Finset.smul_sum]
  have hs : (∑ j : Fin r, (((j:ℂ)+b) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j) +
      ((r:ℂ)+4-(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j))) =
      ∑ j : Fin r, ((r:ℂ)+4+b) • vermaMode c h ((j:ℤ)-(r:ℤ)) (vermaBSAState c h t N j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← add_smul]
    congr 1
    ring
  rw [hs]
  module





/-- L₂ lowers the intermediate states on the full generic singular curve.
The proof keeps both the charge and highest-weight terms in the telescope. -/
theorem vermaBSAState_L2 (t : ℂ) (N r : ℕ) (ht : t≠0) (hr : r+2<N) :
    vermaMode (vermaBSACharge t) (vermaBSAWeight N t) 2
      (vermaBSAState (vermaBSACharge t) (vermaBSAWeight N t) t N (r+2))=
      ((r:ℂ)+vermaBSAOffset2 N t) •
        vermaBSAState (vermaBSACharge t) (vermaBSAWeight N t) t N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    have hs := vermaBSASource_L2_step (vermaBSACharge t) (vermaBSAWeight N t) t N r
      (vermaBSAOffset1 N t) (vermaBSAOffset2 N t)
      (vermaBSAState_L1 _ t N r ht (by omega)) (fun j => ih j j.isLt (by omega))
    rw [vermaBSAState_eq_source _ _ _ N (r+2) (by omega),map_smul,hs]
    have hd' := bsa_denominator_ne_zero N (r+2) (by omega) hr
    by_cases hz : r=0
    · subst r
      simp only [vermaBSASource,Fin.sum_univ_zero,smul_zero,zero_add,smul_smul,
        Nat.cast_zero,Nat.cast_ofNat]
      congr 1
      unfold vermaBSACharge vermaBSAWeight vermaBSAOffset1 vermaBSAOffset2
      norm_num at hd' ⊢
      field_simp [ht,hd']
      <;> ring
    · rw [vermaBSAState_eq_source _ _ _ N r (by omega)]
      simp only [smul_add,smul_smul,← add_smul]
      congr 1
      have hd := bsa_denominator_ne_zero N r (by omega) (by omega)
      unfold vermaBSACharge vermaBSAWeight vermaBSAOffset1 vermaBSAOffset2
      push_cast at hd' ⊢
      field_simp [ht,hd,hd',(mul_ne_zero_iff.mp hd).1,(mul_ne_zero_iff.mp hd).2,
        (mul_ne_zero_iff.mp hd').1,(mul_ne_zero_iff.mp hd').2]
      <;> ring

/-- L₂ kills the terminal source on the generic (1,N) curve for N at least
three. No claim about the separate level-two boundary is needed here. -/
theorem vermaBSASource_L2_terminal (t : ℂ) (N : ℕ) (ht : t≠0) (hN : 3≤N) :
    vermaMode (vermaBSACharge t) (vermaBSAWeight N t) 2
      (vermaBSASource (vermaBSACharge t) (vermaBSAWeight N t) t N N)=0 := by
  obtain ⟨r,hr⟩ : ∃ r : ℕ, N=r+2 := ⟨N-2,by omega⟩
  subst N
  rw [vermaBSASource_L2_step _ _ _ (r+2) r (vermaBSAOffset1 (r+2) t)
      (vermaBSAOffset2 (r+2) t)
      (vermaBSAState_L1 _ t (r+2) r ht (by omega))
      (fun j => vermaBSAState_L2 t (r+2) j ht (by omega)),
    vermaBSAState_eq_source _ _ _ (r+2) r (by omega),smul_smul,← add_smul]
  have hd : (r:ℂ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have he : ((r:ℂ)+4+vermaBSAOffset2 (r+2) t)+
      (7*(r:ℂ)+4*vermaBSAWeight (r+2) t+3*vermaBSAOffset1 (r+2) t+vermaBSACharge t/2)*
      (-t/((r:ℂ)*(((r+2:ℕ):ℂ)-(r:ℂ))))=0 := by
    unfold vermaBSAOffset1 vermaBSAOffset2 vermaBSAWeight vermaBSACharge
    push_cast
    field_simp
    <;> ring
  rw [he,zero_smul]

/-- The generic terminal source satisfies every positive-mode equation.
Nonvanishing is a separate statement: the zero state also satisfies these equations. -/
theorem vermaBSASource_positive_terminal (t : ℂ) (N : ℕ) (ht : t≠0) (hN : 3≤N) :
    ∀ m : ℤ, 0<m → vermaMode (vermaBSACharge t) (vermaBSAWeight N t) m
      (vermaBSASource (vermaBSACharge t) (vermaBSAWeight N t) t N N)=0 :=
  verma_positive_zero_of_one_two _ _ _
    (vermaBSASource_L1_terminal _ t N ht (by omega))
    (vermaBSASource_L2_terminal t N ht hN)



/-- Each intermediate state belongs to the actual PBW word-level span.
All summands have the same creation energy, even at the zero terminal scalar. -/
theorem vermaBSAState_mem_level (c h t : ℂ) (N r : ℕ) :
    vermaBSAState c h t N r∈sortedSpan c h r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r=0
    · subst r
      rw [vermaBSAState_zero]
      exact negWord_mem_sortedSpan_of_sorted c h sortedWord_nil rfl
    · rw [vermaBSAState_eq_source _ _ _ N r (by omega)]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro j hj
      have hs := sortedSpan_stable c h (vermaMode_sorted_insert c h j) (r-j-1) (ih j j.isLt)
      have hn : (j:ℕ)+(r-j-1)+1=r := by omega
      have hi : -((r-j-1:ℕ):ℤ)-1=(j:ℤ)-(r:ℤ) := by omega
      simpa only [hn,hi] using hs

/-- The terminal source itself belongs to its advertised level span. -/
theorem vermaBSASource_mem_level (c h t : ℂ) (N r : ℕ) :
    vermaBSASource c h t N r∈sortedSpan c h r := by
  apply Submodule.sum_mem
  intro j hj
  have hs := sortedSpan_stable c h (vermaMode_sorted_insert c h j) (r-j-1)
    (vermaBSAState_mem_level c h t N j)
  have hn : (j:ℕ)+(r-j-1)+1=r := by omega
  have hi : -((r-j-1:ℕ):ℤ)-1=(j:ℤ)-(r:ℤ) := by omega
  simpa only [hn,hi] using hs

end VOA.InverseDS.VirasoroVerma
