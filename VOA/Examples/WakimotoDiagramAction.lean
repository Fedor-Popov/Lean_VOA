/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HighestKacRoots

/-!
# The affine diagram symmetry on the actual charged Fock module

Interchanging the two affine simple roots sends E_n to F_(n+1), F_n to
E_(n-1), and H_n to -H_n plus k at n=0. The highest weight becomes k-lambda.
The principal grading is unchanged. This is an actual representation and
highest projection, not an assumed symmetry of a determinant formula.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial AffineVOA
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord)
noncomputable section

/-- Actual currents after exchanging the two affine simple roots. -/
def diagramJ (k lam : ℂ) (a : Fin 3) (n : ℤ) : End ℂ WakFock :=
  if a=0 then F k lam (n+1) else if a=1 then Ecur (n-1) else
    -H k lam n + if n=0 then k • (1 : End ℂ WakFock) else 0

/-- The transformed raising mode is the shifted original lowering mode. -/
theorem diagramJ_E (k lam : ℂ) (n : ℤ) : diagramJ k lam 0 n=F k lam (n+1) := by simp [diagramJ]

/-- The transformed lowering mode is the shifted original raising mode. -/
theorem diagramJ_F (k lam : ℂ) (n : ℤ) : diagramJ k lam 1 n=Ecur (n-1) := by norm_num [diagramJ]

/-- The transformed Cartan mode has the forced central correction at zero. -/
theorem diagramJ_H (k lam : ℂ) (n : ℤ) : diagramJ k lam 2 n=
    -H k lam n+if n=0 then k • (1 : End ℂ WakFock) else 0 := by
  norm_num [diagramJ,Fin.ext_iff]

set_option maxHeartbeats 1000000 in
/-- Diagram-transformed currents satisfy all ACTUAL affine commutators at
unchanged level, including the central correction in the opposite roots. -/
theorem diagramJ_comm (k lam : ℂ) (hk : k+2≠0) (a b : Fin 3) (m n : ℤ) :
    ⁅diagramJ k lam a m,diagramJ k lam b n⁆=
      (∑ c,fabc a b c • diagramJ k lam c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ WakFock) else 0 := by
  have hs (z : ℂ) (T : End ℂ WakFock) : ⁅T,z • (1 : End ℂ WakFock)⁆=0 := by
    rw [lie_swap,scalar_lie,neg_zero]
  have fe : ⁅F k lam (m+1),Ecur (n-1)⁆=
      -H k lam (m+n) + if m+n=0 then ((1+(m : ℂ))*k) • (1 : End ℂ WakFock) else 0 := by
    rw [lie_swap,ef,show n-1+(m+1)=m+n by omega]
    by_cases hz : m+n=0
    · have hn : (n : ℂ)=-(m : ℂ) := by exact_mod_cast (show n= -m by omega)
      simp only [if_pos hz,Int.cast_sub,Int.cast_one,hn]
      module
    · simp only [if_neg hz,add_zero]
  have ef' : ⁅Ecur (m-1),F k lam (n+1)⁆=
      H k lam (m+n)+if m+n=0 then (((m : ℂ)-1)*k) • (1 : End ℂ WakFock) else 0 := by
    rw [ef,show m-1+(n+1)=m+n by omega,Int.cast_sub,Int.cast_one]
  rcases fin3_cases a with rfl|rfl|rfl <;> rcases fin3_cases b with rfl|rfl|rfl <;>
    simp only [diagramJ_E,diagramJ_F,diagramJ_H,Fin.sum_univ_three,fabc,kappa]
  · rw [ff k lam hk]; split_ifs <;> module
  · rw [fe]; split_ifs <;> module
  · simp only [lie_add,lie_neg]
    rw [lie_swap,hf k lam hk,show n+(m+1)=m+n+1 by omega]
    split_ifs <;> simp only [hs,lie_zero] <;> module
  · rw [ef']; split_ifs <;> module
  · rw [rel_ee]; split_ifs <;> module
  · simp only [lie_add,lie_neg]
    rw [lie_swap,he,show n+(m-1)=m+n-1 by omega]
    split_ifs <;> simp only [hs,lie_zero] <;> module
  · simp only [add_lie,neg_lie]
    rw [hf k lam hk,show m+(n+1)=m+n+1 by omega]
    split_ifs <;> simp only [scalar_lie,zero_lie] <;> module
  · simp only [add_lie,neg_lie]
    rw [he,show m+(n-1)=m+n-1 by omega]
    split_ifs <;> simp only [scalar_lie,zero_lie] <;> module
  · simp only [add_lie,lie_add,neg_lie,lie_neg]
    rw [hh k lam hk]
    split_ifs <;> simp only [scalar_lie,hs,zero_lie,lie_zero] <;> module

/-- The actual polynomial one is highest for the transformed positive
Borel and its Cartan eigenvalue is k-lambda. -/
theorem diagramJ_one_highest (k lam : ℂ) (a : Fin 3) (m : ℤ)
    (hm : ¬IsLower a m) :
    diagramJ k lam a m (1 : WakFock)=if m=0 ∧ a=2 then (k-lam) • (1 : WakFock) else 0 := by
  have hm0 : 0≤m := by simp only [IsLower,not_or] at hm; omega
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [diagramJ_E]
    have h := J_one_positive k lam 1 (m+1) (by omega)
    rw [J_F] at h
    rw [h,if_neg (by simp [Fin.ext_iff])]
  · have hp : 0<m := by by_contra hz; apply hm; right; exact ⟨by omega,rfl⟩
    rw [diagramJ_F,Ecur_one (show 0≤m-1 by omega),if_neg (by simp [Fin.ext_iff])]
  · rw [diagramJ_H]
    by_cases hz : m=0
    · subst m
      simp only [if_pos rfl,LinearMap.add_apply,LinearMap.neg_apply,LinearMap.smul_apply,
        Module.End.one_apply,H_one]
      norm_num
      module
    · have hh := J_one_positive k lam 2 m (by omega)
      rw [J_H] at hh
      simp only [if_neg hz,add_zero,LinearMap.neg_apply,hh,neg_zero]
      rw [if_neg (by simp [hz])]

/-- Diagram symmetry preserves principal root height on actual currents. -/
theorem principalD_diagramJ (k lam : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅principalD,diagramJ k lam a n⁆=
      ((-2*n-colourCharge a : ℤ) : ℂ) • diagramJ k lam a n := by
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [diagramJ_E,← J_F,principalD_J,J_F]
    norm_num [colourCharge,Fin.ext_iff]
    congr 1
    ring
  · rw [diagramJ_F,← J_E k lam,principalD_J,J_E]
    norm_num [colourCharge,Fin.ext_iff]
    congr 1
    ring
  · rw [diagramJ_H,lie_add,lie_neg,← J_H,principalD_J,J_H]
    have hs : ⁅principalD,k • (1 : End ℂ WakFock)⁆=0 := by rw [lie_smul,lie_one',smul_zero]
    by_cases hz : n=0
    · subst n; simp [hs,colourCharge,Fin.ext_iff]
    · simp only [if_neg hz,lie_zero,add_zero]
      norm_num [colourCharge,Fin.ext_iff]

/-- The actual principal eigenvalue of every transformed finite word is
still the sum of its creation root heights. -/
theorem diagramWord_principal (k lam : ℂ) (w : List (Fin 3×ℤ)) :
    principalD (currentWord (diagramJ k lam) w (1 : WakFock))=
      (wordPrincipal w : ℂ) • currentWord (diagramJ k lam) w (1 : WakFock) := by
  induction w with
  | nil => simp [currentWord,wordPrincipal,principalD,Dwt,Dch,Eul_one']
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ WakFock => T (currentWord (diagramJ k lam) w 1))
        (principalD_diagramJ k lam an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply] at hc
      simp only [currentWord,Module.End.mul_apply,wordPrincipal,Int.cast_add,add_smul]
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]

/-- Constant coefficient is the normalized highest projection for the
transformed action as well: every nonempty creation word has positive degree. -/
theorem constantCoeff_diagram_lower (k lam : ℂ) (w : List (Fin 3×ℤ))
    (hw : ∀ an∈w,IsLower an.1 an.2) :
    constantCoeff (currentWord (diagramJ k lam) w (1 : WakFock))=if w=[] then 1 else 0 := by
  by_cases he : w=[]
  · subst w; simp [currentWord]
  · rw [if_neg he]
    have hn : (wordPrincipal w : ℂ)≠0 := by
      exact_mod_cast (fun h => he ((lower_wordPrincipal w hw).2.mp h))
    have hc := congrArg constantCoeff (diagramWord_principal k lam w)
    rw [constantCoeff_principalD,smul_eq_C_mul,map_mul,constantCoeff_C] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left hn

/-- The SAME ordinary word polynomial evaluates to the actual transformed
highest projection at weight k-lambda. -/
theorem wordPolynomial_diagram (k lam : ℂ) (hk : k+2≠0) (w : List (Fin 3×ℤ)) :
    constantCoeff (currentWord (diagramJ k lam) w (1 : WakFock))=
      MvPolynomial.eval ![k,k-lam] (wordPolynomial w) := by
  rw [← evaluate_wordNormal _ _ _ _ (diagramJ_comm k lam hk) (diagramJ_one_highest k lam)]
  change constantCoeff (evaluate (diagramJ k lam) k (k-lam) 1 (wordNormal w))=
    MvPolynomial.eval ![k,k-lam] (highestPolynomial (wordNormal w))
  have hf := wordNormal_mem_lowerForms w
  generalize he : wordNormal w=f at hf ⊢
  clear he w
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t,ht,rfl⟩ := hf
      rw [evaluate_single,one_smul,smul_eq_C_mul,map_mul,constantCoeff_C,
        constantCoeff_diagram_lower k lam _ ht,
        highestPolynomial,Finsupp.linearCombination_single,one_smul]
      split_ifs <;> simp [map_mul,map_pow]
  | zero => simp [wordPolynomial]
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul z f hf ih => simp only [map_smul,smul_eq_C_mul,map_mul,constantCoeff_C,eval_C,ih]

end
end VOA.Wak.Charged
