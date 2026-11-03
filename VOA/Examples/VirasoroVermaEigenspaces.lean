/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaWardSpecialization

/-!
# Actual L₀ eigenspaces of general Verma modules

The proved PBW basis makes L₀ diagonal. Its eigenvalue at a word is h plus
the word's creation energy. This identifies actual eigenspaces with the
word-level spans and rules out negative relative levels. These statements
justify the boundary equations for graded coefficient sequences.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- L₀ acts diagonally on every PBW coordinate of an arbitrary state. -/
theorem verma_L0_coordinate (c h : ℂ) (v : Verma c h)
    (w : {w : List ℕ // SortedWord w}) :
    (vermaSortedBasis c h).repr (vermaMode c h 0 v) w=
      (h+(energyHW w.val:ℂ)) * (vermaSortedBasis c h).repr v w := by
  classical
  let E : Verma c h →ₗ[ℂ] ℂ := (Finsupp.lapply w).comp (vermaSortedBasis c h).repr.toLinearMap
  have he : E.comp (vermaMode c h 0)=(h+(energyHW w.val:ℂ)) • E := by
    apply (vermaSortedBasis c h).ext
    intro u
    simp only [vermaSortedBasis_apply]
    change (vermaSortedBasis c h).repr (vermaMode c h 0 (negWord c h u.val)) w=
      (h+(energyHW w.val:ℂ)) * (vermaSortedBasis c h).repr (negWord c h u.val) w
    rw [vermaMode_zero_negWord,map_smul,Finsupp.smul_apply,smul_eq_mul]
    have hucoord : (vermaSortedBasis c h).repr (negWord c h u.val)=Finsupp.single u 1 := by
      simpa only [vermaSortedBasis_apply] using (vermaSortedBasis c h).repr_self u
    rw [hucoord]
    by_cases hu : u=w
    · subst u; simp
    · simp [hu,Ne.symm hu]
  exact LinearMap.congr_fun he v

/-- An eigenvector can have a nonzero PBW coordinate only at matching
relative energy. Distinct natural levels remain distinct at every charge. -/
theorem verma_eigen_coordinate_zero (c h : ℂ) (v : Verma c h) (z : ℂ)
    (hv : vermaMode c h 0 v=(h+z) • v)
    (w : {w : List ℕ // SortedWord w}) (hw : (energyHW w.val:ℂ)≠z) :
    (vermaSortedBasis c h).repr v w=0 := by
  have he := verma_L0_coordinate c h v w
  rw [hv,map_smul,Finsupp.smul_apply,smul_eq_mul] at he
  have hn : (h+z)-(h+(energyHW w.val:ℂ))≠0 := by
    intro he
    apply hw
    linear_combination -he
  exact (mul_eq_zero.mp (by linear_combination he :
    ((h+z)-(h+(energyHW w.val:ℂ))) * (vermaSortedBasis c h).repr v w=0)).resolve_left hn

/-- The actual eigenspace of weight h+n is exactly the span of level-n
creation words. This strengthens the earlier word-level basis theorem. -/
theorem verma_mem_level_iff_eigen (c h : ℂ) (n : ℕ) (v : Verma c h) :
    v∈sortedSpan c h n ↔ vermaMode c h 0 v=(h+(n:ℂ)) • v := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w,hw,he,rfl⟩ := hx
      rw [vermaMode_zero_negWord,he]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add,hx,hy,smul_add]
    | smul a x _ hx => rw [map_smul,hx,smul_comm]
  · intro hv
    rw [← (vermaSortedBasis c h).linearCombination_repr v]
    change (∑ w ∈ ((vermaSortedBasis c h).repr v).support,
      (vermaSortedBasis c h).repr v w • (vermaSortedBasis c h) w) ∈ _
    apply Submodule.sum_mem
    intro w hw
    by_cases he : energyHW w.val=n
    · apply Submodule.smul_mem
      simpa only [vermaSortedBasis_apply] using negWord_mem_sortedSpan_of_sorted c h w.property he
    · have hz := verma_eigen_coordinate_zero c h v n hv w (by exact_mod_cast he)
      simp only [hz,zero_smul]
      exact Submodule.zero_mem _

/-- There is no nonzero state at a negative integer relative level. -/
theorem verma_eigen_negative_zero (c h : ℂ) (v : Verma c h) (n : ℤ)
    (hn : n<0) (hv : vermaMode c h 0 v=(h+(n:ℂ)) • v) : v=0 := by
  apply (vermaSortedBasis c h).repr.injective
  ext w
  simp only [map_zero,Finsupp.zero_apply]
  apply verma_eigen_coordinate_zero c h v n hv w
  intro he
  have he' : (energyHW w.val:ℤ)=n := by exact_mod_cast he
  omega

/-- Applying mode m shifts an L₀ eigenvalue by minus m. The central term
in its commutator with L₀ is zero, including when m itself is zero. -/
theorem verma_mode_eigen_shift (c h : ℂ) (v : Verma c h) (z : ℂ) (m : ℤ)
    (hv : vermaMode c h 0 v=z • v) :
    vermaMode c h 0 (vermaMode c h m v)=(z-(m:ℂ)) • vermaMode c h m v := by
  rw [vermaMode_comm_apply,hv,map_smul]
  split_ifs <;> simp only [Int.cast_zero,zero_pow (by norm_num : 3≠0),sub_self,
    zero_div,zero_mul,zero_smul,LinearMap.zero_apply,add_zero,zero_add,zero_sub]
  all_goals module

/-- Modes above a state's relative level kill it. This derives the finite
boundary conditions needed for Ward sequences from the actual module. -/
theorem verma_mode_above_level (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v∈sortedSpan c h n) (m : ℤ) (hm : (n:ℤ)<m) :
    vermaMode c h m v=0 := by
  apply verma_eigen_negative_zero c h _ ((n:ℤ)-m) (by omega)
  have he := verma_mode_eigen_shift c h v (h+(n:ℂ)) m
    ((verma_mem_level_iff_eigen c h n v).mp hv)
  convert he using 1 <;> push_cast <;> ring

/-- Whenever the shifted relative level is nonnegative, the actual mode
lands in that precise PBW level span. -/
theorem verma_mode_mem_level (c h : ℂ) (n k : ℕ) (v : Verma c h)
    (hv : v∈sortedSpan c h n) (m : ℤ) (hm : (n:ℤ)-m=k) :
    vermaMode c h m v∈sortedSpan c h k := by
  apply (verma_mem_level_iff_eigen c h k _).mpr
  have he := verma_mode_eigen_shift c h v (h+(n:ℂ)) m
    ((verma_mem_level_iff_eigen c h n v).mp hv)
  have hh : (n:ℂ)-(m:ℂ)=(k:ℂ) := by exact_mod_cast hm
  convert he using 1
  congr 1
  linear_combination -hh

end VOA.InverseDS.VirasoroVerma
