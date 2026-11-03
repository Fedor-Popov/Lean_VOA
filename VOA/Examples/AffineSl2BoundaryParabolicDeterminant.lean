/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BoundaryParabolicRoots
import VOA.Examples.AffineSl2KacParabolicCoefficient
import VOA.Examples.AffineSl2ParabolicFirstBlock

/-! # Actual reflected Verma nondegeneracy in the boundary parabolic range -/
namespace VOA.AffineSl2BoundaryParabolicRoots
open Polynomial AffineVOA.HighestModule Wak.Charged
noncomputable section
local instance boundaryParabolicDetFintype (n : ℕ) (c : ℤ) :
    Fintype (JointIndex n c) := jointIndexFintype n c

/-- Every resonant factor in the reflected block has actual multiplicity zero. -/
theorem reflected_kac_product_ne_zero (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) (n : ℕ) (c : ℤ) (hn : n≤P*r) (hc : 0≤c) :
    (affineKacProduct (2/(P : ℂ)) n c).eval (-2*(r : ℂ)) ≠ 0 := by
  classical
  simp only [affineKacProduct,eval_prod,eval_pow,eval_sub,eval_X,eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_cases hz : realRootWeight (2/(P : ℂ)) i = -2*(r : ℂ)
  · rw [reflected_resonant_multiplicity_zero P r hP hr hcop n c hn hc i hi hz,pow_zero]
    exact one_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hz))

/-- Nonvanishing of the actual normalized reflected Verma determinant,
including all levels where formal real-root factors collide. -/
theorem reflected_weightDeterminant_ne_zero (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) (n : ℕ) (c : ℤ) (hn : n≤P*r) (hc : 0≤c) :
    (weightDeterminant (2/(P : ℂ)-2) n c).eval (-2*(r : ℂ)) ≠ 0 := by
  rw [weightDeterminant_eq_affineKacProduct_all,eval_mul,eval_C]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply derivativeMultiplier_ne_zero
    have hp : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hP)
    simpa only [sub_add_cancel] using div_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hp
  · exact reflected_kac_product_ne_zero P r hP hr hcop n c hn hc

/-- The explicit horizontal-factor-removed product is nonzero strictly
below the next affine singular energy, at every charge cutoff. -/
theorem parabolic_product_below_ne_zero (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) (n : ℕ) (c : ℤ) (hn : n<P*r) :
    (affineParabolicProduct (2*r-2) n c).eval (2/(P : ℂ)-2) ≠ 0 := by
  classical
  simp only [affineParabolicProduct,eval_prod,eval_pow,eval_sub,eval_add,eval_mul,eval_C,
    eval_X,sub_add_cancel]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro hz
  have hd : ((2*r-2 : ℕ) : ℂ) = 2*(r : ℂ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*r)]
    push_cast
    ring
  have he := kac_labels_below_first P r hP hr hcop n c hn i
    (Finset.mem_erase.mp hi).2 (by rw [hd] at hz; exact hz.symm)
  exact (Finset.mem_erase.mp hi).1 he

/-- At the next singular energy the reduced product genuinely vanishes:
the surviving positive root has multiplicity one. -/
theorem parabolic_product_first_zero (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (c : ℤ) (hc : c≤1) :
    (affineParabolicProduct (2*r-2) (P*r) c).eval (2/(P : ℂ)-2) = 0 := by
  classical
  simp only [affineParabolicProduct,eval_prod,eval_pow,eval_sub,eval_add,eval_mul,eval_C,
    eval_X,sub_add_cancel]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨by simp, next_label_mem P r hP hr c hc⟩)
  rw [next_label_multiplicity P r hP hr c hc,pow_one]
  have hd : ((2*r-2 : ℕ) : ℂ) = 2*(r : ℂ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*r)]
    push_cast
    ring
  change ((2*r-2 : ℕ) : ℂ) - realRootWeight (2/(P : ℂ)) ((0,P*r-1),0) = 0
  rw [hd,next_label_resonant P r hP hr,sub_self]

/-- Below the next affine root, every actual parabolic joint Gram form is
nondegenerate, for every charge and including empty reflected blocks. -/
theorem parabolic_quotientGram_below_ne_zero (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) (n : ℕ) (c : ℤ) (hn : n<P*r) :
    (parabolicQuotientGram (2/(P : ℂ)-2) (2*r-2) n c).det ≠ 0 := by
  have he := parabolic_determinant_identity (2/(P : ℂ)-2) (2*r-2) n c
  have hlevel : 2/(P : ℂ)-2+2 ≠ 0 := by
    simpa only [sub_add_cancel] using
      div_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hP))
  have hnz := mul_ne_zero (parabolicDeterminantScale_ne_zero (2*r-2) n c)
    (mul_ne_zero (affineLeadingPolynomial_eval_ne_zero _ hlevel n c)
      (parabolic_product_below_ne_zero P r hP hr hcop n c hn))
  intro hz
  rw [hz,zero_mul] at he
  exact hnz he.symm

/-- The actual parabolic charge-one Gram determinant vanishes at exactly
the next candidate energy; the reflected denominator is proved nonzero. -/
theorem parabolic_quotientGram_first_zero (P r : ℕ) (hP : 0<P) (hr : 0<r)
    (hcop : P.Coprime 2) :
    (parabolicQuotientGram (2/(P : ℂ)-2) (2*r-2) (P*r) 1).det = 0 := by
  have he := parabolic_determinant_identity (2/(P : ℂ)-2) (2*r-2) (P*r) 1
  rw [parabolic_product_first_zero P r hP hr 1 le_rfl,mul_zero,mul_zero] at he
  apply (mul_eq_zero.mp he).resolve_right
  apply mul_ne_zero (pow_ne_zero _ (reflectionNormScale_ne_zero _))
  have hd : ((2*r-2 : ℕ) : ℂ) = 2*(r : ℂ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*r)]
    push_cast
    ring
  have hz : -((2*r-2 : ℕ) : ℂ)-2 = -2*(r : ℂ) := by rw [hd]; ring
  rw [hz]
  exact reflected_weightDeterminant_ne_zero P r hP hr hcop (P*r)
    (1+((2*r-2 : ℕ) : ℤ)+1) le_rfl (by positivity)

end
end VOA.AffineSl2BoundaryParabolicRoots
