/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeNormPolynomial

/-!
# Differentiating a moving word expression at a radical state

When the initial state lies in the canonical radical, differentiating its
word coefficients contributes zero. Only the derivative of the central
charge survives. This justifies the radical part of a moving-parameter
argument, without asserting that any proposed moving source satisfies a
norm identity.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes VirDeformModes.NormalOrdering

/-- The product rule for a finite polynomial Gram matrix at a two-sided
null vector. Terms differentiating either vector vanish by the row and
column relations, leaving only the changing central parameter. -/
theorem finiteGram_moving_derivative {ι : Type*} [Fintype ι]
    (P : ι → ι → Polynomial ℂ) (v : ι → ℂ → ℂ) (v' : ι → ℂ)
    (c : ℂ → ℂ) (c' t0 : ℂ) (hv : ∀ i, HasDerivAt (v i) (v' i) t0)
    (hc : HasDerivAt c c' t0)
    (hrow : ∀ i, ∑ j, (P i j).eval (c t0)*v j t0=0)
    (hcol : ∀ j, ∑ i, v i t0*(P i j).eval (c t0)=0) :
    HasDerivAt (fun t => ∑ i, ∑ j, v i t*(P i j).eval (c t)*v j t)
      (c'*(∑ i, ∑ j, v i t0*(P i j).derivative.eval (c t0)*v j t0)) t0 := by
  classical
  have h := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
      ((hv i).mul (((P i j).hasDerivAt (c t0)).comp t0 hc)).mul (hv j)))
  have hL : (∑ i, ∑ j, v' i*(P i j).eval (c t0)*v j t0)=0 := by
    simp_rw [mul_assoc,← Finset.mul_sum,hrow,mul_zero]
    simp
  have hR : (∑ i, ∑ j, v i t0*(P i j).eval (c t0)*v' j)=0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hcol,zero_mul]
    simp
  have he : (∑ i, ∑ j,
      ((v' i*(P i j).eval (c t0)+v i t0*((P i j).derivative.eval (c t0)*c'))*v j t0+
        (v i t0*(P i j).eval (c t0))*v' j))=
      c'*(∑ i, ∑ j, v i t0*(P i j).derivative.eval (c t0)*v j t0) := by
    simp only [add_mul,Finset.sum_add_distrib]
    rw [hL,hR,zero_add,add_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

  simp only [Function.comp_apply,Pi.mul_apply] at h
  rw [he] at h
  exact h

/-- For an actual finite word family through a radical state, the moving
norm derivative is the charge velocity times the fixed-vector norm
polynomial derivative. Word-coefficient velocities make no contribution. -/
theorem wordNorm_moving_derivative {ι : Type*} [Fintype ι]
    (w : ι → VirWordExpression) (v : ι → ℂ → ℂ) (v' : ι → ℂ)
    (c : ℂ → ℂ) (c' t0 : ℂ) (hv : ∀ i, HasDerivAt (v i) (v' i) t0)
    (hc : HasDerivAt c c' t0)
    (hleft : ∀ x, (VirGram4.canB (c t0)).form
      (wordExpressionEval (c t0) (∑ i, v i t0 • w i)) x=0)
    (hright : ∀ x, (VirGram4.canB (c t0)).form x
      (wordExpressionEval (c t0) (∑ i, v i t0 • w i))=0) :
    HasDerivAt (fun t => (VirGram4.canB (c t)).form
      (wordExpressionEval (c t) (∑ i, v i t • w i))
      (wordExpressionEval (c t) (∑ i, v i t • w i)))
      (c'*(wordExpressionPair (∑ i, v i t0 • w i)
        (∑ i, v i t0 • w i)).derivative.eval (c t0)) t0 := by
  classical
  have hrow (i : ι) : ∑ j, (wordExpressionPair (w i) (w j)).eval (c t0)*v j t0=0 := by
    have h := hright (wordExpressionEval (c t0) (w i))
    simpa only [map_sum,map_smul,smul_eq_mul,← wordExpressionPair_eval,mul_comm] using h
  have hcol (j : ι) : ∑ i, v i t0*(wordExpressionPair (w i) (w j)).eval (c t0)=0 := by
    have h := hleft (wordExpressionEval (c t0) (w j))
    simpa only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
      smul_eq_mul,← wordExpressionPair_eval] using h
  have h := finiteGram_moving_derivative (fun i j => wordExpressionPair (w i) (w j))
    v v' c c' t0 hv hc hrow hcol
  convert h using 1
  · funext t
    simp only [← wordExpressionPair_eval,map_sum,map_smul,LinearMap.sum_apply,
      LinearMap.smul_apply,Polynomial.eval_finsetSum,Polynomial.eval_smul,smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
      Polynomial.derivative_sum,Polynomial.derivative_smul,Polynomial.eval_finsetSum,
      Polynomial.eval_smul,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring


/-- Applied to the actual M(p,3) singular source, radical cancellation
removes all moving word-coefficient derivatives. A future moving-source
construction must still prove its coefficient differentiability and norm
identity; neither is supplied as a conclusion of this chain rule. -/
theorem minimalThree_moving_norm_hasDerivAt {ι : Type*} [Fintype ι]
    (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (w : ι → VirWordExpression) (v : ι → ℂ → ℂ) (v' : ι → ℂ)
    (c : ℂ → ℂ) (c' t0 : ℂ) (hv : ∀ i, HasDerivAt (v i) (v' i) t0)
    (hc : HasDerivAt c c' t0)
    (hc0 : c t0=vermaBSACharge ((3:ℂ)/(p:ℂ)))
    (hs : ∑ i, v i t0 • w i=minimalThreeExpression p hp hcop) :
    HasDerivAt (fun t => (VirGram4.canB (c t)).form
      (wordExpressionEval (c t) (∑ i, v i t • w i))
      (wordExpressionEval (c t) (∑ i, v i t • w i)))
      (c'*(minimalThreeNormPolynomial p hp hcop).derivative.eval
        (vermaBSACharge ((3:ℂ)/(p:ℂ)))) t0 := by
  have hleft : ∀ x, (VirGram4.canB (c t0)).form
      (wordExpressionEval (c t0) (∑ i, v i t0 • w i)) x=0 := by
    rw [hs,hc0,minimalThreeExpression_eval]
    exact canB_singular_left_zero _ (n:=(p-1)*2) (by omega) _
      (minimalThreeChargeVacuum_level p hp hcop _)
      (minimalThreeChargeVacuum_L1 p hp hcop _)
      (minimalThreeChargeVacuum_L2_at_root p hp hcop)
  have hright : ∀ x, (VirGram4.canB (c t0)).form x
      (wordExpressionEval (c t0) (∑ i, v i t0 • w i))=0 := by
    rw [hs,hc0,minimalThreeExpression_eval]
    exact canB_singular_right_zero _ (n:=(p-1)*2) (by omega) _
      (minimalThreeChargeVacuum_level p hp hcop _)
      (minimalThreeChargeVacuum_L1 p hp hcop _)
      (minimalThreeChargeVacuum_L2_at_root p hp hcop)
  have hh := wordNorm_moving_derivative w v v' c c' t0 hv hc hleft hright
  simpa only [hs,hc0,minimalThreeNormPolynomial] using hh

end VOA.InverseDS.VirasoroVerma
