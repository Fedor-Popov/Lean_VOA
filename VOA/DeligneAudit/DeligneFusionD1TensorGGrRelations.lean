import VOA.DeligneAudit.DeligneFusionD1TensorGGrPolynomial
import VOA.DeligneAudit.DeligneFusionD1TensorGGrNil
import VOA.DeligneAudit.DeligneFusionD1TensorGCyclic
import VOA.DeligneAudit.DeligneFusionD1SiteGRelations

/-! Actual filtered highest-weight, sharp simple nilpotence and fusion cutoffs
of the shifted tensor generator, proved from the explicit one-site action. -/
namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
open scoped TensorProduct BigOperators

noncomputable section
variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

/-- A local source eigenrelation lifts to the actual pure tensor generator. -/
theorem local_generator_smul (j : Fin N) (A : Module.End ℂ (D1SiteG.Space S.n)) (a : ℂ)
    (hA : A (D1SiteG.w S.c₀) = a • D1SiteG.w S.c₀) :
    localOp j A (generator S.c₀) = a • generator S.c₀ := by
  rw [generator, localOp_tprod, hA]
  rw [(PiTensorProduct.tprod ℂ).map_update_smul]
  simp only [Function.update_eq_self]

/-- A vanishing local source relation lifts without a global operator-zero premise. -/
theorem local_generator_zero (j : Fin N) (A : Module.End ℂ (D1SiteG.Space S.n))
    (hA : A (D1SiteG.w S.c₀) = 0) : localOp j A (generator S.c₀) = 0 := by
  simpa only [zero_smul] using local_generator_smul S j A 0 (by simpa using hA)

/-- Every positive-root current kills the actual shifted tensor highest vector. -/
theorem tensor_raising (e : Fin S.n) (he : S.raising e) (r : ℕ) :
    (D1TensorG.rep S.f S.jacobi hskew z).op e r (generator S.c₀) = 0 := by
  rw [op_eq_jetOp]
  simp only [JetInterpolation.jetOp, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [local_generator_zero S i _ (D1SiteG.zeroOp_raising S e he),
    local_generator_zero S i _ (D1SiteG.oneOp_w_zero S e
      (D1SiteG.raising_ne_c0 S hskew e he)), smul_zero, smul_zero, add_zero]

/-- The raw tensor Cartan current acts by its explicit scalar moment. -/
theorem tensor_cartan (h : Fin S.n) (hh : S.cartan h) (r : ℕ) :
    (D1TensorG.rep S.f S.jacobi hskew z).op h r (generator S.c₀) =
      ((∑ i, z i ^ r) * (S.thetaH h : ℂ)) • generator S.c₀ := by
  rw [op_eq_jetOp]
  simp only [JetInterpolation.jetOp, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  simp only [local_generator_smul S _ _ _ (D1SiteG.zeroOp_cartan S h hh),
    local_generator_zero S _ _ (D1SiteG.oneOp_w_zero S h
      (D1SiteG.cartan_ne_c0 S hskew h hh)), smul_zero, add_zero, smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_mul]

/-- Negative Cartan conventions satisfy the same genuine scalar relation. -/
theorem tensor_cartanN (h : Fin S.n) (hh : S.cartanN h) (r : ℕ) :
    (D1TensorG.rep S.f S.jacobi hskew z).op h r (generator S.c₀) =
      (-((∑ i, z i ^ r) * (S.thetaN h : ℂ))) • generator S.c₀ := by
  rw [op_eq_jetOp]
  simp only [JetInterpolation.jetOp, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  simp only [local_generator_smul S _ _ _ (D1SiteG.zeroOp_cartanN S h hh),
    local_generator_zero S _ _ (D1SiteG.oneOp_w_zero S h
      (D1SiteG.cartanN_ne_c0 S hskew h hh)), smul_zero, add_zero, smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_mul, mul_neg]

/-- Sharp simple zero-mode nilpotence follows by a binomial pigeonhole bound. -/
theorem tensor_lowering (i : Fin S.n) (hi : S.lowering i) :
    (((D1TensorG.rep S.f S.jacobi hskew z).op i 0) ^
      (N * S.lowExp i + 1)) (generator S.c₀) = 0 := by
  rw [op_eq_jetOp]
  simp only [JetInterpolation.jetOp, pow_zero, one_smul, Nat.cast_zero, zero_mul,
    zero_smul, add_zero]
  have hcomm : ∀ a ∈ (Finset.univ : Finset (Fin N)), ∀ b ∈ Finset.univ,
      Commute (localOp a (D1SiteG.zeroOp S.f i)) (localOp b (D1SiteG.zeroOp S.f i)) := by
    intro a _ b _
    by_cases hab : a = b
    · subst b; exact Commute.refl _
    · exact localOp_comm hab _ _
  have hnil : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      (localOp j (D1SiteG.zeroOp S.f i) ^ (S.lowExp i + 1)) (generator S.c₀) = 0 := by
    intro j _
    apply localOp_pow_zero
    simpa only [Module.End.pow_apply] using D1SiteG.site_lowering_nil S i hi
  have hn := sum_pow_apply_zero (Finset.univ : Finset (Fin N))
    (fun j => localOp j (D1SiteG.zeroOp S.f i)) (fun _ => S.lowExp i)
      (generator S.c₀) hcomm hnil
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hn

/-- A simple-zero site polynomial kills every non-theta fusion color on the generator. -/
theorem tensor_polynomial_non_theta (x : Fin S.n) (hx : x ≠ S.c₀) :
    polynomialOp (D1TensorG.rep S.f S.jacobi hskew z) x (sitePolynomial z)
      (generator S.c₀) = 0 := by
  rw [polynomialOp_tensor]
  simp only [JetInterpolation.jetPolynomialOp, LinearMap.sum_apply,
    LinearMap.smul_apply, sitePolynomial_eval, zero_smul, zero_add]
  simp only [local_generator_zero S _ _ (D1SiteG.oneOp_w_zero S x hx),
    smul_zero, Finset.sum_const_zero]

/-- Double zeros annihilate the whole two-jet action, including theta. -/
theorem tensor_polynomial_square (x : Fin S.n) :
    polynomialOp (D1TensorG.rep S.f S.jacobi hskew z) x ((sitePolynomial z) ^ 2) = 0 := by
  rw [polynomialOp_tensor]
  simp only [JetInterpolation.jetPolynomialOp, Polynomial.eval_pow, sitePolynomial_eval,
    zero_pow (by decide : 2 ≠ 0), sitePolynomial_square_derivative_eval,
    zero_smul, add_zero, Finset.sum_const_zero]

/-- The exact linear non-theta cutoff after passage to current degree. -/
theorem tensor_trunc_non_theta (x : Fin S.n) (hx : x ≠ S.c₀) :
    (D1TensorG.rep S.f S.jacobi hskew z).op x N (generator S.c₀) ∈
      Fbelow (D1TensorG.rep S.f S.jacobi hskew z) (generator S.c₀) N := by
  simpa only [sitePolynomial_degree] using leading_mode_mem
    (D1TensorG.rep S.f S.jacobi hskew z) (generator S.c₀) x (sitePolynomial z)
      (sitePolynomial_monic z) (tensor_polynomial_non_theta S hskew z x hx)

/-- The exact linear theta cutoff after passage to current degree. -/
theorem tensor_trunc_theta :
    (D1TensorG.rep S.f S.jacobi hskew z).op S.c₀ (2 * N) (generator S.c₀) ∈
      Fbelow (D1TensorG.rep S.f S.jacobi hskew z) (generator S.c₀) (2 * N) := by
  have hd : ((sitePolynomial z) ^ 2).natDegree = 2 * N := by
    rw [Polynomial.natDegree_pow, sitePolynomial_degree, Nat.mul_comm]
  have hz := congrArg (fun A : Module.End ℂ (D1TensorG.Space S.n N) => A (generator S.c₀))
    (tensor_polynomial_square S hskew z S.c₀)
  simpa only [hd] using leading_mode_mem
    (D1TensorG.rep S.f S.jacobi hskew z) (generator S.c₀) S.c₀ ((sitePolynomial z) ^ 2)
      ((sitePolynomial_monic z).pow 2) hz

end
end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.tensor_lowering
#print axioms VOA.DeligneAudit.D1TensorG.Gr.tensor_trunc_non_theta
#print axioms VOA.DeligneAudit.D1TensorG.Gr.tensor_trunc_theta
