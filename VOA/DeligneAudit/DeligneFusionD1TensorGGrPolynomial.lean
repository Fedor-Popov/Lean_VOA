import VOA.DeligneAudit.DeligneFusionD1TensorGGrCore
import VOA.DeligneAudit.DeligneFusionD1TensorGShift
import Mathlib.Algebra.Polynomial.BigOperators

/-! Monic annihilating polynomials give actual filtered leading-mode relations. -/
namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl Polynomial
open scoped BigOperators

noncomputable section
variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {T : Type*} [AddCommGroup T] [Module ℂ T]
variable (R : CurrentModule f T) (w : T)

/-- A scalar polynomial applied to one current color. -/
def polynomialOp (c : Fin n) (P : ℂ[X]) : Module.End ℂ T :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • R.op c k

/-- Its top mode belongs to strictly lower current degree whenever the
monic polynomial action kills the source generator. -/
theorem leading_mode_mem (c : Fin n) (P : ℂ[X]) (hP : P.Monic)
    (hzero : polynomialOp R c P w = 0) :
    R.op c P.natDegree w ∈ Fbelow R w P.natDegree := by
  have he : (∑ k ∈ Finset.range P.natDegree, P.coeff k • R.op c k w) +
      R.op c P.natDegree w = 0 := by
    simpa only [polynomialOp, Finset.sum_range_succ, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, hP.coeff_natDegree, one_smul] using hzero
  have hlow : (∑ k ∈ Finset.range P.natDegree, P.coeff k • R.op c k w) ∈
      Fbelow R w P.natDegree := by
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    exact Submodule.subset_span
      ⟨[(c, k)], by simpa only [degree, SectorGraded.wordDeg, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using Finset.mem_range.mp hk, rfl⟩
  have hx : R.op c P.natDegree w =
      -(∑ k ∈ Finset.range P.natDegree, P.coeff k • R.op c k w) := by
    exact eq_neg_of_add_eq_zero_right he
  rw [hx]
  exact Submodule.neg_mem _ hlow

variable {N : ℕ}

/-- The monic polynomial of the actual evaluation sites. -/
def sitePolynomial (z : Fin N → ℂ) : ℂ[X] := ∏ i, (Polynomial.X - Polynomial.C (z i))

theorem sitePolynomial_monic (z : Fin N → ℂ) : (sitePolynomial z).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (z i))

theorem sitePolynomial_degree (z : Fin N → ℂ) : (sitePolynomial z).natDegree = N := by
  rw [sitePolynomial, natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (z i))]
  simp

theorem sitePolynomial_eval (z : Fin N → ℂ) (i : Fin N) :
    (sitePolynomial z).eval (z i) = 0 := by
  rw [sitePolynomial, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem sitePolynomial_square_derivative_eval (z : Fin N → ℂ) (i : Fin N) :
    ((sitePolynomial z) ^ 2).derivative.eval (z i) = 0 := by
  rw [pow_two, derivative_mul, eval_add, eval_mul, eval_mul, sitePolynomial_eval]
  simp

/-- The tensor polynomial action is exactly the checked local two-jet evaluation. -/
theorem polynomialOp_tensor (f : Fin n → Fin n → Fin n → ℂ)
    (hJ : SectorLoop.JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)
    (z : Fin N → ℂ) (c : Fin n) (P : ℂ[X]) :
    polynomialOp (D1TensorG.rep f hJ hskew z) c P =
      JetInterpolation.jetPolynomialOp z
        (fun i => localOp i (D1SiteG.zeroOp f c))
        (fun i => localOp i (D1SiteG.oneOp c)) P := by
  unfold polynomialOp
  simp only [op_eq_jetOp]
  exact JetInterpolation.sum_coeff_jetOp z _ _ P _ (Nat.lt_succ_self _)

end
end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.leading_mode_mem
#print axioms VOA.DeligneAudit.D1TensorG.Gr.polynomialOp_tensor
