import VOA.DeligneAudit.D4FusionToroidalFusionAction
import VOA.DeligneAudit.DeligneFusionD1TensorGGrRelations

/-!
# Highest-vector relations in the ungraded toroidal tensor model

These are exact relations on the tensor generator. The positive `t`-mode
Cartan relation is a leading-symbol relation and is not asserted here.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

/-- All positive-root letters kill the tensor highest vector. -/
theorem eval_generator_raising (e : Fin S.n) (he : S.raising e) (i s : ℕ) :
    (d1EvalAction S.f S.jacobi hskew z).op e i s (generator S.c₀) = 0 := by
  rw [d1EvalAction_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro q _
  have hz : localOp q (D1SiteG.op S.f e i) (generator S.c₀) = 0 :=
    D1TensorG.Gr.local_generator_zero S q _ (D1SiteG.site_raising S hskew e he i)
  rw [hz, smul_zero]

/-- Positive `u`-degree Cartan letters kill the tensor highest vector. -/
theorem eval_generator_cartan_u (h : Fin S.n) (hh : S.cartan h) (i s : ℕ)
    (hi : 1 ≤ i) :
    (d1EvalAction S.f S.jacobi hskew z).op h i s (generator S.c₀) = 0 := by
  rw [d1EvalAction_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro q _
  have hz : localOp q (D1SiteG.op S.f h i) (generator S.c₀) = 0 :=
    D1TensorG.Gr.local_generator_zero S q _
      (D1SiteG.site_cartan_pos S hskew h hh i hi)
  rw [hz, smul_zero]

/-- The `u`-degree-zero Cartan eigenvalue is `N` times the site weight. -/
theorem eval_generator_cartan_zero (h : Fin S.n) (hh : S.cartan h) :
    (d1EvalAction S.f S.jacobi hskew z).op h 0 0 (generator S.c₀) =
      ((N * S.thetaH h : ℕ) : ℂ) • generator S.c₀ := by
  rw [d1EvalAction_op]
  simp only [pow_zero, one_smul, D1SiteG.op, LinearMap.sum_apply]
  simp only [D1TensorG.Gr.local_generator_smul S _ _ _
    (D1SiteG.zeroOp_cartan S h hh)]
  rw [← Finset.sum_smul]
  simp

/-- The raw Cartan `t` modes act by scalar moments of the sites. -/
theorem eval_generator_cartan_moment (h : Fin S.n) (hh : S.cartan h) (s : ℕ) :
    (d1EvalAction S.f S.jacobi hskew z).op h 0 s (generator S.c₀) =
      ((∑ q : Fin N, z q ^ s) * (S.thetaH h : ℂ)) • generator S.c₀ := by
  rw [d1EvalAction_op]
  simp only [D1SiteG.op, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [D1TensorG.Gr.local_generator_smul S _ _ _
    (D1SiteG.zeroOp_cartan S h hh), smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_mul]

/-- Positive `u`-degree negative-Cartan letters kill the generator. -/
theorem eval_generator_cartanN_u (h : Fin S.n) (hh : S.cartanN h) (i s : ℕ)
    (hi : 1 ≤ i) :
    (d1EvalAction S.f S.jacobi hskew z).op h i s (generator S.c₀) = 0 := by
  rw [d1EvalAction_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro q _
  have hz : localOp q (D1SiteG.op S.f h i) (generator S.c₀) = 0 :=
    D1TensorG.Gr.local_generator_zero S q _
      (D1SiteG.site_cartanN_pos S hskew h hh i hi)
  rw [hz, smul_zero]

theorem eval_generator_cartanN_moment (h : Fin S.n) (hh : S.cartanN h) (s : ℕ) :
    (d1EvalAction S.f S.jacobi hskew z).op h 0 s (generator S.c₀) =
      (-((∑ q : Fin N, z q ^ s) * (S.thetaN h : ℂ))) • generator S.c₀ := by
  rw [d1EvalAction_op]
  simp only [D1SiteG.op, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [D1TensorG.Gr.local_generator_smul S _ _ _
    (D1SiteG.zeroOp_cartanN S h hh), smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_mul, mul_neg]

theorem eval_generator_cartanN_zero (h : Fin S.n) (hh : S.cartanN h) :
    (d1EvalAction S.f S.jacobi hskew z).op h 0 0 (generator S.c₀) =
      -((N * S.thetaN h : ℕ) : ℂ) • generator S.c₀ := by
  simpa using eval_generator_cartanN_moment S hskew z h hh 0

/-- The `u`-degree-one non-theta fusion letters kill the generator. -/
theorem eval_generator_fusion_one (x : Fin S.n) (hx : x ≠ S.c₀) (s : ℕ) :
    (d1EvalAction S.f S.jacobi hskew z).op x 1 s (generator S.c₀) = 0 := by
  rw [d1EvalAction_op]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro q _
  have hz : localOp q (D1SiteG.op S.f x 1) (generator S.c₀) = 0 :=
    D1TensorG.Gr.local_generator_zero S q _ (D1SiteG.oneOp_w_zero S x hx)
  rw [hz, smul_zero]

/-- Every `u`-degree-two letter acts by zero on the whole tensor product. -/
theorem eval_u_two_zero (c : Fin S.n) (s : ℕ) :
    (d1EvalAction S.f S.jacobi hskew z).op c 2 s = 0 := by
  simp [d1EvalAction_op, D1SiteG.op, localOp_zero]

/-- The lowering power at `t = u = 0` has the sharp tensor exponent. -/
theorem eval_generator_lowering (x : Fin S.n) (hx : S.lowering x) :
    (((d1EvalAction S.f S.jacobi hskew z).op x 0 0) ^
      (N * S.lowExp x + 1)) (generator S.c₀) = 0 := by
  have heq : (d1EvalAction S.f S.jacobi hskew z).op x 0 0 =
      (D1TensorG.rep S.f S.jacobi hskew z).op x 0 := by
    simp [d1EvalAction_op, D1TensorG.rep, tensorRep_op, tensorOp,
      shiftRep_op, shiftOp, D1SiteG.op]
  rw [heq]
  exact D1TensorG.Gr.tensor_lowering S hskew z x hx

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.eval_generator_raising
#print axioms VOA.DeligneAudit.Toroidal.eval_generator_cartan_zero
#print axioms VOA.DeligneAudit.Toroidal.eval_generator_cartan_moment
#print axioms VOA.DeligneAudit.Toroidal.eval_generator_cartanN_moment
#print axioms VOA.DeligneAudit.Toroidal.eval_generator_cartanN_zero
#print axioms VOA.DeligneAudit.Toroidal.eval_generator_fusion_one
#print axioms VOA.DeligneAudit.Toroidal.eval_u_two_zero
#print axioms VOA.DeligneAudit.Toroidal.eval_generator_lowering
