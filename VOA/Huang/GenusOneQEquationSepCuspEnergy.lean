import VOA.Huang.GenusTwoPointSepCuspKernels

/-!
# Energy insertion and the descendant form of the mixed Ward identity

The energy moment is identified with the formal Euler derivative of the actual
spatially evaluated trace. The remaining mixed Ward identity is kept explicit.
Its spatial terms are ordinary L(-1) insertion states, hence are already in
the pair span. No differentiation of an infinite spatial sum is used.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation FuchsianODE
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- An actual spatial summand with L(0)-c/24 inserted on the traced module. -/
def productEnergyTerm
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ β z₁ z₂ : ℂ) (k : ℕ) : ℂ :=
  let n₁ := (α₁ + α₂ - 2) - (α₂ + β - 1 - Q.h) + k
  let n₂ := (α₂ + β - 1 - Q.h) - k
  gradedTraceOp N.isMod (traceEnergy N.isMod * ((Y₁.val n₁ x).comp (Y₂.val n₂ y)))
      (β - W.centralCharge / 24) * z₁ ^ (-n₁ - 1) * z₂ ^ (-n₂ - 1)

theorem productEnergyTerm_eq
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ β z₁ z₂ : ℂ) (k : ℕ) :
    productEnergyTerm Y₁ Y₂ x y α₁ α₂ β z₁ z₂ k =
      (β - W.centralCharge / 24) * productTerm Y₁ Y₂ x y α₁ α₂ β z₁ z₂ k := by
  dsimp only [productEnergyTerm, productTerm, productModeTrace]
  rw [gradedTraceOp_traceEnergy]
  simp only [qDeriv]
  ring

/-- Energy insertion preserves the certified spatial summability at each grade. -/
theorem summable_productEnergyTerm (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (β : ℂ) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    Summable (productEnergyTerm Y₁ Y₂ x y α₁ α₂ β z₁ z₂) := by
  exact ((summable_productTerm hV i₁ i₂ iN Y₁ Y₂ hx hy β hz₂ hz).mul_left
    (β - W.centralCharge / 24)).congr (fun k =>
      (productEnergyTerm_eq Y₁ Y₂ x y α₁ α₂ β z₁ z₂ k).symm)

/-- The Euler derivative is the convergent trace of the actual energy insertion,
coefficient by coefficient. No outer q-convergence is assumed. -/
theorem coeff_theta_productCuspSeries_energy (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) (n : ℕ) :
    PowerSeries.coeff n (thetaShift (N.h - W.centralCharge / 24)
      (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y)) =
      rho ^ n * ∑' k, productEnergyTerm Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ k := by
  simp only [coeff_thetaShift, coeff_productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hx hy,
    productEnergyTerm_eq, tsum_mul_left, productCoeff]
  ring

/-- Energy on the bilinear extension is the same grade scalar as on each
homogeneous summand. The modified vectors are actual finite module vectors. -/
theorem coeff_theta_modifiedProductCuspSeries (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (x : P₁.carrier) (y : P₂.carrier) (n : ℕ) :
    PowerSeries.coeff n (thetaShift (N.h - W.centralCharge / 24)
      (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y)) =
      rho ^ n * ((N.h + n - W.centralCharge / 24) *
        productCoeffPair hV i₁ i₂ iN Y₁ Y₂ (N.h + n) hz₂ hz
          (huangU P₁ (Complex.log z₁) x) (huangU P₂ (Complex.log z₂) y)) := by
  simp only [coeff_thetaShift, modifiedProductCuspSeries, LinearMap.compl₂_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, productCuspSeries,
    coeff_bilinearSeries, LinearMap.smul_apply, smul_eq_mul]
  ring

section Mixed
variable {E F : Type u} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

/-- The right side of the omega Ward identity with all descendants explicit.
Here G k is G_(2k+4), Pleft m is wp_(m+2). -/
def mixedEnergyDescendants (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : WeakModule W E) (B : WeakModule W F) (c : Kernels R)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (x : E) (y : F) (K : ℕ) : PowerSeries ℂ :=
  S (mode (A.YM W.conformalVector) (-1) x) y -
    (∑ k ∈ Finset.range K, c.G k •
      S (mode (A.YM W.conformalVector) (2 * (k + 1) + 1) x) y) +
    ∑ m ∈ Finset.range K, ((-1 : R) ^ (m + 1) * c.Pleft m) •
      S x (mode (B.YM W.conformalVector) (m + 1) y)

/-- All mixed spatial/weight corrections already lie in the insertion span. -/
def mixedEnergyCorrection (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : WeakModule W E) (B : WeakModule W F) (g₂ p₁ : R) (t₁ t₂ : ℂ)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (x : E) (y : F) : PowerSeries ℂ :=
  g₂ • (S (mode (A.YM W.conformalVector) 1 x) y +
    S x (mode (B.YM W.conformalVector) 1 y) +
    t₁ • S (mode (A.YM W.conformalVector) 0 x) y +
    t₂ • S x (mode (B.YM W.conformalVector) 0 y)) -
  p₁ • S x (mode (B.YM W.conformalVector) 0 y)

theorem mixedEnergyDescendants_mem (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : WeakModule W E) (B : WeakModule W F) (c : Kernels R)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (x : E) (y : F) (K : ℕ) :
    mixedEnergyDescendants R A B c S x y K ∈ pairSeriesSpan R S := by
  have hv (v : E) (w : F) : S v w ∈ pairSeriesSpan R S :=
    Submodule.subset_span ⟨(v, w), rfl⟩
  exact Submodule.add_mem _
    (Submodule.sub_mem _ (hv _ _) (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (hv _ _)))
    (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hv _ _))

theorem mixedEnergyCorrection_mem (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : WeakModule W E) (B : WeakModule W F) (g₂ p₁ : R) (t₁ t₂ : ℂ)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (x : E) (y : F) :
    mixedEnergyCorrection R A B g₂ p₁ t₁ t₂ S x y ∈ pairSeriesSpan R S := by
  have hv (v : E) (w : F) : S v w ∈ pairSeriesSpan R S :=
    Submodule.subset_span ⟨(v, w), rfl⟩
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _
    (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (hv _ _) (hv _ _))
      (Submodule.smul_of_tower_mem _ t₁ (hv _ _)))
      (Submodule.smul_of_tower_mem _ t₂ (hv _ _)))) (Submodule.smul_mem _ _ (hv _ _))

/-- Descendant form of Huang's mixed omega identity. For an actual trace this
is the remaining Ward law, not a formal consequence of the commutator alone. -/
def MixedPairWard (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : WeakModule W E) (B : WeakModule W F) (c : Kernels R)
    (g₂ p₁ : R) (t₁ t₂ lam : ℂ) (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) : Prop :=
  ∀ x y, ∃ K, TailBound A B W.conformalVector x y K ∧
    (2 * (Real.pi : ℂ) * Complex.I) ^ 2 • thetaShift lam (S x y) +
      mixedEnergyCorrection R A B g₂ p₁ t₁ t₂ S x y =
        mixedEnergyDescendants R A B c S x y K

/-- The L(-1)-state trick removes every mixed spatial term from the remaining
closure problem. No derivative stability of a smaller coefficient ring is used. -/
theorem pairEulerClosed_of_mixedPairWard (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : WeakModule W E) (B : WeakModule W F) (c : Kernels R)
    (g₂ p₁ : R) (t₁ t₂ lam : ℂ) (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ)
    (h : MixedPairWard R A B c g₂ p₁ t₁ t₂ lam S) : PairEulerClosed R S lam := by
  intro x y
  obtain ⟨K, _, he⟩ := h x y
  have hm : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 • thetaShift lam (S x y) ∈
      pairSeriesSpan R S := by
    rw [eq_sub_iff_add_eq.mpr he]
    exact Submodule.sub_mem _ (mixedEnergyDescendants_mem R A B c S x y K)
      (mixedEnergyCorrection_mem R A B g₂ p₁ t₁ t₂ S x y)
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  have hi := (pairSeriesSpan R S).smul_of_tower_mem
    (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹) hm
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

end Mixed
end VOA.Huang.GenusTwoPoint.Separate
