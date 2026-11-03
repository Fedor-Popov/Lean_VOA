import VOA.Huang.GenusOneQEquationSepPairSystem

/-!
# Scalar regular q-equations from a differential coefficient ring

The matrix route does not need a Noetherian coefficient ring. Scalar elimination
is available if the chosen ring is Noetherian and stable under the Euler
coefficient derivation. These conditions are explicit: they are not asserted
for Huang's four-generator ring with the pure q derivative.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation FuchsianODE
open scoped BigOperators

theorem thetaShift_eq_theta (lam : ℂ) (f : PowerSeries ℂ) :
    thetaShift lam f = VOA.theta f + PowerSeries.C lam * f := by
  ext n
  simp only [coeff_thetaShift, map_add, theta_coeff, PowerSeries.coeff_C_mul]
  ring

/-- The coefficient derivative must be retained when differentiating a
coefficient-ring combination of insertion values. -/
theorem thetaShift_mul (lam : ℂ) (a f : PowerSeries ℂ) :
    thetaShift lam (a * f) = thetaShift 0 a * f + a * thetaShift lam f := by
  simp only [thetaShift_eq_theta, VOA.theta_mul, map_zero, zero_mul, add_zero]
  ring

/-- Derivative closure on generators extends to the whole span only when
the coefficient ring is itself stable under the coefficient derivative. -/
theorem pairSeriesSpan_euler_closed {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (R : Subalgebra ℂ (PowerSeries ℂ))
    (hR : ∀ a : R, thetaShift 0 a.val ∈ R)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (lam : ℂ)
    (hD : PairEulerClosed R S lam) :
    ∀ f ∈ pairSeriesSpan R S, thetaShift lam f ∈ pairSeriesSpan R S := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨x, y⟩, rfl⟩ := hf
    exact hD x y
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using (pairSeriesSpan R S).add_mem hf hg
  | smul a f hf ih =>
    rw [Algebra.smul_def, Subalgebra.algebraMap_eq, thetaShift_mul]
    exact (pairSeriesSpan R S).add_mem
      ((pairSeriesSpan R S).smul_mem (⟨thetaShift 0 a.val, hR a⟩ : R) hf)
      ((pairSeriesSpan R S).smul_mem a ih)

universe u
variable {V E F : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  {W : VertexOperatorAlgebra V}

/-- The Noetherian orbit argument gives a positive-order scalar q-ODE for
any two-insertion family satisfying the algebraic Ward consequences. -/
theorem exists_pair_fuchsianEq (R : Subalgebra ℂ (PowerSeries ℂ)) [IsNoetherianRing R]
    (hR : ∀ a : R, thetaShift 0 a.val ∈ R)
    (A : AdmissibleModule W E) (B : AdmissibleModule W F)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (lam : ℂ)
    (hS : C2Reduction (R := R) A.toWeakModule B.toWeakModule S)
    (hD : PairEulerClosed R S lam) (x : E) (y : F) :
    ∃ (m : ℕ) (a : ℕ → R), 0 < m ∧
      FuchsianEq lam m (fun k => (a k).val) (S x y) := by
  classical
  let T := pairSeriesSpan R S
  letI : Module.Finite R T := Module.Finite.of_fg (pairSeriesSpan_fg R A B hA hB S hS)
  have hi (n : ℕ) : (thetaShift lam)^[n] (S x y) ∈ T := by
    induction n with
    | zero => exact Submodule.subset_span ⟨(x, y), rfl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact pairSeriesSpan_euler_closed R hR S lam hD _ ih
  let t (n : ℕ) : T := ⟨(thetaShift lam)^[n] (S x y), hi n⟩
  obtain ⟨m, a, ha⟩ := MatrixCoeffODE.exists_monic_relation (R := R) (fun k => t (k + 1))
  let b : ℕ → R := fun k => if k = 0 then 0 else a (k - 1)
  have hb : (∑ k ∈ Finset.range (m + 1), b k • t k) =
      ∑ k ∈ Finset.range m, a k • t (k + 1) := by
    rw [Finset.sum_range_succ']
    simp [b]
  have heq := congrArg (fun z : T => (z : PowerSeries ℂ)) (ha.trans hb.symm)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def,
    Subalgebra.algebraMap_eq] at heq
  change (thetaShift lam)^[m + 1] (S x y) =
    ∑ k ∈ Finset.range (m + 1), (b k).val * (thetaShift lam)^[k] (S x y) at heq
  refine ⟨m + 1, fun k => -b k, by omega, ?_⟩
  change (thetaShift lam)^[m + 1] (S x y) +
    ∑ k ∈ Finset.range (m + 1), (-b k).val * (thetaShift lam)^[k] (S x y) = 0
  simp only [Subalgebra.coe_neg, neg_mul, Finset.sum_neg_distrib, ← heq, add_neg_cancel]

/-- The scalar q-equation feeds the existing Fuchsian theorem directly. -/
theorem summable_pairSeries_of_noetherian (R : Subalgebra ℂ (PowerSeries ℂ))
    [IsNoetherianRing R] (hreg : R ≤ SubexpPS)
    (hR : ∀ a : R, thetaShift 0 a.val ∈ R)
    (A : AdmissibleModule W E) (B : AdmissibleModule W F)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (lam : ℂ)
    (hS : C2Reduction (R := R) A.toWeakModule B.toWeakModule S)
    (hD : PairEulerClosed R S lam) (x : E) (y : F) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖PowerSeries.coeff n (S x y) * q ^ n‖) := by
  obtain ⟨m, a, _, heq⟩ := exists_pair_fuchsianEq R hR A B hA hB S lam hS hD x y
  exact summable_of_fuchsianEq (fun k _ => hreg (a k).property) heq hq

end VOA.Huang.GenusTwoPoint.Separate
