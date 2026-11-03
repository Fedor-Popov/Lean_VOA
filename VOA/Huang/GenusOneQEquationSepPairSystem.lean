import VOA.Huang.GenusTwoPointC2Reduction
import VOA.Huang.FuchsianODE

/-!
# Two-insertion finite Euler systems after spatial evaluation

C₂ reduction is used on both insertion slots. The q derivative is required to
lie in the span of insertion values, not to act diagonally on an unsummed
intermediate-level array. The resulting finite first-order system is regular
at the cusp. Its convergence uses the same matrix theorem as the one-point
proof. No bound on the intermediate-level sum is assumed.

The two Ward obligations below are hypotheses, not assertions about all traces.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation FuchsianODE
open scoped BigOperators

/-- The coefficient-ring span of a bilinear family of formal q-series. -/
def pairSeriesSpan {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (R : Subalgebra ℂ (PowerSeries ℂ))
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) : Submodule R (PowerSeries ℂ) :=
  Submodule.span R (Set.range fun p : E × F => S p.1 p.2)

/-- Energy Ward closure on insertion values. It includes the entire evaluated
q derivative; spatial terms must be expressed by insertion descendants before
using this predicate. No analytic growth is part of the predicate. -/
def PairEulerClosed {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (R : Subalgebra ℂ (PowerSeries ℂ))
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (lam : ℂ) : Prop :=
  ∀ x y, thetaShift lam (S x y) ∈ pairSeriesSpan R S

/-- Matrix regular-singular convergence, with an arbitrary finite index type. -/
theorem series_mem_subexp_of_euler_system {ι : Type*} [Fintype ι]
    (R : Subalgebra ℂ (PowerSeries ℂ)) (hR : R ≤ SubexpPS)
    (lam : ℂ) (f : ι → PowerSeries ℂ) (B : ι → ι → R)
    (hsys : ∀ i, thetaShift lam (f i) = ∑ j, (B i j).val * f j) :
    ∀ i, f i ∈ SubexpPS := by
  classical
  let e := Fintype.equivFin ι
  have hs := subexponential_of_system
    (hbase := lam)
    (fun k n => PowerSeries.coeff n (f (e.symm k)))
    (fun k l n => PowerSeries.coeff n (B (e.symm k) (e.symm l)).val)
    (fun k l => hR (B (e.symm k) (e.symm l)).property) (by
      intro k n
      have h := congrArg (PowerSeries.coeff n) (hsys (e.symm k))
      rw [coeff_thetaShift, map_sum] at h
      simp only [coeff_mul_range] at h
      rw [h]
      exact (e.symm.sum_comp _).symm)
  intro i
  simpa only [Equiv.symm_apply_apply] using hs (e i)

universe u
variable {V E F : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  {W : VertexOperatorAlgebra V}

/-- C₂ complements generate the two-point q-series span. -/
theorem pairSeriesSpan_fg (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : AdmissibleModule W E) (B : AdmissibleModule W F)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ)
    (hS : C2Reduction (R := R) A.toWeakModule B.toWeakModule S) :
    (pairSeriesSpan R S).FG := by
  classical
  obtain ⟨U, Z, hUZ⟩ := exists_generators_of_C2 (R := R) (E := PowerSeries ℂ) A B hA hB
  have heq : pairSeriesSpan R S =
      Submodule.span R (Set.range fun k : U × Z => S k.1.val k.2.val) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨x, y⟩, rfl⟩
      obtain ⟨c, hc⟩ := hUZ S hS x y
      dsimp only
      rw [hc]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · apply Submodule.span_mono
      rintro _ ⟨k, rfl⟩
      exact ⟨(k.1.val, k.2.val), rfl⟩
  rw [heq]
  exact Submodule.fg_span (Set.finite_range _)

/-- A genuine first-order formal q-ODE system on finitely many insertion
values. The generators are chosen using C₂ before the bilinear trace map. -/
theorem exists_pair_euler_system (R : Subalgebra ℂ (PowerSeries ℂ))
    (A : AdmissibleModule W E) (B : AdmissibleModule W F)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule) :
    ∃ (U : Finset E) (Z : Finset F),
      ∀ (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (lam : ℂ),
        C2Reduction (R := R) A.toWeakModule B.toWeakModule S →
        PairEulerClosed R S lam →
        ∃ C : U × Z → U × Z → R,
          (∀ k, thetaShift lam (S k.1.val k.2.val) =
            ∑ l : U × Z, (C k l).val * S l.1.val l.2.val) ∧
          (∀ x y, ∃ c : U × Z → R,
            S x y = ∑ l : U × Z, (c l).val * S l.1.val l.2.val) := by
  classical
  obtain ⟨U, Z, hUZ⟩ := exists_generators_of_C2 (R := R) (E := PowerSeries ℂ) A B hA hB
  refine ⟨U, Z, fun S lam hS hD => ?_⟩
  let T := Submodule.span R (Set.range fun k : U × Z => S k.1.val k.2.val)
  have hspan : pairSeriesSpan R S ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    obtain ⟨c, hc⟩ := hUZ S hS x y
    dsimp only
    rw [hc]
    exact T.sum_mem fun k _ => T.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hsys : ∀ k : U × Z, ∃ c : U × Z → R,
      thetaShift lam (S k.1.val k.2.val) =
        ∑ l : U × Z, c l • S l.1.val l.2.val := by
    intro k
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
      (hspan (hD k.1.val k.2.val))
    exact ⟨c, hc.symm⟩
  choose C hC using hsys
  refine ⟨C, ?_, ?_⟩
  · intro k
    simpa only [Algebra.smul_def, Subalgebra.algebraMap_eq] using hC k
  · intro x y
    obtain ⟨c, hc⟩ := hUZ S hS x y
    exact ⟨c, by simpa only [Algebra.smul_def, Subalgebra.algebraMap_eq] using hc⟩

/-- Two-insertion counterpart of the one-point finite-system convergence
argument. The two Ward hypotheses are retained explicitly. -/
theorem pairSeries_mem_subexp_of_C2 (R : Subalgebra ℂ (PowerSeries ℂ))
    (hR : R ≤ SubexpPS) (A : AdmissibleModule W E) (B : AdmissibleModule W F)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (lam : ℂ)
    (hS : C2Reduction (R := R) A.toWeakModule B.toWeakModule S)
    (hD : PairEulerClosed R S lam) (x : E) (y : F) : S x y ∈ SubexpPS := by
  classical
  obtain ⟨U, Z, hUZ⟩ := exists_pair_euler_system R A B hA hB
  obtain ⟨C, hC, hgen⟩ := hUZ S lam hS hD
  have hs := series_mem_subexp_of_euler_system R hR lam
    (fun k : U × Z => S k.1.val k.2.val) C hC
  obtain ⟨c, hc⟩ := hgen x y
  rw [hc]
  exact SubexpPS.sum_mem fun k _ => SubexpPS.mul_mem (hR (c k).property) (hs k)

/-- Absolute q-convergence on the disc of the rescaled coefficient ring. -/
theorem summable_pairSeries_of_C2 (R : Subalgebra ℂ (PowerSeries ℂ))
    (hR : R ≤ SubexpPS) (A : AdmissibleModule W E) (B : AdmissibleModule W F)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule)
    (S : E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ) (lam : ℂ)
    (hS : C2Reduction (R := R) A.toWeakModule B.toWeakModule S)
    (hD : PairEulerClosed R S lam) (x : E) (y : F) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖PowerSeries.coeff n (S x y) * q ^ n‖) := by
  have hs := summable_of_subexponential (fun n => norm_nonneg (PowerSeries.coeff n (S x y)))
    (pairSeries_mem_subexp_of_C2 R hR A B hA hB S lam hS hD x y) (norm_nonneg q) hq
  simpa only [norm_mul, norm_pow] using hs

end VOA.Huang.GenusTwoPoint.Separate
