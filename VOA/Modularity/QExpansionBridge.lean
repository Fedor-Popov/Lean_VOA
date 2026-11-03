/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LevelOneStructure
import VOA.Modularity.QEvalHolomorphic
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Residual **(c-ii)**: `G_{2j}` is a polynomial in `E₄, E₆` **as a power series**

`Modularity.LevelOneStructure` proves `zhuGC_mem_E46`: the *function* `z ↦ G_{2j}(z)` on `ℍ`
lies in the `ℂ`-subalgebra `E46 = ℂ[E₄, E₆]` of `ℍ → ℂ`.  The ODE route of residual **(c)** needs
the *formal* statement instead — that the **coefficient sequence** `zhuG j : ℕ → ℂ` lies in the
finitely generated (hence Noetherian) subring `ℂ[q-exp E₄, q-exp E₆]` of `PowerSeries ℂ`.

Passing between the two is exactly Fourier injectivity, supplied by Mathlib's
`UpperHalfPlane.qExpansion_coeff_unique`, together with multiplicativity of `qExpansion` on the
locus where the cusp function is analytic (`UpperHalfPlane.qExpansion_mul`).

## Main results

* `CuspAnalytic` — the `ℂ`-subalgebra of `ℍ → ℂ` on which `q`-expansion is well behaved;
* `qExpansionAlgHom : CuspAnalytic →ₐ[ℂ] PowerSeries ℂ` — **brick (α)**: `q`-expansion carries
  pointwise multiplication of functions to the Cauchy product of coefficient sequences;
* `qExpansion_zhuGC` — **brick (α′)**: `zhuG j` *is* the `q`-expansion coefficient sequence of
  `zhuGC j`, for `j ≥ 2`;
* `mk_zhuG_mem_adjoin` — **(c-ii)**: `PowerSeries.mk (zhuG j) ∈ ℂ[qExpansion E₄, qExpansion E₆]`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open UpperHalfPlane ModularForm

open scoped MatrixGroups Real

local notation "𝕢" => Function.Periodic.qParam

/-! ## Level one has strict period `1` -/

/-- Every level-one modular form has an analytic cusp function at `q = 0`, for the
period `h = 1`. -/
theorem analyticAt_cuspFunction_modularForm {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    AnalyticAt ℂ (cuspFunction 1 (⇑F : UpperHalfPlane → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero F one_pos
    (by rw [Subgroup.strictPeriods_SL2Z]; exact AddSubgroup.mem_zmultiples 1)

/-- The cusp function of the constant function `1`. -/
theorem cuspFunction_one_eq (h : ℝ) : cuspFunction h (1 : UpperHalfPlane → ℂ) = 1 := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simpa [cuspFunction, Function.Periodic.cuspFunction] using tendsto_const_nhds.limUnder_eq
  · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero h _ hq]

/-- The cusp function of the constant function `0`. -/
theorem cuspFunction_zero_eq (h : ℝ) : cuspFunction h (0 : UpperHalfPlane → ℂ) = 0 := by
  simpa [cuspFunction, Function.Periodic.cuspFunction]
    using (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq

/-! ## The subalgebra on which `q`-expansion is multiplicative -/

/-- The `ℂ`-subalgebra of `ℍ → ℂ` consisting of the functions whose cusp function (for the
period `h = 1`) is analytic at `q = 0`. -/
noncomputable def CuspAnalytic : Subalgebra ℂ (UpperHalfPlane → ℂ) where
  carrier := {f : UpperHalfPlane → ℂ | AnalyticAt ℂ (cuspFunction 1 f) 0}
  mul_mem' := fun {f g} hf hg => by
    change AnalyticAt ℂ (cuspFunction 1 (f * g)) 0
    rw [cuspFunction_mul hf.continuousAt hg.continuousAt]
    exact hf.mul hg
  one_mem' := by
    change AnalyticAt ℂ (cuspFunction 1 (1 : UpperHalfPlane → ℂ)) 0
    rw [cuspFunction_one_eq]
    exact analyticAt_const
  add_mem' := fun {f g} hf hg => by
    change AnalyticAt ℂ (cuspFunction 1 (f + g)) 0
    rw [cuspFunction_add hf.continuousAt hg.continuousAt]
    exact hf.add hg
  zero_mem' := by
    change AnalyticAt ℂ (cuspFunction 1 (0 : UpperHalfPlane → ℂ)) 0
    rw [cuspFunction_zero_eq]
    exact analyticAt_const
  algebraMap_mem' := fun r => by
    change AnalyticAt ℂ (cuspFunction 1 (algebraMap ℂ (UpperHalfPlane → ℂ) r)) 0
    have h1 : (algebraMap ℂ (UpperHalfPlane → ℂ) r) = r • (1 : UpperHalfPlane → ℂ) :=
      Algebra.algebraMap_eq_smul_one r
    have h2 : (r • (1 : ℂ → ℂ)) = fun _ : ℂ => r := by funext z; simp
    rw [h1, cuspFunction_smul (by rw [cuspFunction_one_eq]; exact continuousAt_const),
      cuspFunction_one_eq, h2]
    exact analyticAt_const

@[simp] theorem mem_cuspAnalytic {f : UpperHalfPlane → ℂ} :
    f ∈ CuspAnalytic ↔ AnalyticAt ℂ (cuspFunction 1 f) 0 := Iff.rfl

/-- **Brick (α)**: on `CuspAnalytic`, taking `q`-expansions is a `ℂ`-algebra homomorphism to
`PowerSeries ℂ` — pointwise multiplication of functions on `ℍ` goes to the Cauchy product
(equivalently, to `qConv`) of coefficient sequences. -/
noncomputable def qExpansionAlgHom : CuspAnalytic →ₐ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 (f : UpperHalfPlane → ℂ)
  map_one' := qExpansion_one 1
  map_mul' f g := qExpansion_mul f.2 g.2
  map_zero' := qExpansion_zero 1
  map_add' f g := qExpansion_add f.2 g.2
  commutes' r := by
    show qExpansion 1 ((algebraMap ℂ CuspAnalytic r : CuspAnalytic) : UpperHalfPlane → ℂ) = _
    have h1 : ((algebraMap ℂ CuspAnalytic r : CuspAnalytic) : UpperHalfPlane → ℂ)
        = r • (1 : UpperHalfPlane → ℂ) := by
      rw [← Algebra.algebraMap_eq_smul_one]; rfl
    rw [h1, qExpansion_smul (by rw [cuspFunction_one_eq]; exact analyticAt_const),
      qExpansion_one, Algebra.algebraMap_eq_smul_one]

@[simp] theorem qExpansionAlgHom_apply (f : CuspAnalytic) :
    qExpansionAlgHom f = qExpansion 1 (f : UpperHalfPlane → ℂ) := rfl

/-! ## `E46` lands in `CuspAnalytic`, and its image is a finitely generated subring -/

theorem E46_le_cuspAnalytic : E46 ≤ CuspAnalytic := by
  rw [E46, Algebra.adjoin_le_iff]
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · exact analyticAt_cuspFunction_modularForm ModularForm.E₄
  · exact analyticAt_cuspFunction_modularForm ModularForm.E₆

/-- The image of `E46` under `q`-expansion: the subring of `PowerSeries ℂ` generated by the
`q`-expansions of `E₄` and `E₆`. -/
noncomputable def E46Series : Subalgebra ℂ (PowerSeries ℂ) :=
  Algebra.adjoin ℂ ({qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ),
    qExpansion 1 (⇑ModularForm.E₆ : UpperHalfPlane → ℂ)} : Set (PowerSeries ℂ))

/-- The `q`-expansion of a polynomial in `E₄, E₆` is a polynomial in their `q`-expansions. -/
theorem qExpansion_mem_E46Series {f : UpperHalfPlane → ℂ} (hf : f ∈ E46) :
    qExpansion 1 f ∈ E46Series := by
  have key : ∀ g ∈ E46, AnalyticAt ℂ (cuspFunction 1 g) 0 ∧ qExpansion 1 g ∈ E46Series := by
    intro g hg
    rw [E46] at hg
    refine Algebra.adjoin_induction
      (p := fun g _ => AnalyticAt ℂ (cuspFunction 1 g) 0 ∧ qExpansion 1 g ∈ E46Series)
      ?_ ?_ ?_ ?_ hg
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨analyticAt_cuspFunction_modularForm ModularForm.E₄,
          Algebra.subset_adjoin (by simp)⟩
      · exact ⟨analyticAt_cuspFunction_modularForm ModularForm.E₆,
          Algebra.subset_adjoin (by simp)⟩
    · intro r
      refine ⟨CuspAnalytic.algebraMap_mem r, ?_⟩
      have h1 : (algebraMap ℂ (UpperHalfPlane → ℂ) r) = r • (1 : UpperHalfPlane → ℂ) :=
        Algebra.algebraMap_eq_smul_one r
      rw [h1, qExpansion_smul (by rw [cuspFunction_one_eq]; exact analyticAt_const),
        qExpansion_one, ← Algebra.algebraMap_eq_smul_one]
      exact E46Series.algebraMap_mem r
    · rintro x y - - ⟨hxa, hxq⟩ ⟨hya, hyq⟩
      refine ⟨CuspAnalytic.add_mem hxa hya, ?_⟩
      rw [qExpansion_add hxa hya]
      exact E46Series.add_mem hxq hyq
    · rintro x y - - ⟨hxa, hxq⟩ ⟨hya, hyq⟩
      refine ⟨CuspAnalytic.mul_mem hxa hya, ?_⟩
      rw [qExpansion_mul hxa hya]
      exact E46Series.mul_mem hxq hyq
  exact (key f hf).2

/-! ## Brick (α′): `zhuG j` **is** the `q`-expansion of `zhuGC j` -/

/-- `G_{2j}` as a function on `ℍ` is the scalar multiple `G_{2j}(∞)·E_{2j}` of Mathlib's
normalised Eisenstein form. -/
theorem zhuGC_fun_eq_smul_E {j : ℕ} (hj : 2 ≤ j) :
    (fun z : UpperHalfPlane => zhuGC j (z : ℂ))
      = zhuG j 0 • (⇑(ModularForm.E (show 3 ≤ 2 * j by omega)) : UpperHalfPlane → ℂ) := by
  funext z
  rw [zhuGC_eq_mul_E hj (coe_mem_imGT_zero z)]
  rfl

/-- Mathlib's `q`-parameter at period `1` is the repo's `qC`. -/
theorem qParam_one_eq_qC (z : ℂ) : 𝕢 1 z = qC z := by
  rw [Function.Periodic.qParam, qC, Complex.ofReal_one, div_one]

/-- The Eisenstein `q`-series converges to `G_{2j}` in Mathlib's `𝕢 1` parameter. -/
theorem hasSum_zhuG (j : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => zhuG j m • 𝕢 1 (τ : ℂ) ^ m) (zhuGC j (τ : ℂ)) := by
  have hq : ∀ n : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (τ : ℂ))
      = 𝕢 1 (τ : ℂ) ^ n := fun n => by rw [qexp_eq_qC_pow, qParam_one_eq_qC]
  have hfun : (fun m : ℕ => zhuG j m • 𝕢 1 (τ : ℂ) ^ m)
      = fun m : ℕ => zhuG j m
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ : ℂ)) := by
    funext m
    rw [hq m, smul_eq_mul]
  rw [hfun, zhuGC]
  exact (summable_zhuG_qexp j (coe_mem_imGT_zero τ)).hasSum

/-- The constant term of `G_{2j}` is nonzero: `−B_{2j}/(2j)! ≠ 0`. -/
theorem zhuG_zero_ne_zero {j : ℕ} (hj : j ≠ 0) : zhuG j 0 ≠ 0 := by
  rw [zhuG_zero, neg_ne_zero, div_ne_zero_iff]
  exact ⟨bernoulli_two_mul_ne_zero hj,
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * j))⟩

/-- The normalised Eisenstein form `E_{2j}` has `q`-expansion coefficients
`zhuG j m / zhuG j 0`. -/
theorem coeff_qExpansion_E {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    (qExpansion 1 (⇑(ModularForm.E (show 3 ≤ 2 * j by omega)) : UpperHalfPlane → ℂ)).coeff m
      = zhuG j m / zhuG j 0 := by
  have hc : zhuG j 0 ≠ 0 := zhuG_zero_ne_zero (by omega)
  have hEsum : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => (zhuG j m / zhuG j 0) • 𝕢 1 (τ : ℂ) ^ m)
        (ModularForm.E (show 3 ≤ 2 * j by omega) τ) := by
    intro τ
    have h1 := (hasSum_zhuG j τ).div_const (zhuG j 0)
    have h2 : (fun m : ℕ => (zhuG j m • 𝕢 1 (τ : ℂ) ^ m) / zhuG j 0)
        = fun m : ℕ => (zhuG j m / zhuG j 0) • 𝕢 1 (τ : ℂ) ^ m := by
      funext m
      simp only [smul_eq_mul]
      ring
    rw [h2] at h1
    have hz : zhuGC j (τ : ℂ)
        = zhuG j 0 * ModularForm.E (show 3 ≤ 2 * j by omega) τ :=
      zhuGC_eq_mul_E hj (coe_mem_imGT_zero τ)
    rwa [hz, mul_div_cancel_left₀ _ hc] at h1
  exact (ModularFormClass.qExpansion_coeff_unique (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)))
    (by norm_num : (0 : ℝ) < 1)
    (by rw [Subgroup.strictPeriods_SL2Z]; exact AddSubgroup.mem_zmultiples 1) hEsum m).symm

/-- **Brick (α′)**: for `j ≥ 2` the sequence `zhuG j : ℕ → ℂ` *is* the `q`-expansion coefficient
sequence of the analytic Eisenstein function `zhuGC j`. -/
theorem qExpansion_zhuGC {j : ℕ} (hj : 2 ≤ j) :
    qExpansion 1 (fun z : UpperHalfPlane => zhuGC j (z : ℂ)) = PowerSeries.mk (zhuG j) := by
  have hc : zhuG j 0 ≠ 0 := zhuG_zero_ne_zero (by omega)
  have hE := analyticAt_cuspFunction_modularForm (ModularForm.E (show 3 ≤ 2 * j by omega))
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_mk, zhuGC_fun_eq_smul_E hj, qExpansion_smul hE (zhuG j 0),
    map_smul, coeff_qExpansion_E hj m, smul_eq_mul, mul_comm, div_mul_cancel₀ _ hc]

/-! ## (c-ii) -/

/-- **Residual (c-ii)**: for `j ≥ 2` the Eisenstein coefficient sequence `zhuG j`, read as a
formal power series, lies in the finitely generated — hence **Noetherian** — subring
`ℂ[q-exp E₄, q-exp E₆]` of `PowerSeries ℂ`. -/
theorem mk_zhuG_mem_E46Series {j : ℕ} (hj : 2 ≤ j) :
    PowerSeries.mk (zhuG j) ∈ E46Series := by
  rw [← qExpansion_zhuGC hj]
  exact qExpansion_mem_E46Series (zhuGC_mem_E46 hj)

/-! ## The Noetherian coefficient ring -/

theorem finiteType_E46Series : Algebra.FiniteType ℂ E46Series := by
  rw [E46Series]
  exact Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)

/-- The coefficient ring is **Noetherian** — a finitely generated `ℂ`-algebra, by Hilbert's
basis theorem.  This is what the ODE route of residual **(c)** needs, and what the
subexponential-domain route could *not* supply. -/
theorem isNoetherianRing_E46Series : IsNoetherianRing E46Series :=
  haveI := finiteType_E46Series
  Algebra.FiniteType.isNoetherianRing ℂ E46Series

/-! ## The same statement in Zhu's own generators `G₂, G₄, G₆` -/

/-- The subring of `PowerSeries ℂ` generated by Zhu's `G₂, G₄, G₆`. -/
noncomputable def GSeries : Subalgebra ℂ (PowerSeries ℂ) :=
  Algebra.adjoin ℂ ({PowerSeries.mk (zhuG 1), PowerSeries.mk (zhuG 2),
    PowerSeries.mk (zhuG 3)} : Set (PowerSeries ℂ))

theorem qExpansion_E4_eq :
    qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ)
      = (zhuG 2 0)⁻¹ • PowerSeries.mk (zhuG 2) := by
  have hE : (⇑ModularForm.E₄ : UpperHalfPlane → ℂ)
      = ⇑(ModularForm.E (show 3 ≤ 2 * 2 by omega)) := rfl
  refine PowerSeries.ext fun m => ?_
  rw [hE, coeff_qExpansion_E (j := 2) le_rfl m, map_smul, PowerSeries.coeff_mk, smul_eq_mul,
    ← div_eq_inv_mul]

theorem qExpansion_E6_eq :
    qExpansion 1 (⇑ModularForm.E₆ : UpperHalfPlane → ℂ)
      = (zhuG 3 0)⁻¹ • PowerSeries.mk (zhuG 3) := by
  have hE : (⇑ModularForm.E₆ : UpperHalfPlane → ℂ)
      = ⇑(ModularForm.E (show 3 ≤ 2 * 3 by omega)) := rfl
  refine PowerSeries.ext fun m => ?_
  rw [hE, coeff_qExpansion_E (j := 3) (by omega) m, map_smul, PowerSeries.coeff_mk, smul_eq_mul,
    ← div_eq_inv_mul]

theorem E46Series_le_GSeries : E46Series ≤ GSeries := by
  rw [E46Series, Algebra.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [qExpansion_E4_eq]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (by simp)) _
  · rw [qExpansion_E6_eq]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (by simp)) _

/-- **Residual (c-ii), in Zhu's own generators**: for every `j ≥ 1` the Eisenstein coefficient
sequence `zhuG j`, read as a formal power series, lies in `ℂ[G₂, G₄, G₆] ⊆ PowerSeries ℂ`. -/
theorem mk_zhuG_mem_GSeries {j : ℕ} (hj : 1 ≤ j) :
    PowerSeries.mk (zhuG j) ∈ GSeries := by
  rcases eq_or_lt_of_le hj with h1 | h2
  · rw [← h1]
    exact Algebra.subset_adjoin (by simp)
  · exact E46Series_le_GSeries (mk_zhuG_mem_E46Series (by omega))

theorem finiteType_GSeries : Algebra.FiniteType ℂ GSeries := by
  rw [GSeries]
  exact Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)

/-- `ℂ[G₂, G₄, G₆]` is a **Noetherian** subring of `PowerSeries ℂ` containing every `G_{2j}`. -/
theorem isNoetherianRing_GSeries : IsNoetherianRing GSeries :=
  haveI := finiteType_GSeries
  Algebra.FiniteType.isNoetherianRing ℂ GSeries

end VOA
