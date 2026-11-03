/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.ForMathlib.PoissonSummation

/-!
# Poisson summation over a shifted lattice

`ZLattice.poissonSummation` sums a function over a lattice `Γ`.  The theta series with
*characteristics* — the ones a lattice of level `N > 1` needs — are sums over a **coset**
`μ + Γ`, and Poisson summation there acquires a character:

`∑_{x ∈ Γ} f (x + μ) = (covol Γ)⁻¹ ∑_{y ∈ Γ*} e^{2π i ⟪μ, y⟫} 𝓕f(y)`.

This is the unshifted statement applied to the translate `f(· + μ)`, whose Fourier transform is
`e^{2π i ⟪μ, ·⟫}` times that of `f`.  Mathlib has the translation rule for the vector-valued
Fourier integral (`VectorFourier.fourierIntegral_comp_add_right`) but not the shifted summation
formula.

## Main results

* `ZLattice.fourier_comp_addRight` — `𝓕 (f(· + μ)) w = e^{2π i ⟪μ,w⟫} 𝓕f(w)`.
* `ZLattice.poissonSummation_shift` — Poisson summation over the coset `μ + Γ`.
-/

noncomputable section

open MeasureTheory Module
open scoped Real FourierTransform RealInnerProductSpace

namespace ZLattice

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [DecidableEq ι] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Ebeling's hypothesis (V2) is stable under translation. -/
theorem _root_.ZSpan.LocallySummableOn.comp_addRight {b : Basis ι ℝ V} {f : C(V, ℂ)}
    (hf : ZSpan.LocallySummableOn b f) (μ : V) :
    ZSpan.LocallySummableOn b (f.comp (ContinuousMap.addRight μ)) := by
  intro K
  set K' : TopologicalSpace.Compacts V :=
    ⟨(fun x => x + μ) '' (K : Set V), K.isCompact.image (continuous_id.add continuous_const)⟩
    with hK'
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hf K')
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
  have hx : (x : V) + μ ∈ (K' : Set V) := ⟨x, x.2, rfl⟩
  have hval : ((f.comp (ContinuousMap.addRight μ)).comp
        (ContinuousMap.addRight (ZSpan.latticeVec ι b m))).restrict (K : Set V) x
      = (f.comp (ContinuousMap.addRight (ZSpan.latticeVec ι b m))).restrict (K' : Set V)
          ⟨(x : V) + μ, hx⟩ := by
    show f ((x : V) + ZSpan.latticeVec ι b m + μ) = f ((x : V) + μ + ZSpan.latticeVec ι b m)
    rw [add_right_comm]
  rw [hval]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- Translating the argument multiplies the Fourier transform by a character. -/
theorem fourier_comp_addRight (f : V → ℂ) (μ w : V) :
    𝓕 (fun v => f (v + μ)) w
      = Complex.exp (2 * Real.pi * Complex.I * (⟪μ, w⟫ : ℝ)) * 𝓕 f w := by
  have h := VectorFourier.fourierIntegral_comp_add_right (𝐞) (volume : Measure V) (innerₗ V) f μ
  have h2 : 𝓕 (fun v => f (v + μ)) w = ((𝐞 ((innerₗ V μ) w) : Circle) : ℂ) • 𝓕 f w := by
    rw [Real.fourier_eq, Real.fourier_eq]
    exact congrFun h w
  rw [h2, Real.fourierChar_apply]
  simp only [innerₗ_apply_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **Poisson summation over a coset of a lattice.**  For `μ ∈ V`,

`∑_{x ∈ Γ} f (x + μ) = (covol Γ)⁻¹ ∑_{y ∈ Γ*} e^{2π i ⟪μ, y⟫} 𝓕f(y)`.

This is the shape the theta series of a lattice of level `N > 1` transforms in: the characters
`e^{2π i ⟪μ, y⟫}` are what turns the `S`-transformation into a sum over the discriminant group. -/
theorem poissonSummation_shift (b : Basis ι ℝ V) (μ : V) {f : C(V, ℂ)}
    (hf : ZSpan.LocallySummableOn b (f.comp (ContinuousMap.addRight μ)))
    (hsum : Summable fun y : dual V (Submodule.span ℤ (Set.range b)) =>
      Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ)) * 𝓕 (f : V → ℂ) (y : V)) :
    ∑' x : Submodule.span ℤ (Set.range b), f ((x : V) + μ)
      = (covolume (Submodule.span ℤ (Set.range b)) volume)⁻¹
        • ∑' y : dual V (Submodule.span ℤ (Set.range b)),
            Complex.exp (2 * Real.pi * Complex.I * (⟪μ, (y : V)⟫ : ℝ))
              * 𝓕 (f : V → ℂ) (y : V) := by
  have hFeq : ∀ w : V, 𝓕 ((f.comp (ContinuousMap.addRight μ) : C(V, ℂ)) : V → ℂ) w
      = Complex.exp (2 * Real.pi * Complex.I * (⟪μ, w⟫ : ℝ)) * 𝓕 (f : V → ℂ) w := by
    intro w
    exact fourier_comp_addRight (f : V → ℂ) μ w
  have hsum' : Summable fun y : dual V (Submodule.span ℤ (Set.range b)) =>
      𝓕 ((f.comp (ContinuousMap.addRight μ) : C(V, ℂ)) : V → ℂ) (y : V) :=
    hsum.congr fun y => (hFeq (y : V)).symm
  have hP := poissonSummation b hf hsum'
  have hlhs : ∑' x : Submodule.span ℤ (Set.range b), f ((x : V) + μ)
      = ∑' x : Submodule.span ℤ (Set.range b),
          (f.comp (ContinuousMap.addRight μ) : C(V, ℂ)) (x : V) := rfl
  rw [hlhs, hP]
  congr 1
  exact tsum_congr fun y => hFeq (y : V)

end ZLattice
