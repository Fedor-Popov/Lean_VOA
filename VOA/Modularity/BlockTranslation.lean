/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockFiniteDim
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# `T` acts on the (finite-dimensional) block space

The `SL₂(ℤ)`-obstruction of `Modularity.SlashAmbientObstruction` is specific to `denomC γ ≠ 1`.
For `γ = T` the automorphy factor is `1`, so `blockSlash W T F v z = F v (z+1)` — and *that* map
**does** preserve `IsAnalyticBlock`: it is additive in `v` on the nose, the Eisenstein coefficients
`G_{2j}` are `1`-periodic, and `d/dz` is translation-invariant.

Since Zhu's Theorem 5.3.2 makes the block space finite-dimensional, this exhibits `T` as an
endomorphism of a finite-dimensional space — the entry point of Zhu's own route to Theorem 5.3.3
(generalized `T`-eigendecomposition ⟹ `q`-expansions ⟹ leading-coefficient descent, whose
algebraic half is already banked as `symmetricFunctional_of_zeroModeVanishing`).

## Main results

* `zhuGC_add_one` — `G_{2j}(z+1) = G_{2j}(z)`;
* `IsAnalyticBlock.translate` — the block conditions are `T`-stable;
* `blockTranslateₗ` — translation as a `ℂ`-linear endomorphism, and
  `blockTranslate_mapsTo_analytic` / `blockTranslate_restrict_mem` — it preserves both
  `analyticBlocks W` and its finite-dimensional image `restrictImGT '' 𝔅`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `1`-periodicity of Zhu's Eisenstein family -/

/-- **`G_{2j}` is `1`-periodic**: its `q`-expansion only sees `e^{2πiz}`. -/
theorem zhuGC_add_one (j : ℕ) (z : ℂ) : zhuGC j (z + 1) = zhuGC j z := by
  rw [zhuGC, zhuGC]
  refine tsum_congr (fun n => ?_)
  congr 1
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z
        + ((n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## Translation of blocks -/

section Translate

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

/-- The `T`-translate `F(·)(z+1)` of a family of functions. -/
def blockTranslate (F : 𝒱 → ℂ → ℂ) : 𝒱 → ℂ → ℂ := fun v z => F v (z + 1)

theorem mem_imGT_add_one {z : ℂ} (hz : z ∈ imGT 0) : z + 1 ∈ imGT 0 := by
  simp only [imGT, Set.mem_setOf_eq] at hz ⊢
  simpa using hz

/-- **The block conditions are `T`-stable.** -/
theorem IsAnalyticBlock.translate (hF : IsAnalyticBlock W F) :
    IsAnalyticBlock W (blockTranslate F) where
  holo := fun v => by
    intro z hz
    have hd : DifferentiableAt ℂ (F v) (z + 1) :=
      (hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds (mem_imGT_add_one hz))
    exact (hd.comp z ((differentiable_id.add_const 1) z)).differentiableWithinAt
  addv := fun v w z => hF.addv v w (z + 1)
  smulv := fun c v z => hF.smulv c v (z + 1)
  vanish := fun ka hka a ha v => by
    funext z
    exact congrFun (hF.vanish ka hka a ha v) (z + 1)
  negTwo := fun ka hka a ha v z hz => by
    have h := hF.negTwo ka hka a ha v (z + 1) (mem_imGT_add_one hz)
    refine Eq.trans ?_ h
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [zhuGC_add_one]
    rfl
  omega := fun v z hz => by
    have h := hF.omega v (z + 1) (mem_imGT_add_one hz)
    have hd : _root_.deriv (blockTranslate F v) z = _root_.deriv (F v) (z + 1) :=
      deriv_comp_add_const (f := F v) (a := 1) (x := z)
    rw [show blockTranslate F (Lsq W (-2) v) z = F (Lsq W (-2) v) (z + 1) from rfl, h, hd]
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [zhuGC_add_one]
    rfl

/-- Translation as a `ℂ`-linear endomorphism of `𝒱 → ℂ → ℂ`. -/
def blockTranslateₗ : (𝒱 → ℂ → ℂ) →ₗ[ℂ] (𝒱 → ℂ → ℂ) where
  toFun := blockTranslate
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem blockTranslateₗ_apply (F : 𝒱 → ℂ → ℂ) : blockTranslateₗ F = blockTranslate F := rfl

variable (W)

/-- **`T` preserves the block space.** -/
theorem blockTranslate_mapsTo_analytic :
    Submodule.map (blockTranslateₗ (𝒱 := 𝒱)) (analyticBlocks W) ≤ analyticBlocks W := by
  rintro _ ⟨F, hF, rfl⟩
  exact (hF : IsAnalyticBlock W F).translate

/-- `restrictImGT` commutes with translation (the half-plane is translation-invariant). -/
theorem restrictImGT_blockTranslate (F : 𝒱 → ℂ → ℂ) :
    restrictImGT (blockTranslate F) = blockTranslate (restrictImGT F) := by
  funext v z
  by_cases hz : z ∈ imGT 0
  · rw [restrictImGT_apply _ hz]
    show F v (z + 1) = Set.indicator (imGT 0) (F v) (z + 1)
    rw [Set.indicator_of_mem (mem_imGT_add_one hz)]
  · show Set.indicator (imGT 0) _ z = _
    rw [Set.indicator_of_notMem hz]
    show (0 : ℂ) = Set.indicator (imGT 0) (F v) (z + 1)
    rw [Set.indicator_of_notMem (by
      simp only [imGT, Set.mem_setOf_eq] at hz ⊢
      simpa using hz)]

/-- **`T` preserves the FINITE-DIMENSIONAL block space** `restrictImGT '' 𝔅` — so `T` is an
endomorphism of a finite-dimensional `ℂ`-vector space. -/
theorem blockTranslate_restrict_mem :
    Submodule.map (blockTranslateₗ (𝒱 := 𝒱)) (Submodule.map restrictImGT (analyticBlocks W))
      ≤ Submodule.map restrictImGT (analyticBlocks W) := by
  rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
  refine ⟨blockTranslate F, (hF : IsAnalyticBlock W F).translate, ?_⟩
  exact restrictImGT_blockTranslate F

end Translate

end VOA
