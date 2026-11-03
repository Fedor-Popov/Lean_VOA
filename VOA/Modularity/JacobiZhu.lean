/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.JacobiCharacter
import VOA.Modularity.RhoS
import VOA.Modularity.BlockFiniteDim

/-!
# Jacobi characters: the slices of Theorem 5.3.9 that are already theorems

`Modularity.JacobiCharacter` defines `Z_M(τ,u,v)` (Gannon 5.3.21a) and `χ^J_M(τ,v,w)` (5.3.14) and
states Theorem 5.3.9 (5.3.20) as `JacobiTransformation D β` — "with the same `ρ` as Theorem 5.3.8".
Two of its slices need nothing beyond what is already proved:

* `jacobiTransformation_T_holds` — **the `A = T` instance of 5.3.20, unconditionally**, for
  every `v ∈ 𝒱₁` and every `w`.  `T` has `c = 0`, so 5.3.20 collapses to the `q`-periodicity
  `Z_M(τ+1,0,v) = e^{2πi(h−c/24)}Z_M(τ,0,v)` (`Zfun_T_transform`) against the diagonal `ρ(T)`.
  This is the Jacobi-character twin of `zhu_modularity_T`.
* `jacobiTransformation_v_zero_of_zhu` — **the `v = 0` instance of 5.3.20 for every `A`**, from
  Zhu's law: `χ^J_M(τ,0,w) = e^{2πiw}·χ_M(τ)` (`jacobiChar_v_zero`), so the elliptic variable
  factors out and 5.3.20 *is* 5.3.18b.

Together with `jacobiTransformation_zero` (the converse consistency check, already in
`JacobiCharacter`) these pin the statement: 5.3.20 restricted to either generator slice is exactly
Zhu's theorem, so the convention in `JacobiTransformation` is the right one.

Also proved here: the elliptic periodicity `jacobiChar_period_w` (`w ↦ w+1`), the first genuine
Jacobi-form property of `χ^J`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Residual: Theorem 5.3.9 for general `(A, v)` — that
needs, beyond `ρ` (available conditionally through `Modularity.RhoS`), the `𝒱₁`-bookkeeping of
Miyamoto / Krauel–Mason: the `u`-dependence of `Z_M(τ,u,v)` under `SL₂(ℤ)` is *not* a formal
consequence of the `u = 0` case.
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## `Z_M(τ,0,v)` as a plain graded trace -/

theorem blockMatrix_zero (N : OrdVModule W M) (α : ℂ) : blockMatrix N 0 α = 0 := by
  haveI := N.finrank α
  rw [blockMatrix, show weightBlock N (0 : Module.End ℂ M) α = 0 from by
    simp only [weightBlock, LinearMap.zero_comp, LinearMap.comp_zero], map_zero]

theorem blockExpTrace_right_zero (N : OrdVModule W M) (A : Module.End ℂ M) (α : ℂ) :
    blockExpTrace N A 0 α = Matrix.trace (NormedSpace.exp (blockMatrix N A α)) := by
  rw [blockExpTrace, blockMatrix_zero, NormedSpace.exp_zero, mul_one]

/-- `Z_M(τ,0,v)` is the graded trace of `e^{2πi·o(v)}` — the `u`-slot being `0`, the `τ`-dependence
sits entirely in the `q`-powers. -/
theorem Zfun_left_zero (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (v : 𝒱)
    (τ : UpperHalfPlane) :
    Zfun N h β 0 v τ
      = ∑' n : ℕ, Matrix.trace (NormedSpace.exp (blockMatrix N (twoPiI • oMod N v) (h + n)))
          * Complex.exp (twoPiI * (τ : ℂ) * (h + n - W.centralCharge / 24)) := by
  rw [Zfun]
  refine tsum_congr (fun n => ?_)
  simp only [map_zero, LinearMap.zero_apply, zero_div, zero_smul, sub_zero, smul_zero,
    mul_zero, add_zero]
  rw [blockExpTrace_right_zero]

/-! ## `T`-periodicity -/

/-- **`Z_M(τ+1,0,v) = e^{2πi(h−c/24)}·Z_M(τ,0,v)`** — the `q`-periodicity of the Jacobi trace,
for every `v`.  The `n`-dependence of the phase is `e^{2πin} = 1`. -/
theorem Zfun_T_transform (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (v : 𝒱)
    {τ τ' : UpperHalfPlane} (hτ : (τ' : ℂ) = (τ : ℂ) + 1) :
    Zfun N h β 0 v τ' = modularTEntry W h * Zfun N h β 0 v τ := by
  rw [Zfun_left_zero, Zfun_left_zero, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [hτ, modularTEntry]
  have hexp : Complex.exp (twoPiI * ((τ : ℂ) + 1) * (h + (n : ℂ) - W.centralCharge / 24))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24))
        * Complex.exp (twoPiI * (τ : ℂ) * (h + (n : ℂ) - W.centralCharge / 24)) := by
    rw [← Complex.exp_add]
    have hsplit : twoPiI * ((τ : ℂ) + 1) * (h + (n : ℂ) - W.centralCharge / 24)
        = (2 * (Real.pi : ℂ) * Complex.I * (h - W.centralCharge / 24)
            + twoPiI * (τ : ℂ) * (h + (n : ℂ) - W.centralCharge / 24))
          + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [twoPiI]; ring
    rw [hsplit, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hexp]
  ring

/-! ## The elliptic variable -/

/-- **Elliptic periodicity** `χ^J_M(τ,v,w+1) = χ^J_M(τ,v,w)` — the first Jacobi-form property. -/
theorem jacobiChar_period_w (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (v : 𝒱) (w : ℂ)
    (τ : UpperHalfPlane) :
    jacobiChar N h β v (w + 1) τ = jacobiChar N h β v w τ := by
  rw [jacobiChar, jacobiChar, twoPiI, mul_add, mul_one, Complex.exp_add,
    show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = ((1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from
      by push_cast; ring, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- `χ^J_M(τ,0,w) = e^{2πiw}·χ_M(τ)`: at `v = 0` the elliptic variable simply factors out. -/
theorem jacobiChar_v_zero (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (w : ℂ)
    (τ : UpperHalfPlane) :
    jacobiChar N h β 0 w τ
      = Complex.exp (twoPiI * w) * qEvalAt (gradedDim N) (h - W.centralCharge / 24) τ := by
  rw [jacobiChar, Zfun_zero_zero]

/-! ## The two proved slices of Theorem 5.3.9 -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `A = T` instance of Theorem 5.3.9 (5.3.20), unconditionally**, for every
`v ∈ 𝒱₁` and every `w`.  `T = (1 1; 0 1)` has `c = 0`, so the elliptic arguments are unchanged and
5.3.20 is exactly the `q`-periodicity of `Z_M` against the diagonal `ρ(T)` of `ModularData`. -/
theorem jacobiTransformation_T_holds (D : ModularData W ι) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (v : 𝒱)
    (w : ℂ) (i : ι) (τ : UpperHalfPlane) :
    jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor ModularGroup.T τ)⁻¹ • v)
        (w - ((ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
            Matrix (Fin 2) (Fin 2) ℤ) 1 0 * β v v / (2 * autFactor ModularGroup.T τ))
        (ModularGroup.T • τ)
      = ∑ j, D.rep ModularGroup.T i j
          * jacobiChar (D.Mfam j).isMod (D.h j) β v w τ := by
  classical
  have hc : (((ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 0 := by simp [ModularGroup.T]
  have hτ : ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [ModularGroup.T]
  rw [autFactor_T, inv_one, one_smul, hc, zero_mul, zero_div, sub_zero, D.rep_T,
    Finset.sum_eq_single i
      (fun j _ hj => by
        simp only [Matrix.of_apply]
        rw [modularRepT_off_diag W D.h (Ne.symm hj), zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi)]
  simp only [Matrix.of_apply, modularRepT_diag]
  rw [jacobiChar, jacobiChar, Zfun_T_transform _ _ _ _ hτ]
  ring

/-- **The `v = 0` instance of Theorem 5.3.9 (5.3.20) for every `A`, from Zhu's law.**
At `v = 0` the elliptic variable factors out of `χ^J`, so 5.3.20 *is* 5.3.18b for the graded
dimensions.  Together with `jacobiTransformation_zero` (the converse) this pins the convention of
`JacobiTransformation`. -/
theorem jacobiTransformation_v_zero_of_zhu (D : ModularData W ι) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ)
    (hZ : ZhuModularityAnalytic D) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (w : ℂ) (i : ι)
    (τ : UpperHalfPlane) :
    jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
        (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
      = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ := by
  have hchar := zhuModularityAnalytic_vacuum D hZ A i τ
  simp only [smul_zero, map_zero, LinearMap.zero_apply, mul_zero, zero_div, sub_zero]
  rw [jacobiChar_v_zero, hchar, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [jacobiChar_v_zero]
  ring

end

/-! ## Downstream of the new `ρ` -/

section Downstream

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `v = 0` slice of Theorem 5.3.9 (5.3.20) from the dimension bound.**  With
`Modularity.BlockFiniteDim` supplying finite-dimensionality unconditionally, this instance of the
Jacobi transformation law rests on exactly the same inputs as Zhu's theorem itself. -/
theorem exists_jacobiTransformation_v_zero (Mfam : ι → IrrModule W) (hh : ι → ℂ)
    (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (hC2 : C2Cofinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (hh i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (hh i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W hh))
    (hle : Module.finrank ℂ (analyticSlashAmbient Mfam hh) ≤ Fintype.card ι) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D ∧
      ∀ (A : SL(2, ℤ)) (w : ℂ) (i : ι) (τ : UpperHalfPlane),
        jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
            (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
          = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ := by
  refine ⟨_, zhu_modularity_of_analytic_finrank_le Mfam hh hC2 hz₀ hcw hgr hinj hle,
    fun A w i τ => ?_⟩
  exact jacobiTransformation_v_zero_of_zhu _ β
    (zhu_modularity_of_analytic_finrank_le Mfam hh hC2 hz₀ hcw hgr hinj hle) A w i τ

end Downstream

/-! ## Residual for Theorem 5.3.9

The two slices above are the `A`-generator slice (`A = T`, all `v`) and the `v`-degenerate slice
(all `A`, `v = 0`).  The general case is **not** a formal consequence of them: 5.3.20 asserts that
the elliptic variable transforms as `v ↦ v/(cτ+d)` with the theta-like factor
`e^{−2πi·c(v|v)/(2(cτ+d))}`, and that is a statement about the `u`-dependence of `Z_M(τ,u,v)` —
Miyamoto's `𝒱₁`-refinement of Zhu's recursion, not the recursion itself.  With `ρ` available
(conditionally) through `Modularity.RhoS`, the missing input is exactly that refinement.
-/

end VOA
