/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockSpanning
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Instances.Matrix

/-!
# Jacobi characters — Theorem 5.3.9  (Gannon §5.3.5, pp. 344–345)

The refinement of Zhu's theorem that keeps track of a `𝒱₁`-weight and transforms like a
**Jacobi form**.

* **`Z_M(τ,u,v)`** (Gannon 5.3.21a): `tr_M e^{2πi(o(v) − (u|v)/2)} q^{L₀ + o(u) − (c+12(u|u))/24}`.
  The exponential of the zero mode `o(v)` is a genuine operator exponential — `o(v)` is **not**
  locally nilpotent, so `Core/Automorphism.expLN` does not apply.  Since every weight space `M_α`
  is finite-dimensional and preserved by zero modes, `e^{2πi o(v)}` is defined **blockwise**: on
  `M_α` it is the matrix exponential of the block of `o(v)` (`blockExpTrace`), which is exactly
  the construction of `gradedExpL0` with `L₀` replaced by an arbitrary weight-preserving operator.
  `q^{o(u)} = e^{2πiτ o(u)}` is treated the same way, so `Z_M(τ,u,v)` is a function of `τ ∈ ℍ`
  (a `tsum` over the weights `h + ℕ`), not a formal `q`-series.
* **The Jacobi character** (Def 5.3.7 / 5.3.14): `χ^J_M(τ,v,w) = e^{2πiw}·Z_M(τ,0,v)`.
* **Theorem 5.3.9** (5.3.20): the transformation law, stated as a `Prop` (`JacobiTransformation`)
  over a `ModularData D` — "with the same `ρ` as Theorem 5.3.8" — so it is downstream of the
  spanning data of `BlockSpanning`.
* **The consistency check**: at `u = v = 0`, `Z_M(τ,0,0)` is the character `qEvalAt (gradedDim)`
  (`Zfun_zero_zero`), so the `v = w = 0` instance of `JacobiTransformation` is exactly Zhu's law
  5.3.18b for the graded dimensions (`jacobiTransformation_zero_iff_zhu`).

The invariant bilinear form `(·|·)` on `𝒱₁` is carried as a parameter `β` (an `InvariantForm W`,
`Core/BilinearForm`, is the intended instance).

## Status
Definitions real (axiom-clean); `Zfun_zero_zero` and the reduction to Zhu's law proved;
`JacobiTransformation` is a named `Prop` (Thm 5.3.9), not asserted.
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Blockwise operator exponentials -/

/-- The block of `A` on `M_α` as a matrix in the chosen finite basis. -/
noncomputable def blockMatrix (N : OrdVModule W M) (A : Module.End ℂ M) (α : ℂ) :
    Matrix (Fin (Module.finrank ℂ (N.weight α))) (Fin (Module.finrank ℂ (N.weight α))) ℂ :=
  haveI := N.finrank α
  LinearMap.toMatrix (Module.finBasis ℂ (N.weight α)) (Module.finBasis ℂ (N.weight α))
    (weightBlock N A α)

/-- **The blockwise trace of a product of two operator exponentials**:
`tr_{M_α}(e^{A}·e^{B})`, via the matrix exponential of the blocks.  This is `gradedExpL0`'s
construction for an arbitrary weight-preserving operator, and it is what `e^{2πi o(v)}` means. -/
noncomputable def blockExpTrace (N : OrdVModule W M) (A B : Module.End ℂ M) (α : ℂ) : ℂ :=
  Matrix.trace (NormedSpace.exp (blockMatrix N A α) * NormedSpace.exp (blockMatrix N B α))

/-- The exponential of the zero block is the identity: `tr_{M_α}(e⁰·e⁰) = dim M_α`. -/
theorem blockExpTrace_zero_zero (N : OrdVModule W M) (α : ℂ) :
    blockExpTrace N 0 0 α = (Module.finrank ℂ (N.weight α) : ℂ) := by
  haveI := N.finrank α
  have h0 : blockMatrix N 0 α = 0 := by
    rw [blockMatrix, show weightBlock N (0 : Module.End ℂ M) α = 0 from by
      simp only [weightBlock, LinearMap.zero_comp, LinearMap.comp_zero], map_zero]
  rw [blockExpTrace, h0, NormedSpace.exp_zero, one_mul, Matrix.trace_one, Fintype.card_fin]

/-! ## `Z_M(τ, u, v)` and the Jacobi character -/

/-- The scalar `2πi`. -/
noncomputable def twoPiI : ℂ := 2 * (Real.pi : ℂ) * Complex.I

/-- **`Z_M(τ,u,v)`** (Gannon 5.3.21a), for a module of conformal weight `h` and an invariant
bilinear form `β` on `𝒱`:

  `Z_M(τ,u,v) = Σ_{n≥0} tr_{M_{h+n}}( e^{2πi(o(v) − (u|v)/2)} · e^{2πiτ·o(u)} ) · e^{2πiτ(h+n−(c+12(u|u))/24)}`.

The two operator exponentials are taken blockwise on the finite-dimensional weight spaces. -/
noncomputable def Zfun (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (u v : 𝒱)
    (τ : UpperHalfPlane) : ℂ :=
  ∑' n : ℕ,
    blockExpTrace N (twoPiI • (oMod N v - (β u v / 2) • (1 : Module.End ℂ M)))
        ((twoPiI * (τ : ℂ)) • oMod N u) (h + n)
      * Complex.exp (twoPiI * (τ : ℂ) * (h + n - (W.centralCharge + 12 * β u u) / 24))

/-- **The Jacobi character** `χ^J_M(τ,v,w) = e^{2πiw}·Z_M(τ,0,v)` (Gannon Def 5.3.7 / 5.3.14). -/
noncomputable def jacobiChar (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (v : 𝒱) (w : ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (twoPiI * w) * Zfun N h β 0 v τ

/-! ## The consistency check `u = v = 0` -/

/-- **`Z_M(τ,0,0)` is the character**: `qEvalAt (gradedDim N) (h − c/24) τ`. -/
theorem Zfun_zero_zero (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (τ : UpperHalfPlane) :
    Zfun N h β 0 0 τ = qEvalAt (gradedDim N) (h - W.centralCharge / 24) τ := by
  rw [Zfun, qEvalAt, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  simp only [map_zero, zero_div, zero_smul, sub_zero, smul_zero, mul_zero, add_zero]
  rw [blockExpTrace_zero_zero, gradedDim,
    show h - W.centralCharge / 24 + (n : ℂ) + W.centralCharge / 24 = h + n from by ring,
    qParam, ← Complex.exp_nat_mul, twoPiI, mul_left_comm, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- `χ^J_M(τ, 0, 0)` is the character. -/
theorem jacobiChar_zero_zero (N : OrdVModule W M) (h : ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ)
    (τ : UpperHalfPlane) :
    jacobiChar N h β 0 0 τ = qEvalAt (gradedDim N) (h - W.centralCharge / 24) τ := by
  rw [jacobiChar, mul_zero, Complex.exp_zero, one_mul, Zfun_zero_zero]

/-! ## Theorem 5.3.9 as a statement -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 5.3.9 (Gannon 5.3.20)** — the Jacobi transformation law for a family of modules with
modular data `D` (the same `ρ` as Theorem 5.3.8) and an invariant form `β`:

  `χ^J_{Mᵢ}(Aτ, v/(cτ+d), w − c(v|v)/(2(cτ+d))) = Σ_j ρ(A)_{ij} χ^J_{Mⱼ}(τ, v, w)`

for all `A ∈ SL₂(ℤ)`, `v ∈ 𝒱₁`, `w ∈ ℂ`.  A named `Prop`; its proof (via Miyamoto / Krauel–Mason)
is downstream of the trace-spanning data of `BlockSpanning`. -/
def JacobiTransformation (D : ModularData W ι) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) : Prop :=
  ∀ (A : SL(2, ℤ)) (v : 𝒱), v ∈ W.grading 1 → ∀ (w : ℂ) (i : ι) (τ : UpperHalfPlane),
    jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • v)
        (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β v v / (2 * autFactor A τ)) (A • τ)
      = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β v w τ

/-- **Consistency**: the `v = 0, w = 0` instance of the Jacobi transformation law is exactly Zhu's
law 5.3.18b for the graded dimensions (`ZhuModularityAnalytic` at `v = 𝟙`), since
`χ^J(τ,0,0) = χ(τ)`. -/
theorem jacobiTransformation_zero (D : ModularData W ι) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ)
    (hJ : JacobiTransformation D β) (A : SL(2, ℤ)) (i : ι) (τ : UpperHalfPlane) :
    qEvalAt (gradedDim (D.Mfam i).isMod) (D.h i - W.centralCharge / 24) (A • τ)
      = ∑ j, D.rep A i j * qEvalAt (gradedDim (D.Mfam j).isMod) (D.h j - W.centralCharge / 24) τ := by
  have h := hJ A 0 (Submodule.zero_mem _) 0 i τ
  simp only [smul_zero, map_zero, mul_zero, zero_div, sub_zero] at h
  rw [jacobiChar_zero_zero] at h
  rw [h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [jacobiChar_zero_zero]

/-- The graded-dimension instance of `ZhuModularityAnalytic` — the same statement as
`jacobiTransformation_zero`, seen from Zhu's side (`traceFun` at `𝟙` is the character). -/
theorem zhuModularityAnalytic_vacuum (D : ModularData W ι) (hZ : ZhuModularityAnalytic D)
    (A : SL(2, ℤ)) (i : ι) (τ : UpperHalfPlane) :
    qEvalAt (gradedDim (D.Mfam i).isMod) (D.h i - W.centralCharge / 24) (A • τ)
      = ∑ j, D.rep A i j * qEvalAt (gradedDim (D.Mfam j).isMod) (D.h j - W.centralCharge / 24) τ := by
  have hvac0 : W.vacuum ∈ sqWeightSpace W ((0 : ℕ) : ℂ) := by
    rw [mem_sqWeightSpace_iff, Nat.cast_zero, zero_smul, Lsq_zero_apply]
    refine finsum_eq_zero_of_forall_eq_zero (fun a => ?_)
    by_cases ha : a < 0
    · rw [sqBracketCoeff_zero_of_neg ha, zero_smul]
    · push_neg at ha
      rw [VertexOperatorAlgebra.L_def,
        show mode (W.Y W.conformalVector) (a + 1) W.vacuum
          = W.smul W.conformalVector (a + 1) W.vacuum from rfl,
        W.smul_vacuum_nonneg _ (by omega), smul_zero]
  have h := hZ A 0 W.vacuum hvac0 i τ
  rw [pow_zero, one_mul] at h
  simp only [traceFun, torusOnePoint_vacuum, torusPartition] at h
  exact h

end

/-! ## Residual

* **Theorem 5.3.9 itself** (`JacobiTransformation D β` for the modular data of a `C₂`-cofinite
  weakly rational VOA) — downstream of the trace-spanning data (Zhu Thms 5.3.1–5.3.3) and the
  `𝒱₁`-bookkeeping of Miyamoto [426] / Krauel–Mason [151].
* **Semisimplicity of `o(v)`** for `v` in a Cartan subalgebra of `𝒱₁` (needed to read `Z_M` as a
  `q`-expansion with rational exponents) — not needed for the definition, which is blockwise. -/

end VOA
