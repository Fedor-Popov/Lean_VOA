/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GelfandFuks
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The square-bracket (torus) grading `𝒱_{[k]}`  (Gannon 5.3.17a, 5.3.18a)

Zhu's theorem 5.3.18a is quantified over the **square-bracket weight**: the exponent `n` in the
automorphy factor `(cτ+d)ⁿ` is the `L[0]`-eigenvalue, not the `L₀`-eigenvalue.  So the grading
`𝒱_{[k]} := ker(L[0] − k)` is a genuine prerequisite for `ZhuTheorem`, not decoration.

## Structure of `L[0]`

`L[0] = Lsq W 0` has **no vacuum correction** (`s(1) = 0`), so it is purely the `ω`-part:
`L[0] = Σ_{a ≥ 0} d[0,a]·L_a` with `d[0,0] = 1` (`sqBracketCoeff_zero_diag`) — i.e.

  `L[0] = L₀ + (strictly grade-lowering terms)`,

since `L_a` for `a ≥ 1` lowers the `L₀`-grade by `a`.  This triangularity is the standard reason the
square-bracket grading has the *same* graded dimensions as the ordinary one, and it is the route to
`DirectSum.IsInternal (sqWeightSpace W)` (see the residual note).

## Status
`DirectSum.IsInternal (sqWeightSpace W)` is **proved unconditionally** —
independence here, spanning in `Modularity/SqWeightSpanning.lean` (`sqWeightSpace_isInternal`).

## References
* Gannon §5.3.5, eqs. (5.3.17a), (5.3.18a); Zhu, J. AMS 9 (1996) §4.
-/

namespace VOA

open PowerSeries
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The square-bracket weight space** `𝒱_{[k]} = ker(L[0] − k)` (Gannon 5.3.17a). -/
noncomputable def sqWeightSpace (W : VertexOperatorAlgebra 𝒱) (k : ℂ) : Submodule ℂ 𝒱 :=
  LinearMap.ker (Lsq W 0 - k • (LinearMap.id : 𝒱 →ₗ[ℂ] 𝒱))

theorem mem_sqWeightSpace_iff (W : VertexOperatorAlgebra 𝒱) (k : ℂ) (x : 𝒱) :
    x ∈ sqWeightSpace W k ↔ Lsq W 0 x = k • x := by
  rw [sqWeightSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

/-- **`L[0]` has no vacuum correction**: `L[0] x = Σ_a d[0,a]·L_a x` (the `𝟙`-term of `Lsq` vanishes
at `n = 0` because `s(1) = 0`). -/
theorem Lsq_zero_apply (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    Lsq W 0 x = ∑ᶠ a : ℤ, sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.L a x := by
  rw [Lsq_apply, sqBracketCoeffZ_vacuum_of_ne (0 + 1) (by norm_num), mul_zero, zero_smul, sub_zero,
    vSqZ_omega_apply]

/-- **The leading coefficient is `1`**: `d[0,0] = 1`, i.e. `L[0] = L₀ + (lower)`. -/
theorem sqBracketCoeff_zero_diag : sqBracketCoeffZ 2 (0 + 1) (0 + 1) = 1 :=
  sqBracketCoeffZ_diag 0

/-- **Triangularity**: `d[0,a] = 0` for `a < 0`, so `L[0]` involves only `L_a` with `a ≥ 0` — the
`a = 0` term is `L₀` (coefficient `1`) and every `a ≥ 1` term strictly lowers the `L₀`-grade. -/
theorem sqBracketCoeff_zero_of_neg {a : ℤ} (ha : a < 0) :
    sqBracketCoeffZ 2 (0 + 1) (a + 1) = 0 :=
  sqBracketCoeffZ_of_lt 2 (by omega)

/-! ## Toward `DirectSum.IsInternal (sqWeightSpace W)`

Following the repo's own template `Foundations.AffineLie.ell0_isInternal`: the weight spaces **are**
the eigenspaces of `L[0]`, so **independence is automatic** (`Module.End.eigenspaces_iSupIndep`), and
the whole statement reduces to the single spanning fact `⨆ k, 𝒱_{[k]} = ⊤`. -/

/-- **The square-bracket weight spaces are the eigenspaces of `L[0]`.** -/
theorem sqWeightSpace_eq_eigenspace (W : VertexOperatorAlgebra 𝒱) (k : ℂ) :
    sqWeightSpace W k = Module.End.eigenspace (Lsq W 0) k := by
  ext x
  rw [mem_sqWeightSpace_iff, Module.End.mem_eigenspace_iff]

/-- **Independence is automatic**: eigenspaces for distinct eigenvalues are independent. -/
theorem sqWeightSpace_iSupIndep (W : VertexOperatorAlgebra 𝒱) :
    iSupIndep (sqWeightSpace W) := by
  have h : sqWeightSpace W = Module.End.eigenspace (Lsq W 0) :=
    funext (sqWeightSpace_eq_eigenspace W)
  rw [h]
  exact Module.End.eigenspaces_iSupIndep _

/-- **The `L[0]`-grading, reduced to spanning.**  `DirectSum.IsInternal (sqWeightSpace W)` holds
as soon as the weight spaces **span** — independence is free.  So the whole `L[0]`-grading rests on the
single named fact `⨆ k, 𝒱_{[k]} = ⊤` (see the residual note below for its proof route). -/
theorem sqWeightSpace_isInternal_of_iSup_eq_top (W : VertexOperatorAlgebra 𝒱)
    (hspan : ⨆ k : ℂ, sqWeightSpace W k = ⊤) :
    DirectSum.IsInternal (sqWeightSpace W) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (sqWeightSpace_iSupIndep W) hspan

/-- **The single remaining fact** for the `L[0]`-grading: the square-bracket weight spaces span. -/
def SqWeightSpansTop (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ⨆ k : ℂ, sqWeightSpace W k = ⊤

/-- Restatement: `SqWeightSpansTop` is exactly what upgrades independence to an internal grading. -/
theorem sqWeightSpace_isInternal_of_spansTop (W : VertexOperatorAlgebra 𝒱)
    (h : SqWeightSpansTop W) : DirectSum.IsInternal (sqWeightSpace W) :=
  sqWeightSpace_isInternal_of_iSup_eq_top W h

/-! ## `SqWeightSpansTop`

See `Modularity/SqWeightSpanning.lean`: `sqWeightSpansTop_holds` and the unconditional
`sqWeightSpace_isInternal`.  The proof needs neither finite-dimensionality nor a normal-form
conjugation — only that `L₀` acts by **distinct** scalars on distinct grades, which makes `L[0] − d`
*surjective* on `𝒱^{≤e}` for `e < d`.
-/

end VOA
