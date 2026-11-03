/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.InvariantFormRadical
import VOA.Core.RigidityBridge
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The level-`n` Gram **matrix**, and what its rank and determinant compute

`Core/InvariantFormRadical` proves Li's theorem in the form

* `LiRadical.maxGradedIdeal_inf_grading` — `maxGradedIdeal W ⊓ 𝒱ₙ` is the image of
  `ker (gradedForm B n)`;
* `LiRadical.maxGradedIdeal_inf_grading_eq_bot_iff` — that intersection is `⊥` exactly when
  `gradedForm B n` is nondegenerate.

Both are statements about an abstract bilinear form.  This file turns them into statements
about a **matrix**, which is the object a Kac-determinant computation actually produces.

## Contents

Fix `B : InvariantForm W` fully invariant and normalised, and a finite basis `e` of `𝒱ₙ`.

* `gramMatrix B n e` — the matrix `(i, j) ↦ B(eᵢ, eⱼ)`.
* `gramMatrix_det_ne_zero_iff` — `det (gramMatrix B n e) ≠ 0 ↔ maxGradedIdeal W ⊓ 𝒱ₙ = ⊥`.
* `rank_gramMatrix_add_finrank` — `rank (gramMatrix B n e) + dim (maxGradedIdeal W ⊓ 𝒱ₙ)
  = dim 𝒱ₙ`, and `rank_gramMatrix_eq` in subtracted form.
* `finrank_maxQuotient_grading` — **the bridge**: `dim (W / maxGradedIdeal W)ₙ
  = rank (canGram hne hqp n e)`.  This is the statement that turns "identify the simple quotient"
  into a finite linear-algebra computation, uniformly in the parameters of a family.
* `finrank_maxQuotient_grading_lt_of_det_eq_zero` /
  `finrank_maxQuotient_grading_eq_of_det_ne_zero` — the **graded-dimension jump**: a vanishing
  level-`n` determinant strictly lowers `dim L(W)ₙ`, a nonvanishing one leaves it full.

## ⚠ Rank, not determinant, is what the bridge computes

A Kac determinant tells you *where* the radical is nonzero; it does **not** tell you *how big*
the radical is.  Two Gram matrices whose determinants agree up to a nonzero constant have the
same zero set but need not have the same rank at a zero.  Since `rank_gramMatrix_eq` is the
statement that gives `dim Lₖ(𝒱)ₙ = dim 𝒱ₙ - dim (radical)ₙ`, a Gram matrix imported from a
*different* form — even one whose determinant is a constant multiple — is not a substitute.

Concretely, in this library: `Examples/LeeYangKac.gram4` is the matrix of
`RigidBridge.shapForm` (the top-mode pairing `ε(a₍₂ₖ₋₁₎b)`), **not** of
`gradedForm (canonicalInvariantForm hne hqp) 4`.  The two agree only on quasi-primary vectors,
and at level `4` of a Virasoro VOA neither basis vector is quasi-primary
(`L₁L₋₄𝟙 = 5L₋₃𝟙` and `L₁L₋₂²𝟙 = 3L₋₃𝟙`).  Their determinants differ by the constant `21`,
so the *zero sets* coincide and `det_gram4` correctly locates the degenerate central charges —
but only a Gram matrix for `gradedForm` itself may be fed to `rank_gramMatrix_eq`.

## Hypotheses

No finiteness is assumed of `W`: the caller supplies a `Basis ι ℂ (W.grading n)` with `ι` a
`Fintype`, which is exactly the data a concrete level-`n` computation has anyway.
-/

namespace VOA

open VOA.VertexOperatorAlgebra
open Module (finrank Dual Basis)
open scoped Matrix
open QuotVOA (maxGradedIdeal)
open LiRadical (gradedForm)

universe u

namespace GramMat

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **level-`n` Gram matrix** of an invariant form `B` in a basis `e` of `𝒱ₙ`:
`(gramMatrix B n e) i j = B(eᵢ, eⱼ)`. -/
noncomputable def gramMatrix (B : InvariantForm W) (n : ℤ) (e : Basis ι ℂ (W.grading n)) :
    Matrix ι ι ℂ :=
  LinearMap.BilinForm.toMatrix e (gradedForm B n)

@[simp] theorem gramMatrix_apply (B : InvariantForm W) (n : ℤ) (e : Basis ι ℂ (W.grading n))
    (i j : ι) : gramMatrix B n e i j = B.form (e i : 𝒱) (e j : 𝒱) := by
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply, LiRadical.gradedForm_apply]

section

-- `𝒱ₙ` is a finite free `ℂ`-module once a finite basis of it is given.
omit [Fintype ι] [DecidableEq ι] in
theorem finite_of_basis [Finite ι] {W : VertexOperatorAlgebra 𝒱} {n : ℤ}
    (e : Basis ι ℂ (W.grading n)) : Module.Finite ℂ (W.grading n) := Module.Finite.of_basis e

omit [Fintype ι] [DecidableEq ι] in
theorem free_of_basis {W : VertexOperatorAlgebra 𝒱} {n : ℤ} (e : Basis ι ℂ (W.grading n)) :
    Module.Free ℂ (W.grading n) := Module.Free.of_basis e

variable (B : InvariantForm W) (n : ℤ) (e : Basis ι ℂ (W.grading n))

/-- The Gram matrix is the matrix of the map `𝒱ₙ → (𝒱ₙ)^*` induced by `B`, up to transpose. -/
theorem toLin_transpose_gramMatrix :
    Matrix.toLin e e.dualBasis (gramMatrix B n e)ᵀ = gradedForm B n := by
  haveI := finite_of_basis (W := W) (n := n) e
  refine e.ext fun j => ?_
  refine e.ext fun i => ?_
  rw [Matrix.toLin_self]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.transpose_apply, Basis.dualBasis_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Basis.repr_self, Ne.symm hb])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp [Basis.repr_self]

/-- **The Gram determinant decides the level-`n` radical.**  `det ≠ 0` exactly when the
maximal graded ideal has nothing in degree `n`. -/
theorem gramMatrix_det_ne_zero_iff (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    (gramMatrix B n e).det ≠ 0 ↔ maxGradedIdeal W ⊓ W.grading n = ⊥ := by
  haveI := finite_of_basis (W := W) (n := n) e
  haveI := free_of_basis (W := W) (n := n) e
  rw [LiRadical.maxGradedIdeal_inf_grading_eq_bot_iff hB hn n,
    ← LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e]
  rfl

/-- Restated: the level-`n` Gram form is degenerate exactly when the maximal graded ideal
reaches degree `n`. -/
theorem gramMatrix_det_eq_zero_iff (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    (gramMatrix B n e).det = 0 ↔ maxGradedIdeal W ⊓ W.grading n ≠ ⊥ := by
  rw [← not_ne_iff (a := (gramMatrix B n e).det), gramMatrix_det_ne_zero_iff B n e hB hn]

/-- The degree-`n` piece of the maximal ideal has the same dimension as the radical of the
level-`n` Gram form (the two are related by the injective inclusion `𝒱ₙ ↪ 𝒱`). -/
theorem finrank_maxGradedIdeal_inf (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ 𝒱)
      = finrank ℂ (LinearMap.ker (gradedForm B n)) := by
  rw [LiRadical.maxGradedIdeal_inf_grading hB hn n]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (W.grading n).subtype (Submodule.subtype_injective _) _)).symm

/-- **The rank of the level-`n` Gram matrix is the dimension of the level-`n` piece of the
*simple quotient*.**  Stated additively to avoid truncated subtraction:
`rank + dim (maxGradedIdeal ⊓ 𝒱ₙ) = dim 𝒱ₙ`.

This — not the determinant — is what a Gram computation must produce if one wants the graded
dimensions of `W / maxGradedIdeal W`. -/
theorem rank_gramMatrix_add_finrank (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    (gramMatrix B n e).rank + finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ 𝒱)
      = finrank ℂ (W.grading n) := by
  haveI := finite_of_basis (W := W) (n := n) e
  have hrank : (gramMatrix B n e).rank
      = finrank ℂ (LinearMap.range (gradedForm B n)) := by
    rw [← Matrix.rank_transpose (gramMatrix B n e),
      Matrix.rank_eq_finrank_range_toLin (gramMatrix B n e)ᵀ e.dualBasis e,
      toLin_transpose_gramMatrix B n e]
  rw [hrank, finrank_maxGradedIdeal_inf B n hB hn]
  exact LinearMap.finrank_range_add_finrank_ker (gradedForm B n)

/-- The same statement in subtracted form, as usually quoted:
`rank (Gram) = dim 𝒱ₙ - dim (maxGradedIdeal ⊓ 𝒱ₙ)`. -/
theorem rank_gramMatrix_eq (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    (gramMatrix B n e).rank
      = finrank ℂ (W.grading n)
        - finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ 𝒱) := by
  have h := rank_gramMatrix_add_finrank B n e hB hn
  omega

/-- Dually: the level-`n` radical has dimension `dim 𝒱ₙ - rank`. -/
theorem finrank_maxGradedIdeal_inf_eq (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ 𝒱)
      = finrank ℂ (W.grading n) - (gramMatrix B n e).rank := by
  have h := rank_gramMatrix_add_finrank B n e hB hn
  omega

end

/-! ## Instantiation at the canonical FHL form

Under `hne : 𝟙 ≠ 0` and `hqp : L₁𝒱₁ = 0` the canonical form is unconditionally fully invariant
and normalised, so all four statements above apply with no further hypotheses. -/

section Canonical

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hne : W.vacuum ≠ 0) (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0)
variable (n : ℤ) (e : Basis ι ℂ (W.grading n))

/-- The **canonical** level-`n` Gram matrix: the matrix of
`gradedForm (canonicalInvariantForm hne hqp) n`.  Its normalisation is fixed by
`(𝟙|𝟙) = +1` (`InvariantForm.Normalized`). -/
noncomputable def canGram : Matrix ι ι ℂ := gramMatrix (canonicalInvariantForm hne hqp) n e

@[simp] theorem canGram_apply (i j : ι) :
    canGram hne hqp n e i j = (canonicalInvariantForm hne hqp).form (e i : V) (e j : V) :=
  gramMatrix_apply _ _ _ _ _

/-- `det ≠ 0 ↔ maxGradedIdeal W ⊓ 𝒱ₙ = ⊥`, for the canonical form. -/
theorem canGram_det_ne_zero_iff :
    (canGram hne hqp n e).det ≠ 0 ↔ maxGradedIdeal W ⊓ W.grading n = ⊥ :=
  gramMatrix_det_ne_zero_iff _ n e (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp)

/-- `rank + dim (maxGradedIdeal ⊓ 𝒱ₙ) = dim 𝒱ₙ`, for the canonical form. -/
theorem rank_canGram_add_finrank :
    (canGram hne hqp n e).rank + finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ V)
      = finrank ℂ (W.grading n) :=
  rank_gramMatrix_add_finrank _ n e (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp)

/-- The level-`n` dimension of the simple quotient, read off the canonical Gram matrix. -/
theorem finrank_radical_eq_sub_rank :
    finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ V)
      = finrank ℂ (W.grading n) - (canGram hne hqp n e).rank :=
  finrank_maxGradedIdeal_inf_eq _ n e (canonicalInvariantForm_isFullyInvariant hne hqp)
    (canonicalInvariantForm_normalized hne hqp)

end Canonical

/-! ## §  **The bridge**: the graded dimension of the *simple quotient*

Everything above measures the **radical** `maxGradedIdeal W ⊓ 𝒱ₙ`.  What a caller actually wants
is the graded dimension of the simple quotient `L(W) = W / maxGradedIdeal W`, because that is the
object a character, a Zhu computation, or a graded-unitarity filtration is about.

The two are the same statement read through rank–nullity, and the identification is *definitional*
on one side: `QuotVOA.quotientVOA` gives the quotient VOA the grading `𝒱ₙ.map mkQ`, so
`(maxQuotientVOA W).grading n = (W.grading n).map (maxGradedIdeal W).mkQ` holds by `rfl`.
Restricting `mkQ` to `𝒱ₙ` therefore has that graded piece as its **range**, and
`maxGradedIdeal W ⊓ 𝒱ₙ` as (the image of) its **kernel**.  Rank–nullity for that one linear map,
against `rank_canGram_add_finrank`, is the whole proof.

`finrank_maxQuotient_grading` is the statement that makes "identify the simple quotient"
into a finite linear-algebra computation, uniformly in the parameters of a family.
-/

section Bridge

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The grading of the maximal quotient is the image grading — **by `rfl`**, from
`QuotVOA.quotientVOA`. -/
theorem maxQuotientVOA_grading_eq (n : ℤ) :
    (QuotVOA.maxQuotientVOA W).grading n = (W.grading n).map (maxGradedIdeal W).mkQ := rfl

/-- The quotient map `V ↠ V ⧸ maxGradedIdeal W`, restricted to the degree-`n` piece. -/
noncomputable def mkQGrading (W : VertexOperatorAlgebra V) (n : ℤ) :
    (W.grading n) →ₗ[ℂ] (V ⧸ maxGradedIdeal W) :=
  (maxGradedIdeal W).mkQ.domRestrict (W.grading n)

/-- Its range is the degree-`n` piece of the maximal quotient. -/
theorem range_mkQGrading (n : ℤ) :
    LinearMap.range (mkQGrading W n) = (W.grading n).map (maxGradedIdeal W).mkQ := by
  rw [mkQGrading, LinearMap.range_domRestrict]

/-- Its kernel is the level-`n` radical, viewed inside `𝒱ₙ`. -/
theorem ker_mkQGrading (n : ℤ) :
    (LinearMap.ker (mkQGrading W n)).map (W.grading n).subtype
      = maxGradedIdeal W ⊓ W.grading n := by
  rw [mkQGrading, LinearMap.ker_domRestrict, Submodule.ker_mkQ, Submodule.map_comap_subtype,
    inf_comm]

theorem finrank_ker_mkQGrading (n : ℤ) :
    finrank ℂ (LinearMap.ker (mkQGrading W n))
      = finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ V) := by
  rw [← ker_mkQGrading (W := W) n]
  exact LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (W.grading n).subtype (Submodule.subtype_injective _) _)

/-- **D1 — THE BRIDGE.**  The level-`n` graded dimension of the **simple quotient**
`L(W) = W / maxGradedIdeal W` is the **rank** of the canonical level-`n` Gram matrix:

  `dim L(W)ₙ = rank (canGram hne hqp n e)`.

No hypothesis beyond the two that the canonical form needs (`𝟙 ≠ 0`, `L₁𝒱₁ = 0`) and a finite
basis `e` of `𝒱ₙ`; finite-dimensionality of `𝒱ₙ` is a *structure field* of
`VertexOperatorAlgebra`, so nothing has to be supplied for it.

⚠ Note which side is which.  `rank_canGram_add_finrank` measures the **radical**; this measures
the **quotient**.  They are complementary, and it is the quotient that is the simple VOA. -/
theorem finrank_maxQuotient_grading (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (n : ℤ) (e : Basis ι ℂ (W.grading n)) :
    finrank ℂ ((QuotVOA.maxQuotientVOA W).grading n) = (canGram hne hqp n e).rank := by
  haveI := W.finrank n
  have hrk : (canGram hne hqp n e).rank
      + finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ V)
      = finrank ℂ (W.grading n) := rank_canGram_add_finrank hne hqp n e
  have hrn : finrank ℂ (LinearMap.range (mkQGrading W n))
      + finrank ℂ (LinearMap.ker (mkQGrading W n)) = finrank ℂ (W.grading n) :=
    LinearMap.finrank_range_add_finrank_ker (mkQGrading W n)
  rw [range_mkQGrading, finrank_ker_mkQGrading] at hrn
  rw [maxQuotientVOA_grading_eq (W := W) n]
  omega

end Bridge

/-! ## §  The **dimension jump** at a degenerate parameter

Two immediate consequences of `rank_canGram_add_finrank` that the rigidity argument runs on.
They are the reason a determinant is enough to *detect* the jump even though a determinant does
not determine a rank: the determinant decides between "rank is full" and "rank is not full", and
that dichotomy alone already forces a strict inequality of graded dimensions. -/

section Jump

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- **Nondegenerate level.**  If the level-`n` determinant is nonzero, the rank is the *full*
graded dimension of `𝒱ₙ` — so, by `finrank_maxQuotient_grading`, `dim L(W)ₙ = dim 𝒱ₙ`. -/
theorem rank_canGram_eq_of_det_ne_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (n : ℤ) (e : Basis ι ℂ (W.grading n))
    (hdet : (canGram hne hqp n e).det ≠ 0) :
    (canGram hne hqp n e).rank = finrank ℂ (W.grading n) := by
  have hbot := (canGram_det_ne_zero_iff hne hqp n e).mp hdet
  have h := rank_canGram_add_finrank hne hqp n e
  rw [hbot] at h
  simpa using h

/-- **Degenerate level.**  If the level-`n` determinant vanishes, the rank is *strictly* smaller
than `dim 𝒱ₙ` — so `dim L(W)ₙ < dim 𝒱ₙ`.  This is the half that needs the radical to be a
*nonzero* finite-dimensional space, not merely a nonzero submodule. -/
theorem rank_canGram_lt_of_det_eq_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (n : ℤ) (e : Basis ι ℂ (W.grading n))
    (hdet : (canGram hne hqp n e).det = 0) :
    (canGram hne hqp n e).rank < finrank ℂ (W.grading n) := by
  haveI := W.finrank n
  have hne' : maxGradedIdeal W ⊓ W.grading n ≠ ⊥ := by
    intro hb; exact ((canGram_det_ne_zero_iff hne hqp n e).mpr hb) hdet
  haveI : FiniteDimensional ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ V) :=
    FiniteDimensional.of_injective
      (Submodule.inclusion (inf_le_right : maxGradedIdeal W ⊓ W.grading n ≤ W.grading n))
      (Submodule.inclusion_injective _)
  have hpos : 0 < finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ V) := by
    rcases Nat.eq_zero_or_pos
        (finrank ℂ (maxGradedIdeal W ⊓ W.grading n : Submodule ℂ V)) with h0 | h0
    · exact absurd (Submodule.finrank_eq_zero.mp h0) hne'
    · exact h0
  have h := rank_canGram_add_finrank hne hqp n e
  omega

/-- **The jump, stated on the simple quotient.**  At a degenerate level the graded dimension of
the simple quotient is strictly below the universal one. -/
theorem finrank_maxQuotient_grading_lt_of_det_eq_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (n : ℤ) (e : Basis ι ℂ (W.grading n))
    (hdet : (canGram hne hqp n e).det = 0) :
    finrank ℂ ((QuotVOA.maxQuotientVOA W).grading n) < finrank ℂ (W.grading n) := by
  rw [finrank_maxQuotient_grading hne hqp n e]
  exact rank_canGram_lt_of_det_eq_zero hne hqp n e hdet

/-- **No jump at a nondegenerate level**: the simple quotient has the full graded dimension. -/
theorem finrank_maxQuotient_grading_eq_of_det_ne_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (n : ℤ) (e : Basis ι ℂ (W.grading n))
    (hdet : (canGram hne hqp n e).det ≠ 0) :
    finrank ℂ ((QuotVOA.maxQuotientVOA W).grading n) = finrank ℂ (W.grading n) := by
  rw [finrank_maxQuotient_grading hne hqp n e]
  exact rank_canGram_eq_of_det_ne_zero hne hqp n e hdet

end Jump


/-! ## ⚠ The comparison with the top-mode (Shapovalov) form

`Core/RigidityBridge.shapForm` is the *top-mode* pairing `⟨a,b⟩ₖ = ε(a₍₂ₖ₋₁₎b)`.  It is a
**different form** from `gradedForm B n`, and the two are related only on **quasi-primary**
vectors, and then only **up to a sign**: with the unit normalisation `(𝟙|𝟙) = +1`, the identity
carries a factor `(-1)^n`.  A plain "`gradedForm = shapForm` on quasi-primaries" is therefore
true at the vacuum but false uniformly across all weights.

The underlying statement is `RigidBridge.invariantForm_eq_shapForm`.  The two lemmas here are its
`gradedForm`- and `gramMatrix`-level restatements, which is the vocabulary a Kac-determinant
computation actually works in. -/

section Shap

variable {B : InvariantForm W}

/-- **The signed comparison**, in `gradedForm` vocabulary: for a quasi-primary `a ∈ 𝒱ₙ`,
`gradedForm B n a b = (-1)^n · ⟨a,b⟩ₙ` for every `b ∈ 𝒱ₙ`. -/
theorem gradedForm_eq_signed_shapForm_of_quasiPrimary (hB : B.IsFullyInvariant)
    (hn : B.Normalized) (hvac : W.vacuum ≠ 0) {n : ℤ} (a : W.grading n)
    (hL1 : W.L 1 (a : 𝒱) = 0) (b : W.grading n) :
    gradedForm B n a b = (-1 : ℂ) ^ n * RigidBridge.shapForm W hvac n a b := by
  rw [LiRadical.gradedForm_apply]
  exact RigidBridge.invariantForm_eq_shapForm hB hn hvac a.2 hL1 b

/-- **Exactly when a `shapForm` Kac matrix may be reused.**  If *every* vector of the chosen
basis of `𝒱ₙ` is quasi-primary, then the Gram matrix of `gradedForm B n` is `(-1)^n` times
the matrix of `shapForm`.  In that case the two have the same rank, and a `shapForm` computation
may be fed to `rank_gramMatrix_add_finrank`.

⚠ The hypothesis is genuinely restrictive, and it is *not* a technicality.  At level `4` of a
Virasoro VOA it fails outright: `L₁L₋₄𝟙 = 5L₋₃𝟙` and `L₁L₋₂²𝟙 = 3L₋₃𝟙`, so the quasi-primary
subspace of `𝒱₄` is a single line and **no** basis of `𝒱₄` satisfies `hqp`.  There the two Gram
matrices are matrices of different forms whose determinants happen to differ by a constant — and
constants fix zero sets, not ranks.  See `Examples/VirasoroGram4`. -/
theorem gramMatrix_eq_signed_shapMatrix (hB : B.IsFullyInvariant) (hn : B.Normalized)
    (hvac : W.vacuum ≠ 0) (n : ℤ) (e : Basis ι ℂ (W.grading n))
    (hqp : ∀ i, W.L 1 ((e i : W.grading n) : 𝒱) = 0) :
    gramMatrix B n e
      = (-1 : ℂ) ^ n • LinearMap.BilinForm.toMatrix e (RigidBridge.shapForm W hvac n) := by
  ext i j
  rw [gramMatrix_apply, Matrix.smul_apply, LinearMap.BilinForm.toMatrix_apply, smul_eq_mul,
    ← LiRadical.gradedForm_apply B n (e i) (e j)]
  exact gradedForm_eq_signed_shapForm_of_quasiPrimary hB hn hvac (e i) (hqp i) (e j)

end Shap

end GramMat

end VOA
