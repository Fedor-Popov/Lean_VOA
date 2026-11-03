/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Rank-one transfer for positive Hermitian matrices

This file isolates the finite-dimensional linear algebra behind removing a single null direction
from a positive-definite Hermitian form.  For a positive-definite matrix `A` and a nonzero vector
`k`, put `x = A *ᵥ k` and `s = star k ⬝ᵥ x`.  The rank-one remainder is
`A - s⁻¹ • vecMulVec x (star x)`.

The main results give its completed-square identity, positive semidefiniteness, and exact
one-dimensional kernel.  They are independent of vertex-operator-algebra infrastructure.
-/

namespace VOA

open Matrix
open scoped ComplexOrder

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- The positive scalar paired with the direction removed by the rank-one update. -/
def rankOnePivotScalar (A : Matrix n n 𝕜) (k : n → 𝕜) : 𝕜 :=
  star k ⬝ᵥ (A *ᵥ k)

/-- The rank-one update which kills `k` when `A` is positive definite and `k` is nonzero. -/
def rankOneRemainder (A : Matrix n n 𝕜) (k : n → 𝕜) : Matrix n n 𝕜 :=
  A - (rankOnePivotScalar A k)⁻¹ •
    vecMulVec (A *ᵥ k) (star (A *ᵥ k))

/-- The vector left after removing the `A`-orthogonal projection onto `k`. -/
def rankOneComplement (A : Matrix n n 𝕜) (k y : n → 𝕜) : n → 𝕜 :=
  y - ((rankOnePivotScalar A k)⁻¹ * (star (A *ᵥ k) ⬝ᵥ y)) • k

theorem star_mulVec_dotProduct (hA : A.IsHermitian) (k y : n → 𝕜) :
    star (A *ᵥ k) ⬝ᵥ y = star k ⬝ᵥ (A *ᵥ y) := by
  calc
    star (A *ᵥ k) ⬝ᵥ y = (star k ᵥ* Aᴴ) ⬝ᵥ y := by rw [star_mulVec]
    _ = (star k ᵥ* A) ⬝ᵥ y := by rw [hA.eq]
    _ = star k ⬝ᵥ (A *ᵥ y) := by rw [dotProduct_mulVec]

theorem rankOnePivotScalar_star (hA : A.IsHermitian) (k : n → 𝕜) :
    star (rankOnePivotScalar A k) = rankOnePivotScalar A k := by
  have hd := star_dotProduct k (A *ᵥ k)
  calc
    star (rankOnePivotScalar A k) =
        star (star (star (A *ᵥ k) ⬝ᵥ k)) := by
      rw [rankOnePivotScalar, hd]
    _ = star (A *ᵥ k) ⬝ᵥ k := by rw [star_star]
    _ = rankOnePivotScalar A k := star_mulVec_dotProduct hA k k

theorem rankOnePivotScalar_pos (hA : A.PosDef) {k : n → 𝕜} (hk : k ≠ 0) :
    0 < rankOnePivotScalar A k :=
  hA.dotProduct_mulVec_pos hk

theorem rankOnePivotScalar_ne_zero (hA : A.PosDef) {k : n → 𝕜} (hk : k ≠ 0) :
    rankOnePivotScalar A k ≠ 0 :=
  ne_of_gt (rankOnePivotScalar_pos hA hk)

/-- The quadratic value of the rank-one remainder is the original positive quadratic form
evaluated on the complementary vector. -/
theorem rankOneRemainder_completedSquare (hA : A.PosDef) {k : n → 𝕜} (hk : k ≠ 0)
    (y : n → 𝕜) :
    star y ⬝ᵥ (rankOneRemainder A k *ᵥ y) =
      star (rankOneComplement A k y) ⬝ᵥ
        (A *ᵥ rankOneComplement A k y) := by
  let s := rankOnePivotScalar A k
  let b := star (A *ᵥ k) ⬝ᵥ y
  have hs : s ≠ 0 := rankOnePivotScalar_ne_zero hA hk
  have hsstar : star s = s := rankOnePivotScalar_star hA.isHermitian k
  have hb : star b = star y ⬝ᵥ (A *ᵥ k) := by
    have hd := star_dotProduct (A *ᵥ k) y
    dsimp [b]
    rw [hd]
    change star (star (star y ⬝ᵥ (A *ᵥ k))) = _
    rw [star_star]
  have hcross : star k ⬝ᵥ (A *ᵥ y) = b := by
    exact (star_mulVec_dotProduct hA.isHermitian k y).symm
  have hself : star k ⬝ᵥ (A *ᵥ k) = s := rfl
  have hastar : star (s⁻¹ * b) = s⁻¹ * star b := by
    change (starRingEnd 𝕜) (s⁻¹ * b) = s⁻¹ * star b
    simp only [map_mul, map_inv₀, starRingEnd_apply, hsstar]
  calc
    star y ⬝ᵥ (rankOneRemainder A k *ᵥ y) =
        star y ⬝ᵥ (A *ᵥ y) - s⁻¹ * b * star b := by
      change star y ⬝ᵥ
        ((A - s⁻¹ • vecMulVec (A *ᵥ k) (star (A *ᵥ k))) *ᵥ y) = _
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
        op_smul_eq_smul, dotProduct_sub, dotProduct_smul]
      rw [hb]
      ring
    _ = star (rankOneComplement A k y) ⬝ᵥ
        (A *ᵥ rankOneComplement A k y) := by
      change _ = star (y - (s⁻¹ * b) • k) ⬝ᵥ
        (A *ᵥ (y - (s⁻¹ * b) • k))
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul,
        dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      rw [← hb, hcross, hself, hastar]
      field_simp
      ring

/-- The rank-one remainder is positive semidefinite. -/
theorem rankOneRemainder_posSemidef (hA : A.PosDef) {k : n → 𝕜} (hk : k ≠ 0) :
    (rankOneRemainder A k).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply hA.isHermitian.sub
    apply (posSemidef_vecMulVec_self_star (A *ᵥ k)).isHermitian.smul
    exact IsSelfAdjoint.of_nonneg
      (inv_pos.mpr (rankOnePivotScalar_pos hA hk)).le
  · intro y
    rw [rankOneRemainder_completedSquare hA hk y]
    exact hA.posSemidef.dotProduct_mulVec_nonneg _

/-- The prescribed direction is killed by the rank-one remainder. -/
theorem rankOneRemainder_mulVec_self (hA : A.PosDef) {k : n → 𝕜} (hk : k ≠ 0) :
    rankOneRemainder A k *ᵥ k = 0 := by
  let s := rankOnePivotScalar A k
  have hs : s ≠ 0 := rankOnePivotScalar_ne_zero hA hk
  change (A - s⁻¹ • vecMulVec (A *ᵥ k) (star (A *ᵥ k))) *ᵥ k = 0
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul]
  rw [star_mulVec_dotProduct hA.isHermitian k k, smul_smul,
    show star k ⬝ᵥ (A *ᵥ k) = s by rfl,
    inv_mul_cancel₀ hs, one_smul, sub_self]

/-- The kernel of the rank-one remainder consists exactly of multiples of `k`. -/
theorem rankOneRemainder_mulVec_eq_zero_iff (hA : A.PosDef) {k y : n → 𝕜} (hk : k ≠ 0) :
    rankOneRemainder A k *ᵥ y = 0 ↔ y ∈ 𝕜 ∙ k := by
  constructor
  · intro hy
    have hq : star y ⬝ᵥ (rankOneRemainder A k *ᵥ y) = 0 := by rw [hy, dotProduct_zero]
    rw [rankOneRemainder_completedSquare hA hk y] at hq
    have hz : rankOneComplement A k y = 0 := by
      by_contra hz
      exact (ne_of_gt (hA.dotProduct_mulVec_pos hz)) hq
    rw [rankOneComplement, sub_eq_zero] at hz
    rw [Submodule.mem_span_singleton]
    exact ⟨_, hz.symm⟩
  · rw [Submodule.mem_span_singleton]
    rintro ⟨a, rfl⟩
    rw [Matrix.mulVec_smul, rankOneRemainder_mulVec_self hA hk, smul_zero]

/-- The kernel submodule of the rank-one remainder is the line spanned by `k`. -/
theorem rankOneRemainder_ker (hA : A.PosDef) {k : n → 𝕜} (hk : k ≠ 0) :
    LinearMap.ker (rankOneRemainder A k).mulVecLin = 𝕜 ∙ k := by
  ext y
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
    rankOneRemainder_mulVec_eq_zero_iff hA hk]

end VOA
