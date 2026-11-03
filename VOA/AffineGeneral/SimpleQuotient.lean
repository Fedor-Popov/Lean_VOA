/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.Virasoro
import VOA.AffineGeneral.WeightOne
import VOA.Core.QuotientVOA

/-!
# The simple affine VOA `L_k(𝔤)` for general `𝔤`

`simpleVOA D k hk` is the quotient of the universal affine VOA `affineVOA D k hk` by its maximal
graded ideal.  It is simple (`simpleVOA_isSimple`, using vacuum nonvanishing from relative PBW), and
its weight-one space is spanned by the images of the currents (`simple_grading_one_eq_range`) — the
`gen_weight_one` input of the Deligne capstone, for every `𝔤`.
-/

namespace VOA.AffineGeneral

open VOA.AffineLie

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)

/-- The maximal graded ideal of `V^k(𝔤)`. -/
def maxIdeal (k : ℂ) (hk : k + D.h ≠ 0) : Submodule ℂ (Vacuum D k) :=
  QuotVOA.maxGradedIdeal (affineVOA D k hk)

/-- **The simple affine VOA `L_k(𝔤)`.** -/
def simpleVOA (k : ℂ) (hk : k + D.h ≠ 0) : VertexOperatorAlgebra (Vacuum D k ⧸ maxIdeal D k hk) :=
  QuotVOA.maxQuotientVOA (affineVOA D k hk)

/-- `L_k(𝔤)` is simple (among all ideals). -/
theorem simpleVOA_isSimple (k : ℂ) (hk : k + D.h ≠ 0) : (simpleVOA D k hk).IsSimple :=
  QuotVOA.isSimple_maxQuotientVOA' (affineVOA D k hk) (vacuumA_ne_zero D k)

/-- The projection `V^k(𝔤) → L_k(𝔤)`. -/
def simpleProjection (k : ℂ) (hk : k + D.h ≠ 0) : Vacuum D k →ₗ[ℂ] Vacuum D k ⧸ maxIdeal D k hk :=
  (maxIdeal D k hk).mkQ

/-- The current states in `L_k(𝔤)`. -/
def simpleCurrentState (k : ℂ) (hk : k + D.h ≠ 0) : 𝔤 →ₗ[ℂ] Vacuum D k ⧸ maxIdeal D k hk :=
  (simpleProjection D k hk).comp (currentState D k)

/-- **The weight-one space of `L_k(𝔤)` is spanned by the currents.** -/
theorem simple_grading_one_eq_range (k : ℂ) (hk : k + D.h ≠ 0) :
    (simpleVOA D k hk).grading 1 = LinearMap.range (simpleCurrentState D k hk) := by
  change (gradingZA D k 1).map (simpleProjection D k hk) = _
  rw [grading_one_eq_range, simpleCurrentState, LinearMap.range_comp]

/-- The basis currents lie in weight one of `L_k(𝔤)`. -/
theorem simpleCurrentState_mem (k : ℂ) (hk : k + D.h ≠ 0) (i : ι) :
    simpleCurrentState D k hk (D.generator i) ∈ (simpleVOA D k hk).grading 1 := by
  rw [simple_grading_one_eq_range]
  exact ⟨_, rfl⟩

end

end VOA.AffineGeneral
