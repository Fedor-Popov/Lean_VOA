/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GradedBlock
import VOA.Modularity.SqWeightSpanning
import VOA.Core.InvariantFormFHL2

/-!
# The linearly extended square-bracket modes

Zhu defines `a[j]` first for ordinary-homogeneous `a`, and then extends linearly in `a`.
The old API exposed only the first half (`vSqZ W a k j`).  This file supplies the missing linear
extension over the canonical ordinary-weight decomposition.

It also audits the apparent bi-homogeneity shortcut in `IsGradedBlock.negTwo`: the conformal vector
satisfies `L[0]ω = 2ω - (c/12)𝟙`, so for nonzero central charge it is not square-homogeneous (when
the vacuum is nonzero).  Thus the old simultaneous round/square hypothesis can genuinely miss the
weight-two vector which generates the Virasoro part of the theory.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Linearity

variable (W : VertexOperatorAlgebra 𝒱)

/-- `vSqZ` is additive in its first slot when the ordinary-weight parameter is fixed. -/
theorem vSqZ_add_left (a b : 𝒱) (k : ℕ) (j : ℤ) :
    vSqZ W (a + b) k j = vSqZ W a k j + vSqZ W b k j := by
  ext v
  simp only [LinearMap.add_apply]
  rw [vSqZ_apply, vSqZ_apply, vSqZ_apply]
  have ha := sqModeZ_support_finite W a k j v
  have hb := sqModeZ_support_finite W b k j v
  simp only [map_add, mode_add, LinearMap.add_apply, smul_add]
  rw [finsum_add_distrib ha hb]

/-- `vSqZ` is homogeneous in its first slot when the ordinary-weight parameter is fixed. -/
theorem vSqZ_smul_left (c : ℂ) (a : 𝒱) (k : ℕ) (j : ℤ) :
    vSqZ W (c • a) k j = c • vSqZ W a k j := by
  ext v
  simp only [LinearMap.smul_apply]
  rw [vSqZ_apply, vSqZ_apply]
  have ha := sqModeZ_support_finite W a k j v
  simp only [map_smul, mode_smul, LinearMap.smul_apply]
  rw [smul_finsum' c ha]
  exact finsum_congr fun i => by
    simp only [smul_smul]
    congr 1
    ring

@[simp] theorem vSqZ_zero_left (k : ℕ) (j : ℤ) :
    vSqZ W (0 : 𝒱) k j = 0 := by
  have h := vSqZ_smul_left W (0 : ℂ) (0 : 𝒱) k j
  simpa using h

/-- The square mode on one ordinary-weight summand, valued in endomorphisms. -/
noncomputable def sqModeFamily (j : ℤ) (k : ℤ) :
    W.grading k →ₗ[ℂ] Module.End ℂ 𝒱 where
  toFun a := vSqZ W (a : 𝒱) k.toNat j
  map_add' a b := by
    exact vSqZ_add_left W (a : 𝒱) (b : 𝒱) k.toNat j
  map_smul' c a := by
    exact vSqZ_smul_left W c (a : 𝒱) k.toNat j

/-- Zhu's square-bracket mode `a[j]`, extended linearly over the ordinary grading of `a`. -/
noncomputable def sqMode (j : ℤ) : 𝒱 →ₗ[ℂ] Module.End ℂ 𝒱 :=
  by
    classical
    exact (DFinsupp.lsum ℂ (sqModeFamily W j)).comp
      (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

@[simp] theorem sqMode_apply (j : ℤ) (a v : 𝒱) :
    sqMode W j a v =
      (by
        classical
        exact ((DirectSum.decompose W.grading a).sum fun k ak =>
          vSqZ W (ak : 𝒱) k.toNat j) v) := by
  classical
  change ((DFinsupp.lsum ℂ (sqModeFamily W j))
    (DirectSum.decompose W.grading a)) v = _
  rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  rfl

/-- On an ordinary-homogeneous vector the linear extension is the original `vSqZ`. -/
theorem sqMode_of_mem_grading {k : ℤ} {a : 𝒱} (ha : a ∈ W.grading k) (j : ℤ) :
    sqMode W j a = vSqZ W a k.toNat j := by
  classical
  have hdec : DirectSum.decompose W.grading a =
      DirectSum.of (fun i => (W.grading i : Submodule ℂ 𝒱)) k ⟨a, ha⟩ :=
    DirectSum.decompose_coe (ℳ := fun i => (W.grading i : Submodule ℂ 𝒱)) ⟨a, ha⟩
  change (DFinsupp.lsum ℂ (sqModeFamily W j))
    (DirectSum.decompose W.grading a) = _
  rw [hdec]
  change (DFinsupp.lsum ℂ (sqModeFamily W j))
    (DFinsupp.single k ⟨a, ha⟩) = _
  rw [DFinsupp.lsum_single]
  rfl

end Linearity

section VacuityAudit

variable (W : VertexOperatorAlgebra 𝒱)

/-- The ordinary Virasoro mode `L₂` sends the conformal vector to `(c/2)𝟙`. -/
theorem L_two_conformalVector :
    W.L 2 W.conformalVector = (W.centralCharge / 2) • W.vacuum := by
  have hω : W.conformalVector = W.L (-2) W.vacuum := by
    rw [VertexOperatorAlgebra.L_def, show (-2 + 1 : ℤ) = -1 by ring,
      ← PreVertexAlgebra.smul_def, W.smul_vacuum_neg_one]
  have hL2vac : W.L 2 W.vacuum = 0 := by
    rw [VertexOperatorAlgebra.L_def, show (2 + 1 : ℤ) = 3 by ring,
      ← PreVertexAlgebra.smul_def,
      W.toPreVertexAlgebra.smul_vacuum_nonneg W.conformalVector (by norm_num : (0 : ℤ) ≤ 3)]
  have hL0vac : W.L 0 W.vacuum = 0 := by
    rw [W.L_zero_grading W.vacuum W.vacuum_mem_grading_zero, Int.cast_zero, zero_smul]
  have hbr := W.L_virasoro 2 (-2)
  rw [show (2 + (-2) : ℤ) = 0 by ring, if_pos rfl] at hbr
  rw [hω]
  have hcomm : W.L 2 (W.L (-2) W.vacuum)
      = (⁅W.L 2, W.L (-2)⁆ : Module.End ℂ 𝒱) W.vacuum
        + W.L (-2) (W.L 2 W.vacuum) := by
    rw [LieRing.of_associative_ring_bracket]
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    abel
  rw [hcomm, hbr, hL2vac, map_zero, add_zero, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, hL0vac, smul_zero,
    zero_add]
  norm_num
  ring_nf

/-- The audited formula behind the weight-two vacuity warning. -/
theorem Lsq_zero_conformalVector :
    Lsq W 0 W.conformalVector =
      (2 : ℂ) • W.conformalVector - (W.centralCharge / 12) • W.vacuum := by
  rw [Lsq_zero_apply]
  have hzero : ∀ a : ℤ, a < 0 →
      sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.L a W.conformalVector = 0 := by
    intro a ha
    rw [sqBracketCoeff_zero_of_neg ha, zero_smul]
  have hhigh : ∀ a : ℤ, 3 ≤ a →
      sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.L a W.conformalVector = 0 := by
    intro a ha
    have hmem := L_mem_grading W W.conformal_mem a
    have hneg : (2 : ℤ) - a < 0 := by omega
    rw [W.positivity (2 - a) hneg, Submodule.mem_bot] at hmem
    rw [hmem, smul_zero]
  have hsupp : Function.support (fun a : ℤ =>
      sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.L a W.conformalVector)
      ⊆ ({0, 1, 2} : Finset ℤ) := by
    intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hnot
    push Not at hnot
    rcases lt_or_ge a 0 with hneg | hnonneg
    · exact ha (hzero a hneg)
    · exact ha (hhigh a (by omega))
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  have hd0 : sqBracketCoeffZ 2 (0 + 1) (0 + 1) = 1 := sqBracketCoeff_zero_diag
  have hd1 : sqBracketCoeffZ 2 (0 + 1) (1 + 1) = (1 / 2 : ℂ) := by
    norm_num [sqBracketCoeffZ, onePlusXUnit_coe, uUnit_coe, uSeries,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, PowerSeries.coeff_X, Int.toNat_of_nonneg,
      show (2 : ℤ).toNat = 2 by rfl]
  have hd2 : sqBracketCoeffZ 2 (0 + 1) (2 + 1) = (-1 / 6 : ℂ) := by
    norm_num [sqBracketCoeffZ, onePlusXUnit_coe, uUnit_coe, uSeries,
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, PowerSeries.coeff_X, Int.toNat_of_nonneg,
      show (2 : ℤ).toNat = 2 by rfl]
  rw [Finset.sum_insert (by norm_num : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
    Finset.sum_insert (by norm_num : (1 : ℤ) ∉ ({2} : Finset ℤ)), Finset.sum_singleton,
    hd0, hd1, hd2]
  rw [W.L_zero_grading W.conformalVector W.conformal_mem, L1_conformal_zero,
    L_two_conformalVector, smul_zero]
  module

/-- If `c ≠ 0` and the vacuum is nonzero, the conformal vector is not an `L[0]`-eigenvector of
weight `2`; hence the old bi-homogeneous condition misses this canonical element of `𝒱₂`. -/
theorem conformalVector_not_mem_sqWeightSpace_two
    (hc : W.centralCharge ≠ 0) (hvac : W.vacuum ≠ 0) :
    W.conformalVector ∉ sqWeightSpace W (2 : ℂ) := by
  rw [mem_sqWeightSpace_iff, Lsq_zero_conformalVector]
  intro h
  have hz : (W.centralCharge / 12) • W.vacuum = 0 := by
    have h' : (2 : ℂ) • W.conformalVector =
        (2 : ℂ) • W.conformalVector + (W.centralCharge / 12) • W.vacuum :=
      sub_eq_iff_eq_add.mp h
    exact add_left_cancel (by simpa only [add_zero] using h'.symm)
  have hscalar : W.centralCharge / 12 = 0 := by
    by_contra hscalar
    have h := congrArg (fun x : 𝒱 => (W.centralCharge / 12)⁻¹ • x) hz
    simp only [smul_zero, smul_smul] at h
    have hone : (W.centralCharge / 12)⁻¹ * (W.centralCharge / 12) = (1 : ℂ) :=
      inv_mul_cancel₀ hscalar
    rw [hone, one_smul] at h
    exact hvac h
  apply hc
  norm_num at hscalar ⊢
  exact hscalar

/-- If the ordinary weight-two space is spanned by `ω`, its simultaneous ordinary/square
weight-two part is zero when `c ≠ 0` and the vacuum is nonzero. -/
theorem eq_zero_of_mem_grading_two_mem_sqWeightSpace_two
    (hc : W.centralCharge ≠ 0) (hvac : W.vacuum ≠ 0)
    (hgrade : W.grading (2 : ℤ) ≤ ℂ ∙ W.conformalVector) {a : 𝒱}
    (ha : a ∈ W.grading (2 : ℤ)) (hasq : a ∈ sqWeightSpace W (2 : ℂ)) : a = 0 := by
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp (hgrade ha)
  by_cases hd : d = 0
  · simp [hd]
  have hωsq : W.conformalVector ∈ sqWeightSpace W (2 : ℂ) := by
    have h := Submodule.smul_mem (sqWeightSpace W (2 : ℂ)) d⁻¹ hasq
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using h
  exact absurd hωsq (conformalVector_not_mem_sqWeightSpace_two W hc hvac)

end VacuityAudit

end VOA
