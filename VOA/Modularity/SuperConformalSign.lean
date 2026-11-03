/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperAutomorphism
import VOA.Modularity.SuperHalfSquareGrading

/-!
# The conformal sign of a half-integrally graded super VOA

For a super VOA whose **original** conformal weights lie in `1/2 * Z`, this file constructs
the automorphism

`kappa = exp(2 * pi * i * L(0))`.

The construction is algebraic: on the original doubled-weight summand `V_(d/2)`, `kappa` is
the scalar `(-1)^d`.  It therefore does not require an analytic exponential of an infinite
dimensional endomorphism.  The equality with the complex exponential is proved on every
homogeneous summand.

No spin--statistics relation is used.  In particular `kappa` need not be the parity
automorphism.  Both are even involutions and commute, but either can degenerate to the identity.
The subgroup they generate is consequently defined as an actual `Subgroup.closure`; no
cardinality-four assertion is made.

The grading in this file is always the original `L(0)` grading.  It is deliberately distinct
from the square-bracket grading by `L[0]` used later in Zhu recursion.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]

namespace SuperVertexOperatorAlgebra

variable (W : SuperVertexOperatorAlgebra VType)

/-! ## The doubled-weight phase -/

/-- The scalar by which `exp(2 * pi * i * L(0))` acts on original doubled weight `d`. -/
noncomputable def conformalPhase (d : ℤ) : ℂ := (-1 : ℂ) ^ d

@[simp] theorem conformalPhase_zero : conformalPhase 0 = 1 := by
  simp [conformalPhase]

/-- Every doubled-weight phase is a square root of one. -/
@[simp] theorem conformalPhase_mul_self (d : ℤ) :
    conformalPhase d * conformalPhase d = 1 := by
  rw [conformalPhase, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    show d + d = 2 * d by ring, zpow_mul]
  norm_num

/-- The doubled-weight phase is multiplicative under the ordinary mode-weight shift. -/
theorem conformalPhase_mode (d e n : ℤ) :
    conformalPhase (d + e - 2 * n - 2) = conformalPhase d * conformalPhase e := by
  rw [conformalPhase, conformalPhase, conformalPhase,
    show d + e - 2 * n - 2 = (d + e) + 2 * (-n - 1) by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

/-- The algebraic phase is the literal complex exponential at original weight `d/2`. -/
theorem conformalPhase_eq_exp (d : ℤ) :
    conformalPhase d =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((d : ℂ) / 2)) := by
  exact (GammaThetaStmt.tPhase_half d).symm

/-- A strictly half-integral original weight has phase `-1`. -/
theorem conformalPhase_eq_neg_one_of_not_two_dvd {d : ℤ} (hd : ¬ (2 ∣ d)) :
    conformalPhase d = -1 := by
  rw [conformalPhase_eq_exp]
  exact GammaThetaStmt.tPhase_half_of_odd hd

/-! ## The block-diagonal sign operator -/

/-- The conformal-sign map on one original doubled-weight summand. -/
noncomputable def conformalSignFamily (d : ℤ) :
    W.toSuperNearVOA.halfGrading d →ₗ[ℂ] VType :=
  conformalPhase d • (W.toSuperNearVOA.halfGrading d).subtype

/-- The block-diagonal endomorphism acting by `(-1)^d` on original weight `d/2`. -/
noncomputable def conformalSignEnd (hhalf : IsHalfIntegerGraded W) : End ℂ VType :=
  letI := SuperNearVOA.halfGradingDecomposition W hhalf
  (DFinsupp.lsum ℂ W.conformalSignFamily).comp
    (DirectSum.decomposeLinearEquiv W.toSuperNearVOA.halfGrading).toLinearMap

/-- On original doubled weight `d`, the conformal sign is the scalar `(-1)^d`. -/
theorem conformalSignEnd_of_mem_halfGrading (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {x : VType} (hx : x ∈ W.toSuperNearVOA.halfGrading d) :
    W.conformalSignEnd hhalf x = conformalPhase d • x := by
  letI := SuperNearVOA.halfGradingDecomposition W hhalf
  have hcollapse : W.conformalSignEnd hhalf x = W.conformalSignFamily d ⟨x, hx⟩ := by
    change (DFinsupp.lsum ℂ W.conformalSignFamily)
      (DirectSum.decompose W.toSuperNearVOA.halfGrading x) = _
    rw [DirectSum.decompose_of_mem W.toSuperNearVOA.halfGrading hx]
    exact DFinsupp.lsum_single ℂ W.conformalSignFamily d ⟨x, hx⟩
  rw [hcollapse]
  rfl

/-- The conformal-sign endomorphism is involutive. -/
theorem conformalSignEnd_involutive (hhalf : IsHalfIntegerGraded W) :
    Function.Involutive (W.conformalSignEnd hhalf) := by
  intro x
  classical
  letI := SuperNearVOA.halfGradingDecomposition W hhalf
  let dx := DirectSum.decompose W.toSuperNearVOA.halfGrading x
  have hxsum : x = ∑ d ∈ dx.support, (dx d : VType) :=
    (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading x).symm
  rw [hxsum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [W.conformalSignEnd_of_mem_halfGrading hhalf (dx d).2,
    map_smul, W.conformalSignEnd_of_mem_halfGrading hhalf (dx d).2,
    smul_smul, conformalPhase_mul_self, one_smul]

/-- The conformal-sign endomorphism as a linear equivalence. -/
noncomputable def conformalSignLinearEquiv (hhalf : IsHalfIntegerGraded W) :
    VType ≃ₗ[ℂ] VType :=
  LinearEquiv.ofBijective (W.conformalSignEnd hhalf)
    (W.conformalSignEnd_involutive hhalf).bijective

@[simp] theorem conformalSignLinearEquiv_apply (hhalf : IsHalfIntegerGraded W)
    (x : VType) : W.conformalSignLinearEquiv hhalf x = W.conformalSignEnd hhalf x := rfl

@[simp] theorem conformalSignLinearEquiv_symm_apply (hhalf : IsHalfIntegerGraded W)
    (x : VType) : (W.conformalSignLinearEquiv hhalf).symm x = W.conformalSignEnd hhalf x := by
  apply (W.conformalSignLinearEquiv hhalf).injective
  rw [LinearEquiv.apply_symm_apply, conformalSignLinearEquiv_apply,
    W.conformalSignEnd_involutive hhalf]

/-! ## Product and parity compatibility -/

/-- The conformal sign preserves an ordinary mode product of homogeneous original weights. -/
theorem conformalSignEnd_smul_homogeneous (hhalf : IsHalfIntegerGraded W)
    {d e : ℤ} {u v : VType}
    (hu : u ∈ W.toSuperNearVOA.halfGrading d)
    (hv : v ∈ W.toSuperNearVOA.halfGrading e) (n : ℤ) :
    W.conformalSignEnd hhalf (W.smul u n v) =
      W.smul (W.conformalSignEnd hhalf u) n (W.conformalSignEnd hhalf v) := by
  have huv : W.smul u n v ∈
      W.toSuperNearVOA.halfGrading (d + e - 2 * n - 2) := by
    have hmode := W.smul_mem_grading hu hv n
    change W.smul u n v ∈ W.grading (((d + e - 2 * n - 2 : ℤ) : ℂ) / 2)
    convert hmode using 1
    push_cast
    ring
  rw [W.conformalSignEnd_of_mem_halfGrading hhalf huv,
    W.conformalSignEnd_of_mem_halfGrading hhalf hu,
    W.conformalSignEnd_of_mem_halfGrading hhalf hv,
    W.smul_smul_left, W.smul_smul_right, smul_smul,
    conformalPhase_mode]

/-- The conformal sign preserves every ordinary mode product. -/
theorem conformalSignEnd_smul (hhalf : IsHalfIntegerGraded W)
    (u : VType) (n : ℤ) (v : VType) :
    W.conformalSignEnd hhalf (W.smul u n v) =
      W.smul (W.conformalSignEnd hhalf u) n (W.conformalSignEnd hhalf v) := by
  classical
  letI := SuperNearVOA.halfGradingDecomposition W hhalf
  let du := DirectSum.decompose W.toSuperNearVOA.halfGrading u
  let dv := DirectSum.decompose W.toSuperNearVOA.halfGrading v
  have husum : u = ∑ d ∈ du.support, (du d : VType) :=
    (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading u).symm
  have hvsum : v = ∑ e ∈ dv.support, (dv e : VType) :=
    (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading v).symm
  let leftMode (y : VType) : VType →ₗ[ℂ] VType :=
    { toFun := fun x => W.smul x n y
      map_add' := fun x z => W.smul_add_left x z n y
      map_smul' := fun c x => W.smul_smul_left c x n y }
  let rightMode (x : VType) : VType →ₗ[ℂ] VType :=
    { toFun := fun y => W.smul x n y
      map_add' := fun y z => W.smul_add_right x n y z
      map_smul' := fun c y => W.smul_smul_right x c n y }
  rw [husum, hvsum]
  have hmodeSum :
      W.smul (∑ d ∈ du.support, (du d : VType)) n
          (∑ e ∈ dv.support, (dv e : VType)) =
        ∑ d ∈ du.support, ∑ e ∈ dv.support,
          W.smul (du d : VType) n (dv e : VType) := by
    change leftMode (∑ e ∈ dv.support, (dv e : VType))
        (∑ d ∈ du.support, (du d : VType)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    change rightMode (du d : VType) (∑ e ∈ dv.support, (dv e : VType)) = _
    rw [map_sum]
    rfl
  have hmodeSignSum :
      W.smul (∑ d ∈ du.support, W.conformalSignEnd hhalf (du d : VType)) n
          (∑ e ∈ dv.support, W.conformalSignEnd hhalf (dv e : VType)) =
        ∑ d ∈ du.support, ∑ e ∈ dv.support,
          W.smul (W.conformalSignEnd hhalf (du d : VType)) n
            (W.conformalSignEnd hhalf (dv e : VType)) := by
    change leftMode
        (∑ e ∈ dv.support, W.conformalSignEnd hhalf (dv e : VType))
        (∑ d ∈ du.support, W.conformalSignEnd hhalf (du d : VType)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    change rightMode (W.conformalSignEnd hhalf (du d : VType))
        (∑ e ∈ dv.support, W.conformalSignEnd hhalf (dv e : VType)) = _
    rw [map_sum]
    rfl
  have hsignModeSum :
      W.conformalSignEnd hhalf
          (∑ d ∈ du.support, ∑ e ∈ dv.support,
            W.smul (du d : VType) n (dv e : VType)) =
        ∑ d ∈ du.support, ∑ e ∈ dv.support,
          W.conformalSignEnd hhalf (W.smul (du d : VType) n (dv e : VType)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [map_sum]
  have hsignUSum :
      W.conformalSignEnd hhalf (∑ d ∈ du.support, (du d : VType)) =
        ∑ d ∈ du.support, W.conformalSignEnd hhalf (du d : VType) := by
    rw [map_sum]
  have hsignVSum :
      W.conformalSignEnd hhalf (∑ e ∈ dv.support, (dv e : VType)) =
        ∑ e ∈ dv.support, W.conformalSignEnd hhalf (dv e : VType) := by
    rw [map_sum]
  rw [hmodeSum, hsignModeSum, hsignUSum, hsignVSum, hmodeSignSum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  exact W.conformalSignEnd_smul_homogeneous hhalf (du d).2 (dv e).2 n

/-- The conformal sign is even, independently of spin--statistics. -/
theorem conformalSignEnd_mem_parity (hhalf : IsHalfIntegerGraded W)
    {p : ZMod 2} {x : VType} (hx : x ∈ W.parity p) :
    W.conformalSignEnd hhalf x ∈ W.parity p := by
  classical
  letI := SuperNearVOA.halfGradingDecomposition W hhalf
  let dx := DirectSum.decompose W.toSuperNearVOA.halfGrading x
  have hxsum : x = ∑ d ∈ dx.support, (dx d : VType) :=
    (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading x).symm
  have hcomp : ∀ d : ℤ, (dx d : VType) ∈ W.parity p := by
    intro d
    have hpres : ∀ e : ℤ, ∀ y ∈ W.toSuperNearVOA.halfGrading e,
        W.toSuperNearVOA.parProj p y ∈ W.toSuperNearVOA.halfGrading e := by
      intro e y hy
      exact W.toSuperNearVOA.parProj_mem_grading p hy
    have hcomm := homogProj_comm W.toSuperNearVOA.halfGrading
      (W.toSuperNearVOA.parProj p) hpres d x
    rw [W.toSuperNearVOA.parProj_of_mem hx] at hcomm
    have hproj : homogProj W.toSuperNearVOA.halfGrading d x = (dx d : VType) := rfl
    rw [hproj] at hcomm
    rw [hcomm]
    exact W.toSuperNearVOA.parProj_mem p _
  rw [hxsum, map_sum]
  exact Submodule.sum_mem _ fun d _ => by
    rw [W.conformalSignEnd_of_mem_halfGrading hhalf (dx d).2]
    exact (W.parity p).smul_mem _ (hcomp d)

/-! ## The conformal-sign automorphism -/

/-- `kappa = exp(2 * pi * i * L(0))`, built from the original half-weight grading. -/
noncomputable def conformalSign (hhalf : IsHalfIntegerGraded W) : SuperAut W where
  toLinearEquiv := W.conformalSignLinearEquiv hhalf
  map_smul' := W.conformalSignEnd_smul hhalf
  map_vacuum := by
    have hv : W.vacuum ∈ W.toSuperNearVOA.halfGrading 0 := by
      change W.vacuum ∈ W.grading (((0 : ℤ) : ℂ) / 2)
      simpa using W.vacuum_mem
    rw [conformalSignLinearEquiv_apply,
      W.conformalSignEnd_of_mem_halfGrading hhalf hv, conformalPhase_zero, one_smul]
  map_omega := by
    have hw : W.conformalVector ∈ W.toSuperNearVOA.halfGrading 4 := by
      change W.conformalVector ∈ W.grading (((4 : ℤ) : ℂ) / 2)
      norm_num
      exact W.conformal_mem
    rw [conformalSignLinearEquiv_apply,
      W.conformalSignEnd_of_mem_halfGrading hhalf hw]
    norm_num [conformalPhase]
  map_parity' p x := by
    constructor
    · intro hx
      have hx' := W.conformalSignEnd_mem_parity hhalf hx
      simpa [conformalSignLinearEquiv_apply,
        W.conformalSignEnd_involutive hhalf x] using hx'
    · intro hx
      simpa [conformalSignLinearEquiv_apply] using
        W.conformalSignEnd_mem_parity hhalf hx

@[simp] theorem conformalSign_apply (hhalf : IsHalfIntegerGraded W) (x : VType) :
    W.conformalSign hhalf x = W.conformalSignEnd hhalf x := rfl

/-- On original doubled weight `d`, `kappa` is the scalar `(-1)^d`. -/
theorem conformalSign_of_mem_halfGrading (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {x : VType} (hx : x ∈ W.toSuperNearVOA.halfGrading d) :
    W.conformalSign hhalf x = conformalPhase d • x :=
  W.conformalSignEnd_of_mem_halfGrading hhalf hx

/-- On original doubled weight `d`, `kappa` is literally `exp(2 * pi * i * d/2)`. -/
theorem conformalSign_of_mem_halfGrading_eq_exp (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {x : VType} (hx : x ∈ W.toSuperNearVOA.halfGrading d) :
    W.conformalSign hhalf x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((d : ℂ) / 2)) • x := by
  rw [W.conformalSign_of_mem_halfGrading hhalf hx, conformalPhase_eq_exp]

/-- The conformal sign has order dividing two; exact order two requires a strict half weight. -/
@[simp] theorem conformalSign_sq (hhalf : IsHalfIntegerGraded W) :
    W.conformalSign hhalf ^ 2 = 1 := by
  apply SuperAut.ext
  apply LinearEquiv.ext
  intro x
  rw [pow_two, SuperAut.mul_apply, conformalSign_apply, conformalSign_apply,
    W.conformalSignEnd_involutive hhalf, SuperAut.one_apply]

theorem conformalSign_isOfFinOrder (hhalf : IsHalfIntegerGraded W) :
    IsOfFinOrder (W.conformalSign hhalf) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨2, by norm_num, W.conformalSign_sq hhalf⟩

/-- A strict half weight prevents the conformal sign from degenerating to the identity. -/
theorem conformalSign_ne_one_of_hasStrictHalfWeight
    (hhalf : IsHalfIntegerGraded W) (hstrict : HasStrictHalfWeight W) :
    W.conformalSign hhalf ≠ 1 := by
  rintro hkappa
  rcases hstrict with ⟨d, hd, hgrade⟩
  apply hgrade
  rw [eq_bot_iff]
  intro x hx
  have hfun := congrArg (fun a : SuperAut W => a x) hkappa
  change W.conformalSign hhalf x = (1 : SuperAut W) x at hfun
  rw [W.conformalSign_of_mem_halfGrading hhalf hx,
    conformalPhase_eq_neg_one_of_not_two_dvd hd, neg_one_smul,
    SuperAut.one_apply] at hfun
  have htwo : (2 : ℂ) • x = 0 := by
    rw [two_smul, ← neg_eq_iff_add_eq_zero]
    exact hfun
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- With a strict half weight, the conformal sign has exact order two. -/
theorem orderOf_conformalSign_eq_two
    (hhalf : IsHalfIntegerGraded W) (hstrict : HasStrictHalfWeight W) :
    orderOf (W.conformalSign hhalf) = 2 :=
  orderOf_eq_prime (W.conformalSign_sq hhalf)
    (W.conformalSign_ne_one_of_hasStrictHalfWeight hhalf hstrict)

/-- Every even super-VOA automorphism commutes with the parity automorphism. -/
theorem parityAut_commute (g : SuperAut W) : Commute W.parityAut g := by
  apply SuperAut.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := W.parityGrading.exists_parity_decomp x
  simp only [SuperAut.mul_apply, map_add, W.parityAut_homog hx₀,
    W.parityAut_homog hx₁, g.toLinearEquiv.map_smul,
    W.parityAut_homog (g.map_mem_parity hx₀),
    W.parityAut_homog (g.map_mem_parity hx₁)]

/-- `kappa` and the parity automorphism commute without spin--statistics. -/
theorem conformalSign_commute_parityAut (hhalf : IsHalfIntegerGraded W) :
    Commute (W.conformalSign hhalf) W.parityAut :=
  (W.parityAut_commute (W.conformalSign hhalf)).symm

/-! ## The generated sign subgroup -/

/-- The subgroup generated by the conformal and parity signs.

This definition retains all degeneracies: it can have fewer than four elements when either sign
is trivial or when the two signs coincide. -/
noncomputable def superSignSubgroup (hhalf : IsHalfIntegerGraded W) :
    Subgroup (SuperAut W) :=
  Subgroup.closure ({W.conformalSign hhalf, W.parityAut} : Set (SuperAut W))

theorem conformalSign_mem_superSignSubgroup (hhalf : IsHalfIntegerGraded W) :
    W.conformalSign hhalf ∈ W.superSignSubgroup hhalf :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem parityAut_mem_superSignSubgroup (hhalf : IsHalfIntegerGraded W) :
    W.parityAut ∈ W.superSignSubgroup hhalf :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end SuperVertexOperatorAlgebra

end VOA
