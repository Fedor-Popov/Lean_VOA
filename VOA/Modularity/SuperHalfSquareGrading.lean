/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Core.SuperEvenPart
import VOA.Core.SuperTranslationCovariance
import VOA.Modularity.GammaThetaStatement
import VOA.Modularity.SuperHalfWeightSquareBracket
import VOA.Modularity.SuperSquareBracketVirasoro

/-!
# Square-bracket grading for half-integrally graded super VOAs

Square-bracket modes are homogeneous only after the left state has been decomposed into its
ordinary conformal-weight components.  In the half-integral setting the honest index for that
decomposition is the doubled weight `d : ℤ`, representing `d / 2`.

This file constructs that restricted internal decomposition from the official
`IsHalfIntegerGraded` predicate and uses it to extend `superVSqHalf` linearly in its left state.
No parity decomposition is used: the coordinate change is even, so this construction introduces
no Koszul sign.

The square-weight spaces are the eigenspaces of `superLsq 0`.  Their independence is therefore
formal.  Their spanning is proved below from the triangularity of `superLsq 0` with respect to the
doubled ordinary-weight filtration.  In particular the carrier used by super Zhu descent is the
square-weight grading, not the original conformal grading: `L[-1] = L(-1) + L(0)` is not homogeneous
for the latter.

The companion square-translation identity is proved below from the complex-weight coefficient
recurrence

`(h-1-i)c(h,m,i) - (i+1)c(h,m,i+1) = -m c(h,m-1,i)`.

The next algebraic layer is deliberately not packaged as a hypothesis here.  Its remaining bulk
lemma must prove, for the global mode constructed below,

`[L[0], a[m]]v = (L[0]a)[m]v - (m+1)a[m]v`.

That identity implies the general square-weight mode shift.  The bosonic commutator calculation
cannot be reused through a coercion because a half-integral super VOA need not have an underlying
bosonic VOA; its parity-blind scalar part and its even-conformal-vector operator part are therefore
ported separately in `SuperHalfSquareCovariance`.  No conclusion-carrying field is introduced in
its place.
-/

namespace VOA

open scoped BigOperators
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]

namespace SuperNearVOA

variable (V : SuperNearVOA VType)

/-! ## The official doubled-weight decomposition -/

/-- The ordinary conformal-weight space of doubled weight `d`. -/
noncomputable def halfGrading (d : ℤ) : Submodule ℂ VType :=
  V.grading ((d : ℂ) / 2)

theorem halfWeight_injective : Function.Injective (fun d : ℤ => ((d : ℂ) / 2)) := by
  intro d e h
  change (d : ℂ) / 2 = (e : ℂ) / 2 at h
  have hz : (d : ℂ) - (e : ℂ) = 0 := by
    calc
      (d : ℂ) - (e : ℂ) = 2 * ((d : ℂ) / 2 - (e : ℂ) / 2) := by ring
      _ = 0 := by rw [h, sub_self, mul_zero]
  have hh : (d : ℂ) = (e : ℂ) := sub_eq_zero.mp hz
  exact_mod_cast hh

/-- Half-integrality restricts the ambient complex grading to an internal doubled-weight grading. -/
theorem halfGrading_isInternal (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    DirectSum.IsInternal W.toSuperNearVOA.halfGrading := by
  classical
  exact isInternal_comp_of_bot halfWeight_injective W.isInternal
    (fun h hh => hhalf h (by simpa only [not_exists] using hh))

/-- The canonical decomposition attached to the doubled-weight grading. -/
@[reducible] noncomputable def halfGradingDecomposition (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    DirectSum.Decomposition W.toSuperNearVOA.halfGrading :=
  (halfGrading_isInternal W hhalf).chooseDecomposition _

/-- The doubled-weight spaces span the state space. -/
theorem iSup_halfGrading_eq_top (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    (⨆ d : ℤ, W.toSuperNearVOA.halfGrading d) = ⊤ :=
  (halfGrading_isInternal W hhalf).submodule_iSup_eq_top

/-! ## A global square-bracket mode -/

/-- Additivity of a declared-weight square-bracket mode in the left state. -/
theorem superVSqC_add_left (a₁ a₂ : VType) (h : ℂ) (m : ℤ) :
    V.superVSqC (a₁ + a₂) h m = V.superVSqC a₁ h m + V.superVSqC a₂ h m := by
  ext b
  change (∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul (a₁ + a₂) i b) =
    (∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul a₁ i b) +
      ∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul a₂ i b
  simp only [SuperVertexAlgebra.smul_add_left, smul_add]
  rw [finsum_add_distrib (V.superSqModeC_support_finite a₁ h m b)
    (V.superSqModeC_support_finite a₂ h m b)]

/-- Homogeneity of a declared-weight square-bracket mode in the left state. -/
theorem superVSqC_smul_left (c : ℂ) (a : VType) (h : ℂ) (m : ℤ) :
    V.superVSqC (c • a) h m = c • V.superVSqC a h m := by
  ext b
  change (∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul (c • a) i b) =
    c • ∑ᶠ i : ℤ, sqBracketCoeffC h m i • V.smul a i b
  simp only [SuperVertexAlgebra.smul_smul_left]
  rw [smul_finsum' c (V.superSqModeC_support_finite a h m b)]
  exact finsum_congr fun i =>
    calc
      sqBracketCoeffC h m i • (c • V.smul a i b) =
          (sqBracketCoeffC h m i * c) • V.smul a i b :=
        smul_smul (sqBracketCoeffC h m i) c _
      _ = (c * sqBracketCoeffC h m i) • V.smul a i b := by rw [mul_comm]
      _ = c • (sqBracketCoeffC h m i • V.smul a i b) :=
        (smul_smul c (sqBracketCoeffC h m i) _).symm

/-! ### The complex-weight translation coefficient identity -/

open PowerSeries

/-- The elementary recurrence for the generalized complex binomial coefficient. -/
theorem cbinom_succ_mul (x : ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * cbinom x (n + 1) =
      (x - n) * cbinom x n := by
  rw [cbinom, cbinom, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- Formal differentiation of the complex binomial series. -/
theorem complexBinomialSeries_ode (x : ℂ) :
    (1 + X) * derivativeFun (complexBinomialSeries x) =
      PowerSeries.C x * complexBinomialSeries x := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_derivativeFun,
    coeff_X_mul_derivativeFun, PowerSeries.coeff_C_mul,
    coeff_complexBinomialSeries, coeff_complexBinomialSeries]
  have hrec := cbinom_succ_mul x n
  push_cast at hrec ⊢
  linear_combination hrec

/-- The generating series of the complex-weight coefficients `c(h,m,i)`. -/
noncomputable def superSqGenC (h : ℂ) (m : ℤ) : PowerSeries ℂ :=
  complexBinomialSeries (h - 1) *
    ((uUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)

theorem sqBracketCoeffC_eq_coeff_superSqGenC (h : ℂ) (m : ℤ) (d : ℕ) :
    sqBracketCoeffC h m (m + d) = coeff d (superSqGenC h m) := by
  rw [sqBracketCoeffC, if_pos (by omega)]
  have heq : (m + (d : ℤ) - m).toNat = d := by
    rw [show m + (d : ℤ) - m = (d : ℤ) by ring, Int.toNat_natCast]
  rw [heq]
  rfl

/-- The differential identity behind square translation at an arbitrary complex weight. -/
theorem superSqGenC_ode (h : ℂ) (m : ℤ) :
    X * (1 + X) * derivativeFun (superSqGenC h m) =
      PowerSeries.C (h - 1) * X * superSqGenC h m +
        PowerSeries.C (m : ℂ) * superSqGenC h (m - 1) -
          PowerSeries.C (m : ℂ) * (1 + X) * superSqGenC h m := by
  set A : PowerSeries ℂ := complexBinomialSeries (h - 1) with hA
  set U : PowerSeries ℂ :=
    ((uUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) with hU
  set U' : PowerSeries ℂ :=
    ((uUnit ^ (m - 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) with hU'
  have hGm : superSqGenC h m = A * U := by rw [superSqGenC, hA, hU]
  have hGm1 : superSqGenC h (m - 1) = A * U' := by
    rw [superSqGenC, hA, hU']
  have hUU : U = U' * uSeries := by
    rw [hU, hU', ← uUnit_coe, ← Units.val_mul, ← zpow_add_one, sub_add_cancel]
  have hAode : (1 + X) * derivativeFun A = PowerSeries.C (h - 1) * A := by
    rw [hA]
    exact complexBinomialSeries_ode (h - 1)
  have hUder : derivativeFun U =
      PowerSeries.C (m : ℂ) * U' * derivativeFun uSeries := by
    rw [hU, derivativeFun_uUnit_zpow, hU', map_intCast]
  have hODE := uSeries_ODE
  rw [hGm, hGm1, derivativeFun_mul]
  linear_combination (X * U) * hAode + (X * (1 + X) * A) * hUder +
    (PowerSeries.C (m : ℂ) * A * U') * hODE +
      (PowerSeries.C (m : ℂ) * (1 + X) * A) * hUU

/-- The `L[-1]` coefficient identity at arbitrary complex conformal weight. -/
theorem sqBracketCoeffC_derivation (h : ℂ) (m i : ℤ) :
    (h - 1 - i) * sqBracketCoeffC h m i -
        ((i : ℂ) + 1) * sqBracketCoeffC h m (i + 1) =
      -(m : ℂ) * sqBracketCoeffC h (m - 1) i := by
  rcases lt_trichotomy i (m - 1) with hlt | heq | hgt
  · rw [sqBracketCoeffC_of_lt h (by omega), sqBracketCoeffC_of_lt h (by omega),
      sqBracketCoeffC_of_lt h (by omega)]
    ring
  · subst heq
    rw [sqBracketCoeffC_of_lt h (by omega), show m - 1 + 1 = m by ring,
      sqBracketCoeffC_diag, sqBracketCoeffC_diag]
    push_cast
    ring
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, i = m + d := ⟨(i - m).toNat, by omega⟩
    subst hd
    rw [show m + (d : ℤ) + 1 = m + ((d + 1 : ℕ) : ℤ) by push_cast; ring,
      show m + (d : ℤ) = (m - 1) + ((d + 1 : ℕ) : ℤ) by push_cast; ring,
      sqBracketCoeffC_eq_coeff_superSqGenC,
      sqBracketCoeffC_eq_coeff_superSqGenC,
      show (m - 1) + ((d + 1 : ℕ) : ℤ) = m + (d : ℤ) by push_cast; ring,
      sqBracketCoeffC_eq_coeff_superSqGenC]
    have hcoeff := congrArg (coeff (d + 1)) (superSqGenC_ode h m)
    rw [map_sub, map_add] at hcoeff
    simp only [map_add, mul_assoc, mul_add, add_mul, one_mul,
      PowerSeries.coeff_C_mul, coeff_succ_X_mul, coeff_derivativeFun,
      coeff_X_mul_derivativeFun] at hcoeff
    push_cast
    linear_combination -hcoeff

/-- Raising the declared conformal weight by one multiplies the coefficient generating series
by `1 + X`. -/
theorem superSqGenC_add_one (h : ℂ) (m : ℤ) :
    superSqGenC (h + 1) m = (1 + PowerSeries.X) * superSqGenC h m := by
  rw [superSqGenC, superSqGenC,
    show h + 1 - 1 = (h - 1) + 1 by ring,
    complexBinomialSeries_add_one]
  rw [mul_assoc]

/-- Pascal relation for adjacent all-mode square-bracket coefficients. -/
theorem sqBracketCoeffC_add_one (h : ℂ) (m i : ℤ) :
    sqBracketCoeffC (h + 1) m (i + 1) =
      sqBracketCoeffC h m (i + 1) + sqBracketCoeffC h m i := by
  by_cases hi : i < m
  · by_cases hi1 : i + 1 < m
    · rw [sqBracketCoeffC_of_lt (h + 1) hi1,
        sqBracketCoeffC_of_lt h hi1, sqBracketCoeffC_of_lt h hi]
      ring
    · have him : i + 1 = m := by omega
      rw [him, sqBracketCoeffC_diag, sqBracketCoeffC_diag,
        sqBracketCoeffC_of_lt h hi, add_zero]
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, i = m + d :=
      ⟨(i - m).toNat, by omega⟩
    rw [show m + (d : ℤ) + 1 = m + ((d + 1 : ℕ) : ℤ) by push_cast; ring,
      sqBracketCoeffC_eq_coeff_superSqGenC,
      sqBracketCoeffC_eq_coeff_superSqGenC,
      sqBracketCoeffC_eq_coeff_superSqGenC,
      superSqGenC_add_one, add_mul, map_add,
      PowerSeries.coeff_succ_X_mul, one_mul]

/-! ### Square translation on a declared-weight state -/

/-- At bracket index zero and conformal weight two, only ordinary modes zero and one occur. -/
theorem sqBracketCoeffZ_two_zero_of_ne {i : ℤ} (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    sqBracketCoeffZ 2 0 i = 0 := by
  by_cases hneg : i < 0
  · exact sqBracketCoeffZ_of_lt 2 hneg
  · push Not at hneg
    obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hneg
    calc
      sqBracketCoeffZ 2 0 (r : ℤ) = sqBracketCoeff 2 0 r := by
        simpa only [Nat.cast_zero] using sqBracketCoeffZ_of_nonneg 2 0 r
      _ = ((1 : ℕ).choose r : ℂ) := sqBracketCoeff_zero 2 r (by norm_num)
      _ = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

theorem sqBracketCoeffZ_two_zero_zero : sqBracketCoeffZ 2 0 0 = 1 := by
  simpa using sqBracketCoeffZ_diag (-1)

theorem sqBracketCoeffZ_two_zero_one : sqBracketCoeffZ 2 0 1 = 1 := by
  calc
    sqBracketCoeffZ 2 0 1 = sqBracketCoeff 2 0 1 := by
      simpa only [Nat.cast_zero, Nat.cast_one] using sqBracketCoeffZ_of_nonneg 2 0 1
    _ = ((1 : ℕ).choose 1 : ℂ) := sqBracketCoeff_zero 2 1 (by norm_num)
    _ = 1 := by norm_num

/-- The super square Virasoro translation operator is `L(-1) + L(0)`. -/
theorem superLsq_neg_one (V : SuperNearVOA VType) :
    V.superLsq (-1) = V.L (-1) + V.L 0 := by
  ext x
  rw [Lsq_apply, show (-1 : ℤ) + 1 = 0 by norm_num,
    sqBracketCoeffZ_vacuum_of_ne 0 (by norm_num), mul_zero, zero_smul, sub_zero,
    show (0 : ℤ) = (-1 : ℤ) + 1 by norm_num, vSqZ_omega_apply V (-1) x]
  norm_num only
  have hsub : (Function.support fun a : ℤ =>
      sqBracketCoeffZ 2 0 (a + 1) • V.L a x) ⊆ ↑({-1, 0} : Finset ℤ) := by
    intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hmem
    push Not at hmem
    exact ha (by rw [sqBracketCoeffZ_two_zero_of_ne (by omega) (by omega), zero_smul])
  rw [finsum_eq_finsetSum_of_support_subset _ hsub, Finset.sum_pair (by norm_num),
    show (-1 : ℤ) + 1 = 0 by norm_num, zero_add,
    sqBracketCoeffZ_two_zero_zero, sqBracketCoeffZ_two_zero_one,
    one_smul, one_smul, LinearMap.add_apply]

/-- The ordinary `L(0)` commutator with a mode of a complex-weight homogeneous state. -/
theorem superL_zero_mode_comm {h : ℂ} {a : VType} (ha : a ∈ V.grading h)
    (v : VType) (i : ℤ) :
    V.L 0 (V.smul a i v) - V.smul a i (V.L 0 v) =
      (h - i - 1) • V.smul a i v := by
  obtain ⟨s, hs, -⟩ := V.exists_sum_wtProj v
  conv_lhs => rw [← hs]
  conv_rhs => rw [← hs]
  change V.L 0 (mode (V.Y a) i (∑ k ∈ s, V.wtProj k v)) -
      mode (V.Y a) i (V.L 0 (∑ k ∈ s, V.wtProj k v)) =
    (h - i - 1) • mode (V.Y a) i (∑ k ∈ s, V.wtProj k v)
  simp only [map_sum, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := V.wtProj_mem k v
  have hmode := V.smul_mem_grading ha hk i
  change V.L 0 (V.smul a i (V.wtProj k v)) -
      V.smul a i (V.L 0 (V.wtProj k v)) =
    (h - i - 1) • V.smul a i (V.wtProj k v)
  rw [V.L0_eigenvalue hmode, V.L0_eigenvalue hk,
    SuperVertexAlgebra.smul_smul_right]
  module

/-- Declared-weight square translation.  No Koszul sign occurs: the even Virasoro operator is
commuted past one mode, and no two state insertions are exchanged. -/
theorem superLsq_neg_one_superVSqC_comm {h : ℂ} {a : VType}
    (ha : a ∈ V.grading h) (m : ℤ) (v : VType) :
    V.superLsq (-1) (V.superVSqC a h m v) -
        V.superVSqC a h m (V.superLsq (-1) v) =
      (-(m : ℂ)) • V.superVSqC a h (m - 1) v := by
  have hcomm : ∀ i : ℤ,
      (V.L (-1) + V.L 0) (V.smul a i v) -
          V.smul a i ((V.L (-1) + V.L 0) v) =
        (-i : ℂ) • V.smul a (i - 1) v +
          (h - i - 1) • V.smul a i v := by
    intro i
    have h1 := V.L_neg_one_derivε a v i
    rw [V.smul_T_applyε] at h1
    rw [← Int.cast_smul_eq_zsmul ℂ] at h1
    rw [Int.cast_neg] at h1
    have h2 := V.superL_zero_mode_comm ha v i
    simp only [LinearMap.add_apply]
    rw [SuperVertexAlgebra.smul_add_right]
    rw [← h1, ← h2]
    abel
  have hfinL := V.superSqModeC_support_finite a h m v
  have hexp :
      V.superLsq (-1) (V.superVSqC a h m v) -
          V.superVSqC a h m (V.superLsq (-1) v) =
        ∑ᶠ i : ℤ, sqBracketCoeffC h m i •
          ((V.L (-1) + V.L 0) (V.smul a i v) -
            V.smul a i ((V.L (-1) + V.L 0) v)) := by
    rw [V.superLsq_neg_one, V.superVSqC_apply, V.superVSqC_apply,
      map_finsum _ hfinL]
    have hfinR := V.superSqModeC_support_finite a h m ((V.L (-1) + V.L 0) v)
    rw [← finsum_sub_distrib (by
      refine hfinL.subset fun i hi => ?_
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro hz
      exact hi (by rw [hz, map_zero])) hfinR]
    exact finsum_congr fun i => by rw [map_smul, smul_sub]
  rw [hexp]
  simp_rw [hcomm, smul_add]
  obtain ⟨R, hR⟩ := V.regularity a v
  have hfinA : (Function.support fun i : ℤ =>
      sqBracketCoeffC h m i • ((-i : ℂ) • V.smul a (i - 1) v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc m R) ?_
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    constructor
    · by_contra hc
      push Not at hc
      exact hi (by rw [sqBracketCoeffC_of_lt h hc, zero_smul])
    · by_contra hc
      push Not at hc
      have hz : V.smul a (i - 1) v = 0 := hR (i - 1) (by omega)
      exact hi (by rw [hz, smul_zero, smul_zero])
  have hfinB : (Function.support fun i : ℤ =>
      sqBracketCoeffC h m i • ((h - i - 1) • V.smul a i v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc m R) ?_
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    constructor
    · by_contra hc
      push Not at hc
      exact hi (by rw [sqBracketCoeffC_of_lt h hc, zero_smul])
    · by_contra hc
      push Not at hc
      have hz : V.smul a i v = 0 := hR i (by omega)
      exact hi (by rw [hz, smul_zero, smul_zero])
  rw [finsum_add_distrib hfinA hfinB]
  have hshift : (∑ᶠ i : ℤ,
      sqBracketCoeffC h m i • ((-i : ℂ) • V.smul a (i - 1) v)) =
      ∑ᶠ i : ℤ, sqBracketCoeffC h m (i + 1) •
        ((-(i + 1) : ℂ) • V.smul a i v) := by
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    refine finsum_congr fun i => by
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      push_cast
      ring_nf
  have hfinShift : (Function.support fun i : ℤ =>
      sqBracketCoeffC h m (i + 1) • ((-(i + 1) : ℂ) • V.smul a i v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc (m - 1) R) ?_
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    constructor
    · by_contra hc
      push Not at hc
      exact hi (by rw [sqBracketCoeffC_of_lt h (by omega), zero_smul])
    · by_contra hc
      push Not at hc
      have hz : V.smul a i v = 0 := hR i (by omega)
      exact hi (by rw [hz, smul_zero, smul_zero])
  rw [hshift, ← finsum_add_distrib hfinShift hfinB, V.superVSqC_apply,
    smul_finsum' (-(m : ℂ)) (V.superSqModeC_support_finite a h (m - 1) v)]
  exact finsum_congr fun i => by
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    have hc := sqBracketCoeffC_derivation h m i
    push_cast at hc ⊢
    linear_combination hc

/-- State-slot form of square translation on one declared ordinary-weight summand.  The two
summands are deliberately assigned their honest ordinary weights: `L(-1)a` has weight `h+1`,
whereas `L(0)a` remains in weight `h`. -/
theorem superLsq_neg_one_superVSqC_state {h : ℂ} {a : VType}
    (ha : a ∈ V.grading h) (m : ℤ) (v : VType) :
    V.superVSqC (V.L (-1) a) (h + 1) m v +
        V.superVSqC (V.L 0 a) h m v =
      (-(m : ℂ)) • V.superVSqC a h (m - 1) v := by
  rw [V.L0_eigenvalue ha]
  have hA :
      (∑ᶠ i : ℤ, sqBracketCoeffC (h + 1) m i •
          V.smul (V.L (-1) a) i v) =
        ∑ᶠ i : ℤ, sqBracketCoeffC (h + 1) m (i + 1) •
          ((-(i + 1) : ℂ) • V.smul a i v) := by
    simp_rw [V.smul_T_applyε, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg]
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    exact finsum_congr fun i => by
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      push_cast
      ring_nf
  obtain ⟨R, hR⟩ := V.regularity a v
  have hfinA : (Function.support fun i : ℤ =>
      sqBracketCoeffC (h + 1) m (i + 1) •
        ((-(i + 1) : ℂ) • V.smul a i v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc (m - 1) R) ?_
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    constructor
    · by_contra hc
      push Not at hc
      exact hi (by rw [sqBracketCoeffC_of_lt (h + 1) (by omega), zero_smul])
    · by_contra hc
      push Not at hc
      have hz : V.smul a i v = 0 := hR i (by omega)
      exact hi (by rw [hz, smul_zero, smul_zero])
  have hfinB : (Function.support fun i : ℤ =>
      sqBracketCoeffC h m i • (h • V.smul a i v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc m R) ?_
    intro i hi
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    constructor
    · by_contra hc
      push Not at hc
      exact hi (by rw [sqBracketCoeffC_of_lt h hc, zero_smul])
    · by_contra hc
      push Not at hc
      have hz : V.smul a i v = 0 := hR i (by omega)
      exact hi (by rw [hz, smul_zero, smul_zero])
  rw [V.superVSqC_apply, V.superVSqC_apply, V.superVSqC_apply, hA]
  simp_rw [SuperVertexAlgebra.smul_smul_left]
  rw [← finsum_add_distrib hfinA hfinB,
    smul_finsum' (-(m : ℂ)) (V.superSqModeC_support_finite a h (m - 1) v)]
  exact finsum_congr fun i => by
    rw [smul_smul, smul_smul, smul_smul, ← add_smul,
      sqBracketCoeffC_add_one]
    congr 1
    have hc := sqBracketCoeffC_derivation h m i
    push_cast at hc ⊢
    linear_combination hc

/-- The square-bracket mode on one doubled ordinary-weight summand. -/
noncomputable def superSqModeHalfFamily (m d : ℤ) :
    V.halfGrading d →ₗ[ℂ] Module.End ℂ VType where
  toFun a := V.superVSqHalf a d m
  map_add' a b := V.superVSqC_add_left (a : VType) (b : VType) (halfWeight d) m
  map_smul' c a := V.superVSqC_smul_left c (a : VType) (halfWeight d) m

/-- Zhu's square-bracket mode, extended linearly over the official half-weight decomposition. -/
noncomputable def superSqModeHalf (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (m : ℤ) :
    VType →ₗ[ℂ] Module.End ℂ VType := by
  letI := halfGradingDecomposition W hhalf
  exact (DFinsupp.lsum ℂ (W.toSuperNearVOA.superSqModeHalfFamily m)).comp
    (DirectSum.decomposeLinearEquiv W.toSuperNearVOA.halfGrading).toLinearMap

/-- On a doubled-weight homogeneous state, the global mode is the declared half-weight mode. -/
theorem superSqModeHalf_of_mem_halfGrading (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) {d : ℤ} {a : VType}
    (ha : a ∈ W.toSuperNearVOA.halfGrading d) (m : ℤ) :
    superSqModeHalf W hhalf m a =
      W.toSuperNearVOA.superVSqHalf a d m := by
  letI := halfGradingDecomposition W hhalf
  change (DFinsupp.lsum ℂ (W.toSuperNearVOA.superSqModeHalfFamily m))
    (DirectSum.decompose W.toSuperNearVOA.halfGrading a) = _
  rw [DirectSum.decompose_of_mem W.toSuperNearVOA.halfGrading ha]
  exact DFinsupp.lsum_single ℂ (W.toSuperNearVOA.superSqModeHalfFamily m) d ⟨a, ha⟩

/-- Global square translation on one ordinary half-weight summand. -/
theorem superLsq_neg_one_superSqModeHalf_comm_of_mem_halfGrading
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {a : VType} (ha : a ∈ W.toSuperNearVOA.halfGrading d)
    (m : ℤ) (v : VType) :
    W.toSuperNearVOA.superLsq (-1)
          (superSqModeHalf W hhalf m a v) -
        superSqModeHalf W hhalf m a (W.toSuperNearVOA.superLsq (-1) v) =
      (-(m : ℂ)) • superSqModeHalf W hhalf (m - 1) a v := by
  rw [superSqModeHalf_of_mem_halfGrading W hhalf ha m,
    superSqModeHalf_of_mem_halfGrading W hhalf ha (m - 1)]
  exact W.toSuperNearVOA.superLsq_neg_one_superVSqC_comm ha m v

/-- Square translation for the global half-weight mode, with no homogeneity hypothesis. -/
theorem superLsq_neg_one_superSqModeHalf_comm
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (a : VType) (m : ℤ) (v : VType) :
    W.toSuperNearVOA.superLsq (-1)
          (superSqModeHalf W hhalf m a v) -
        superSqModeHalf W hhalf m a (W.toSuperNearVOA.superLsq (-1) v) =
      (-(m : ℂ)) • superSqModeHalf W hhalf (m - 1) a v := by
  classical
  letI := halfGradingDecomposition W hhalf
  let da := DirectSum.decompose W.toSuperNearVOA.halfGrading a
  have ha_sum : a = ∑ d ∈ da.support, (da d : VType) := by
    exact (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading a).symm
  rw [ha_sum]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ =>
    superLsq_neg_one_superSqModeHalf_comm_of_mem_halfGrading W hhalf (da d).2 m v

/-- State-slot square translation on one doubled ordinary-weight summand. -/
theorem superSqModeHalf_superLsq_neg_one_of_mem_halfGrading
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {a : VType} (ha : a ∈ W.toSuperNearVOA.halfGrading d)
    (m : ℤ) (v : VType) :
    superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq (-1) a) v =
      (-(m : ℂ)) • superSqModeHalf W hhalf (m - 1) a v := by
  have hLneg : W.toSuperNearVOA.L (-1) a ∈
      W.toSuperNearVOA.halfGrading (d + 2) := by
    change W.toSuperNearVOA.smul W.conformalVector 0 a ∈
      W.toSuperNearVOA.grading (halfWeight (d + 2))
    have hm := W.toSuperNearVOA.smul_mem_grading W.conformal_mem ha 0
    convert hm using 1
    rw [halfWeight]
    push_cast
    ring
  have hLzero : W.toSuperNearVOA.L 0 a ∈
      W.toSuperNearVOA.halfGrading d := by
    rw [W.toSuperNearVOA.L0_eigenvalue ha]
    exact Submodule.smul_mem _ _ ha
  rw [W.toSuperNearVOA.superLsq_neg_one, LinearMap.add_apply, map_add,
    LinearMap.add_apply,
    superSqModeHalf_of_mem_halfGrading W hhalf hLneg m,
    superSqModeHalf_of_mem_halfGrading W hhalf hLzero m,
    superSqModeHalf_of_mem_halfGrading W hhalf ha (m - 1)]
  rw [superVSqHalf, superVSqHalf, superVSqHalf,
    show halfWeight (d + 2) = halfWeight d + 1 by
      rw [halfWeight, halfWeight]
      push_cast
      ring]
  exact W.toSuperNearVOA.superLsq_neg_one_superVSqC_state ha m v

/-- Global state-slot square translation.  No homogeneity or parity hypothesis remains. -/
theorem superSqModeHalf_superLsq_neg_one
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (a : VType) (m : ℤ) (v : VType) :
    superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq (-1) a) v =
      (-(m : ℂ)) • superSqModeHalf W hhalf (m - 1) a v := by
  classical
  letI := halfGradingDecomposition W hhalf
  let da := DirectSum.decompose W.toSuperNearVOA.halfGrading a
  have ha_sum : a = ∑ d ∈ da.support, (da d : VType) := by
    exact (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading a).symm
  rw [ha_sum]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun d _ =>
    superSqModeHalf_superLsq_neg_one_of_mem_halfGrading W hhalf (da d).2 m v

/-- Global half-weight square modes are eventually zero at natural indices. -/
theorem superSqModeHalf_nat_eventually_zero
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (a b : VType) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → superSqModeHalf W hhalf (k : ℤ) a b = 0 := by
  classical
  letI := halfGradingDecomposition W hhalf
  let da := DirectSum.decompose W.toSuperNearVOA.halfGrading a
  have hevent : ∀ d : ℤ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      W.toSuperNearVOA.superVSqC (da d : VType) (halfWeight d) (k : ℤ) b = 0 := by
    intro d
    obtain ⟨N, hN⟩ := W.toSuperNearVOA.regularity (da d : VType) b
    refine ⟨N.toNat, fun k hk => ?_⟩
    rw [W.toSuperNearVOA.superVSqC_apply]
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    rcases lt_or_ge i (k : ℤ) with hi | hi
    · rw [sqBracketCoeffC_of_lt (halfWeight d) hi, zero_smul]
    · have hz : W.toSuperNearVOA.smul (da d : VType) i b = 0 :=
        hN i (le_trans (by omega) hi)
      rw [hz, smul_zero]
  choose K hK using hevent
  refine ⟨da.support.sup K, fun k hk => ?_⟩
  have ha_sum : a = ∑ d ∈ da.support, (da d : VType) := by
    exact (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading a).symm
  rw [ha_sum]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rw [superSqModeHalf_of_mem_halfGrading W hhalf (da d).2]
  exact hK d k (le_trans (Finset.le_sup (f := K) hd) hk)

/-! ## Square-weight eigenspaces -/

/-- The square-bracket weight space of eigenvalue `k`. -/
noncomputable def superSqWeightSpace (k : ℂ) : Submodule ℂ VType :=
  Module.End.eigenspace (V.superLsq 0) k

theorem mem_superSqWeightSpace_iff (k : ℂ) (x : VType) :
    x ∈ V.superSqWeightSpace k ↔ V.superLsq 0 x = k • x :=
  Module.End.mem_eigenspace_iff

/-- Square-weight spaces are independent because they are eigenspaces of one endomorphism. -/
theorem superSqWeightSpace_iSupIndep : iSupIndep V.superSqWeightSpace :=
  Module.End.eigenspaces_iSupIndep _

/-! ## The doubled ordinary-weight filtration -/

/-- The span of all doubled ordinary-weight spaces of degree at most `d`. -/
noncomputable def halfGradeLE (W : SuperVertexOperatorAlgebra VType) (d : ℤ) :
    Submodule ℂ VType :=
  ⨆ j : {j : ℤ // j ≤ d}, W.toSuperNearVOA.halfGrading (j : ℤ)

theorem mem_halfGradeLE_of_mem_halfGrading (W : SuperVertexOperatorAlgebra VType)
    {j d : ℤ} (hjd : j ≤ d) {x : VType}
    (hx : x ∈ W.toSuperNearVOA.halfGrading j) : x ∈ halfGradeLE W d :=
  Submodule.mem_iSup_of_mem (⟨j, hjd⟩ : {j : ℤ // j ≤ d}) hx

theorem halfGradeLE_mono (W : SuperVertexOperatorAlgebra VType) {d e : ℤ}
    (hde : d ≤ e) : halfGradeLE W d ≤ halfGradeLE W e :=
  iSup_le fun j => le_iSup_of_le
    (⟨(j : ℤ), le_trans j.2 hde⟩ : {j : ℤ // j ≤ e}) le_rfl

/-- CFT positivity kills every strictly negative doubled-weight filtration step. -/
theorem halfGradeLE_eq_bot (W : SuperVertexOperatorAlgebra VType) {d : ℤ}
    (hd : d < 0) : halfGradeLE W d = ⊥ := by
  refine le_antisymm (iSup_le fun j => ?_) bot_le
  change W.grading ((j : ℂ) / 2) ≤ ⊥
  rw [W.positivity ((j : ℂ) / 2) ?_]
  have hj : (j : ℤ) < 0 := lt_of_le_of_lt j.2 hd
  norm_num
  exact div_neg_of_neg_of_pos (by exact_mod_cast hj) (by norm_num)

/-- Every state belongs to a finite doubled-weight filtration step. -/
theorem exists_mem_halfGradeLE (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) (x : VType) :
    ∃ d : ℤ, x ∈ halfGradeLE W d := by
  classical
  letI := halfGradingDecomposition W hhalf
  obtain ⟨D, hD⟩ := Finset.exists_le
    (DirectSum.decompose W.toSuperNearVOA.halfGrading x).support
  refine ⟨D, ?_⟩
  have hx : x = ∑ d ∈ (DirectSum.decompose W.toSuperNearVOA.halfGrading x).support,
      ((DirectSum.decompose W.toSuperNearVOA.halfGrading x) d : VType) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading x]
  rw [hx]
  exact Submodule.sum_mem _ fun d hd =>
    mem_halfGradeLE_of_mem_halfGrading W (hD d hd)
      ((DirectSum.decompose W.toSuperNearVOA.halfGrading x) d).2

/-- `L_m` lowers doubled ordinary weight by `2m`. -/
theorem superL_mem_halfGrading (W : SuperVertexOperatorAlgebra VType)
    {d : ℤ} {x : VType} (hx : x ∈ W.toSuperNearVOA.halfGrading d) (m : ℤ) :
    W.toSuperNearVOA.L m x ∈ W.toSuperNearVOA.halfGrading (d - 2 * m) := by
  have hmode := W.toSuperNearVOA.smul_mem_grading W.conformal_mem hx (m + 1)
  have heq : (2 : ℂ) + (d : ℂ) / 2 - (m + 1 : ℤ) - 1 =
      ((d - 2 * m : ℤ) : ℂ) / 2 := by
    push_cast
    ring
  change W.toSuperNearVOA.smul W.conformalVector (m + 1) x ∈
    W.grading (((d - 2 * m : ℤ) : ℂ) / 2)
  rw [← heq]
  exact hmode

/-- `halfGradeLE d` splits into its top degree and the strictly lower filtration. -/
theorem halfGradeLE_split (W : SuperVertexOperatorAlgebra VType) (d : ℤ) :
    halfGradeLE W d = W.toSuperNearVOA.halfGrading d ⊔ halfGradeLE W (d - 1) := by
  refine le_antisymm (iSup_le fun j => ?_)
    (sup_le (fun _ hx => mem_halfGradeLE_of_mem_halfGrading W le_rfl hx)
      (halfGradeLE_mono W (by omega)))
  rcases eq_or_lt_of_le j.2 with h | h
  · rw [h]
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup_of_le
      (⟨(j : ℤ), by omega⟩ : {j : ℤ // j ≤ d - 1}) le_rfl)

/-! ## Triangularity of `superLsq 0` -/

/-- `superLsq 0` has no vacuum correction. -/
theorem superLsq_zero_apply (W : SuperVertexOperatorAlgebra VType) (x : VType) :
    W.toSuperNearVOA.superLsq 0 x =
      ∑ᶠ a : ℤ, sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.toSuperNearVOA.L a x := by
  rw [Lsq_apply, sqBracketCoeffZ_vacuum_of_ne (0 + 1) (by norm_num), mul_zero,
    zero_smul, sub_zero, vSqZ_omega_apply]

/-- `superLsq 0` is diagonal on doubled degree `d` up to strictly lower degree. -/
theorem superLsq_zero_sub_smul_mem_halfGradeLE (W : SuperVertexOperatorAlgebra VType)
    {d : ℤ} {x : VType} (hx : x ∈ W.toSuperNearVOA.halfGrading d) :
    W.toSuperNearVOA.superLsq 0 x - ((d : ℂ) / 2) • x ∈ halfGradeLE W (d - 1) := by
  classical
  have hfin : (Function.support fun a : ℤ =>
      sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.toSuperNearVOA.L a x).Finite :=
    dL_support_finite W.toSuperNearVOA 0 x
  have hsub : (Function.support fun a : ℤ =>
      sqBracketCoeffZ 2 (0 + 1) (a + 1) • W.toSuperNearVOA.L a x) ⊆
      ↑(insert (0 : ℤ) hfin.toFinset) := by
    intro a ha
    simp only [Finset.coe_insert, Set.mem_insert_iff]
    exact Or.inr ((Set.Finite.mem_toFinset hfin).mpr ha)
  rw [superLsq_zero_apply, finsum_eq_finsetSum_of_support_subset _ hsub,
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self (0 : ℤ) hfin.toFinset),
    show sqBracketCoeffZ 2 (0 + 1) ((0 : ℤ) + 1) • W.toSuperNearVOA.L 0 x =
        ((d : ℂ) / 2) • x from by
      rw [sqBracketCoeffZ_diag, one_smul, W.toSuperNearVOA.L0_eigenvalue hx],
    add_sub_cancel_left]
  refine Submodule.sum_mem _ fun a ha => ?_
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  by_cases hneg : a < 0
  · rw [sqBracketCoeffZ_of_lt 2 (by omega), zero_smul]
    exact Submodule.zero_mem _
  · push Not at hneg
    exact Submodule.smul_mem _ _
      (mem_halfGradeLE_of_mem_halfGrading W (by omega)
        (superL_mem_halfGrading W hx a))

/-! ## Square-weight spanning -/

/-- Below a strictly larger doubled weight `d`, the operator `superLsq 0 - d/2` is surjective. -/
theorem superLsq_sub_halfWeight_surj (W : SuperVertexOperatorAlgebra VType) (d : ℤ) :
    ∀ (n : ℕ) (w : VType), w ∈ halfGradeLE W ((n : ℤ) - 1) →
      ((n : ℤ) - 1 < d) →
      ∃ y ∈ halfGradeLE W ((n : ℤ) - 1),
        W.toSuperNearVOA.superLsq 0 y - ((d : ℂ) / 2) • y = w := by
  intro n
  induction n with
  | zero =>
      intro w hw _
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num,
        halfGradeLE_eq_bot W (by norm_num)] at hw
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [(Submodule.mem_bot ℂ).mp hw, map_zero, smul_zero, sub_zero]
  | succ m ih =>
      intro w hw hlt
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring] at hw hlt ⊢
      rw [halfGradeLE_split W (m : ℤ)] at hw
      obtain ⟨wm, hwm, w', hw', rfl⟩ := Submodule.mem_sup.mp hw
      have hc : ((m : ℂ) / 2) - ((d : ℂ) / 2) ≠ 0 := by
        rw [sub_ne_zero]
        intro heq
        exact (by omega : (m : ℤ) ≠ d) (halfWeight_injective heq)
      set y₀ : VType := (((m : ℂ) / 2) - ((d : ℂ) / 2))⁻¹ • wm with hy₀def
      have hy₀mem : y₀ ∈ W.toSuperNearVOA.halfGrading (m : ℤ) :=
        Submodule.smul_mem _ _ hwm
      have hy₀c : (((m : ℂ) / 2) - ((d : ℂ) / 2)) • y₀ = wm := by
        rw [hy₀def, smul_smul, mul_inv_cancel₀ hc, one_smul]
      have hrem : W.toSuperNearVOA.superLsq 0 y₀ - ((m : ℂ) / 2) • y₀ ∈
          halfGradeLE W ((m : ℤ) - 1) :=
        superLsq_zero_sub_smul_mem_halfGradeLE W hy₀mem
      have hy₀eq : W.toSuperNearVOA.superLsq 0 y₀ - ((d : ℂ) / 2) • y₀ =
          wm + (W.toSuperNearVOA.superLsq 0 y₀ - ((m : ℂ) / 2) • y₀) := by
        rw [← hy₀c, sub_smul]
        abel
      obtain ⟨y₁, hy₁mem, hy₁eq⟩ :=
        ih (w' - (W.toSuperNearVOA.superLsq 0 y₀ - ((m : ℂ) / 2) • y₀))
          (Submodule.sub_mem _ hw' hrem) (by omega)
      refine ⟨y₀ + y₁, ?_, ?_⟩
      · exact Submodule.add_mem _
          (mem_halfGradeLE_of_mem_halfGrading W le_rfl hy₀mem)
          (halfGradeLE_mono W (by omega) hy₁mem)
      · rw [map_add, smul_add,
          show W.toSuperNearVOA.superLsq 0 y₀ + W.toSuperNearVOA.superLsq 0 y₁ -
              (((d : ℂ) / 2) • y₀ + ((d : ℂ) / 2) • y₁) =
            (W.toSuperNearVOA.superLsq 0 y₀ - ((d : ℂ) / 2) • y₀) +
              (W.toSuperNearVOA.superLsq 0 y₁ - ((d : ℂ) / 2) • y₁) by abel,
          hy₀eq, hy₁eq]
        abel

/-- Every doubled ordinary-weight filtration step is spanned by square-weight eigenspaces. -/
theorem halfGradeLE_le_iSup_superSqWeightSpace (W : SuperVertexOperatorAlgebra VType) :
    ∀ n : ℕ, halfGradeLE W ((n : ℤ) - 1) ≤
      ⨆ k : ℂ, W.toSuperNearVOA.superSqWeightSpace k := by
  intro n
  induction n with
  | zero =>
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num,
        halfGradeLE_eq_bot W (by norm_num)]
      exact bot_le
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring,
        halfGradeLE_split W (m : ℤ)]
      refine sup_le (fun x hx => ?_) ih
      have hw := superLsq_zero_sub_smul_mem_halfGradeLE W hx
      obtain ⟨y, hymem, hyeq⟩ :=
        superLsq_sub_halfWeight_surj W (m : ℤ) m
          (W.toSuperNearVOA.superLsq 0 x - ((m : ℂ) / 2) • x)
          (by simpa only using hw) (by omega)
      have hymem' : y ∈ halfGradeLE W ((m : ℤ) - 1) := by
        simpa only using hymem
      have heig : x - y ∈ W.toSuperNearVOA.superSqWeightSpace ((m : ℂ) / 2) := by
        rw [W.toSuperNearVOA.mem_superSqWeightSpace_iff, map_sub, smul_sub]
        have hcast : (((m : ℤ) : ℂ) / 2) = ((m : ℂ) / 2) := by norm_num
        rw [hcast] at hyeq
        linear_combination (norm := abel) -hyeq
      rw [show x = (x - y) + y by abel]
      exact Submodule.add_mem _
        (Submodule.mem_iSup_of_mem ((m : ℂ) / 2) heig) (ih hymem')

/-- The square-weight eigenspaces span a half-integrally graded super VOA. -/
theorem iSup_superSqWeightSpace_eq_top (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    (⨆ k : ℂ, W.toSuperNearVOA.superSqWeightSpace k) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨d, hd⟩ := exists_mem_halfGradeLE W hhalf x
  exact halfGradeLE_le_iSup_superSqWeightSpace W (d + 1).toNat
    (halfGradeLE_mono W (show d ≤ (((d + 1).toNat : ℤ)) - 1 by omega) hd)

/-- The square-weight eigenspaces form an internal grading. -/
theorem superSqWeightSpace_isInternal (W : SuperVertexOperatorAlgebra VType)
    (hhalf : IsHalfIntegerGraded W) :
    DirectSum.IsInternal W.toSuperNearVOA.superSqWeightSpace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    W.toSuperNearVOA.superSqWeightSpace_iSupIndep
    (iSup_superSqWeightSpace_eq_top W hhalf)

/-! ## Square-Virasoro weight shifts -/

/-- The square Virasoro operator `L[n]` shifts square weight by `-n`. -/
theorem superLsq_mem_superSqWeightSpace {K : ℂ} {a : VType}
    (ha : a ∈ V.superSqWeightSpace K) (n : ℤ) :
    V.superLsq n a ∈ V.superSqWeightSpace (K - n) := by
  rw [V.mem_superSqWeightSpace_iff] at ha ⊢
  have hcomm := superLsq_virasoro_apply V 0 n a
  simp only [zero_sub, Int.cast_neg, zero_add, neg_smul, Int.cast_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self, zero_div, zero_mul,
    ite_self, zero_smul, add_zero] at hcomm
  rw [ha, map_smul] at hcomm
  rw [sub_eq_iff_eq_add] at hcomm
  rw [hcomm, sub_smul]
  module

/-- In particular `L[-1]` raises square weight by one.  This replaces the false assertion that it
raises the original conformal weight: `L[-1] = L(-1) + L(0)` is triangular, not homogeneous, for
the original grading. -/
theorem superLsq_neg_one_mem_superSqWeightSpace {K : ℂ} {a : VType}
    (ha : a ∈ V.superSqWeightSpace K) :
    V.superLsq (-1) a ∈ V.superSqWeightSpace (K + 1) := by
  simpa only [Int.cast_neg, Int.cast_one, sub_neg_eq_add] using
    V.superLsq_mem_superSqWeightSpace ha (-1)

end SuperNearVOA

end VOA
