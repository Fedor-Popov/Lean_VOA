/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperHalfSquareGrading
import VOA.Modularity.SqModeWeight

/-!
# Square-weight covariance for half-integrally graded super VOAs

This file ports the square-bracket `L[0]` commutator from integral bosonic weights to arbitrary
complex declared weights, and then assembles it over the official doubled half-weight grading.

The only state moved through another mode is the conformal vector.  It has parity zero, so its
Koszul factor is `koszul 0 p = 1`; every operator identity below is therefore the ordinary
commutator identity, even when the inserted state is odd.
-/

namespace VOA

open PowerSeries
open scoped BigOperators
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]

/-! ## Complex-weight scalar collapses -/

/-- Multiplication by `(1+X)^{-q}` lowers a complex binomial exponent by `q`. -/
theorem onePlusXUnit_neg_nat_mul_complexBinomialSeries (h : ℂ) (q : ℕ) :
    (↑(onePlusXUnit ^ (-(q : ℤ))) : PowerSeries ℂ) * complexBinomialSeries h =
      complexBinomialSeries (h - q) := by
  induction q generalizing h with
  | zero => simp
  | succ q ih =>
      have hstep :
          (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) *
              complexBinomialSeries h = complexBinomialSeries (h - 1) := by
        calc
          (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) *
                complexBinomialSeries h
              = (↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) *
                  ((1 + X) * complexBinomialSeries (h - 1)) := by
                    rw [← complexBinomialSeries_add_one]
                    congr 2
                    ring
          _ = complexBinomialSeries (h - 1) := by
                rw [← onePlusXUnit_coe, ← mul_assoc, ← Units.val_mul,
                  zpow_neg_one, inv_mul_cancel, Units.val_one, one_mul]
      calc
        (↑(onePlusXUnit ^ (-((q + 1 : ℕ) : ℤ))) : PowerSeries ℂ) *
              complexBinomialSeries h
            = (↑(onePlusXUnit ^ (-(q : ℤ))) : PowerSeries ℂ) *
                ((↑(onePlusXUnit ^ (-1 : ℤ)) : PowerSeries ℂ) *
                  complexBinomialSeries h) := by
                    rw [← mul_assoc, ← Units.val_mul, ← zpow_add]
                    congr 2
                    push_cast
                    ring
        _ = (↑(onePlusXUnit ^ (-(q : ℤ))) : PowerSeries ℂ) *
              complexBinomialSeries (h - 1) := by rw [hstep]
        _ = complexBinomialSeries (h - ((q + 1 : ℕ) : ℂ)) := by
              rw [ih (h - 1)]
              congr 1
              push_cast
              ring

/-- The positive Virasoro outer moment lowers an arbitrary complex declared weight. -/
theorem sqOuterMoment_mul_superSqGenC {q : ℕ} (hq : 1 ≤ q) (h : ℂ) (m : ℤ) :
    sqOuterMoment q * SuperNearVOA.superSqGenC h m =
      sqBracketCoeffZ 2 1 ((q + 1 : ℕ) : ℤ) •
        SuperNearVOA.superSqGenC (h - q) m := by
  rw [sqOuterMoment_eq_smul_onePlusXUnit_zpow hq]
  simp only [SuperNearVOA.superSqGenC, smul_mul_assoc]
  rw [← mul_assoc, onePlusXUnit_neg_nat_mul_complexBinomialSeries]
  congr 2
  ring

/-- Complex-weight positive-tail coefficient collapse. -/
theorem sqBracketCoeffC_gBinom_collapse {q : ℕ} (hq : 1 ≤ q)
    (h : ℂ) (m : ℤ) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 1),
        (sqBracketCoeffZ 2 1 ((s + q + 1 : ℕ) : ℤ)
          * gBinom ((s + q + 1 : ℕ) : ℤ) (q + 1))
          * sqBracketCoeffC h m (m + ((t - s : ℕ) : ℤ))
      = sqBracketCoeffZ 2 1 ((q + 1 : ℕ) : ℤ)
          * sqBracketCoeffC (h - q) m (m + (t : ℤ)) := by
  have hc := congrArg (coeff t) (sqOuterMoment_mul_superSqGenC hq h m)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    map_smul] at hc
  simp_rw [coeff_sqOuterMoment] at hc
  have hgen : ∀ (H : ℂ) (n : ℕ), coeff n (SuperNearVOA.superSqGenC H m) =
      sqBracketCoeffC H m (m + (n : ℤ)) := by
    intro H n
    exact (SuperNearVOA.sqBracketCoeffC_eq_coeff_superSqGenC H m n).symm
  simpa only [hgen] using hc

/-- The combined `L(-1)`/`L(0)` scalar identity at an arbitrary complex declared weight. -/
theorem sqLowPair_powerSeriesC (h : ℂ) (m : ℤ) :
    PowerSeries.C h * derivativeFun (X * Pw 0) * SuperNearVOA.superSqGenC h m
        - PowerSeries.C ((m : ℂ) + 1) * Pw 0 * SuperNearVOA.superSqGenC h m
        - X * derivativeFun (Pw 0 * SuperNearVOA.superSqGenC h m)
      = PowerSeries.C (h - (m : ℂ) - 1) * SuperNearVOA.superSqGenC h m := by
  let G := SuperNearVOA.superSqGenC h m
  change PowerSeries.C h * derivativeFun (X * Pw 0) * G
        - PowerSeries.C ((m : ℂ) + 1) * Pw 0 * G
        - X * derivativeFun (Pw 0 * G)
      = PowerSeries.C (h - (m : ℂ) - 1) * G
  have hD : Pw 0 = (1 + X) * uSeries := by
    rw [Pw, zero_add, zpow_one, uUnit_coe]
  have hA : complexBinomialSeries h =
      (1 + X) * complexBinomialSeries (h - 1) := by
    rw [← complexBinomialSeries_add_one]
    congr 1
    ring
  have hU : (↑(uUnit ^ (m + 1)) : PowerSeries ℂ) =
      uSeries * (↑(uUnit ^ m) : PowerSeries ℂ) := by
    calc
      (↑(uUnit ^ (m + 1)) : PowerSeries ℂ) = ↑(uUnit ^ (1 + m)) := by
        congr 2 <;> ring
      _ = _ := by rw [zpow_add, Units.val_mul, zpow_one, uUnit_coe]
  have hDG : Pw 0 * G = SuperNearVOA.superSqGenC (h + 1) (m + 1) := by
    dsimp only [G]
    rw [hD, SuperNearVOA.superSqGenC, SuperNearVOA.superSqGenC]
    rw [show h + 1 - 1 = h by ring, hA, hU]
    ring
  have hGj : (1 + X) * G = SuperNearVOA.superSqGenC (h + 1) m := by
    dsimp only [G]
    rw [SuperNearVOA.superSqGenC, SuperNearVOA.superSqGenC]
    rw [show h + 1 - 1 = h by ring, hA]
    ring
  have hHG : (1 + X) * (derivativeFun (X * Pw 0) * G) - X * (Pw 0 * G)
      = (1 + X) * G := by
    rw [derivativeFun_X_mul_Pw_zero, hD]
    ring
  have hode := SuperNearVOA.superSqGenC_ode (h + 1) (m + 1)
  rw [show h + 1 - 1 = h by ring, show m + 1 - 1 = m by ring,
    ← hDG, ← hGj] at hode
  refine mul_left_cancel₀ (show (1 + X : PowerSeries ℂ) ≠ 0 by
    rw [← onePlusXUnit_coe]
    exact Units.ne_zero onePlusXUnit) ?_
  push_cast at hode ⊢
  simp only [map_sub, map_add, map_one] at hode ⊢
  linear_combination (PowerSeries.C h) * hHG - hode

/-- Coefficient form of the complex-weight low-pair collapse. -/
theorem sqBracketCoeffC_low_pair_collapse (h : ℂ) (m : ℤ) (t : ℕ) :
    ∑ r ∈ Finset.range (t + 1),
        sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + ((t - r : ℕ) : ℤ))
          * (h * ((r : ℂ) + 1) - ((m : ℂ) + (t : ℂ) + 1))
      = (h - (m : ℂ) - 1) * sqBracketCoeffC h m (m + (t : ℤ)) := by
  have hps := sqLowPair_powerSeriesC h m
  rw [show PowerSeries.C h * derivativeFun (X * Pw 0) *
        SuperNearVOA.superSqGenC h m =
          PowerSeries.C h * (derivativeFun (X * Pw 0) *
            SuperNearVOA.superSqGenC h m) by ring,
      show PowerSeries.C ((m : ℂ) + 1) * Pw 0 *
        SuperNearVOA.superSqGenC h m =
          PowerSeries.C ((m : ℂ) + 1) *
            (Pw 0 * SuperNearVOA.superSqGenC h m) by ring] at hps
  have hc := congrArg (coeff t) hps
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_X_mul_derivativeFun, PowerSeries.coeff_C_mul] at hc
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  have hDcoeff : ∀ r : ℕ, coeff r (Pw 0) =
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) := by
    intro r
    have hd := sqBracketCoeffZ_two_eq_coeff_Pw (0 : ℤ) (r : ℤ)
    norm_num at hd
    exact hd.symm
  have hHcoeff : ∀ r : ℕ, coeff r (derivativeFun (X * Pw 0)) =
      ((r : ℂ) + 1) * sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) := by
    intro r
    rw [coeff_derivativeFun, coeff_succ_X_mul, hDcoeff]
    push_cast
    ring
  have hGcoeff : ∀ n : ℕ, coeff n (SuperNearVOA.superSqGenC h m) =
      sqBracketCoeffC h m (m + (n : ℤ)) := by
    intro n
    exact (SuperNearVOA.sqBracketCoeffC_eq_coeff_superSqGenC h m n).symm
  simp_rw [hDcoeff, hHcoeff, hGcoeff] at hc
  push_cast at hc ⊢
  have hrange : Finset.range (t + 1) = Finset.range t.succ := rfl
  rw [hrange]
  let A : ℕ → ℂ := fun r ↦ sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
    * sqBracketCoeffC h m (m + ((t - r : ℕ) : ℤ))
  have hlead : ∑ r ∈ Finset.range t.succ,
        A r * (h * ((r : ℂ) + 1))
      = h * ∑ r ∈ Finset.range t.succ,
          ((r : ℂ) + 1) * sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
            * sqBracketCoeffC h m (m + ((t - r : ℕ) : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [A]
    ring
  have hconst : ∑ r ∈ Finset.range t.succ,
        A r * ((m : ℂ) + (t : ℂ) + 1)
      = ((m : ℂ) + 1) * ∑ r ∈ Finset.range t.succ, A r
          + (t : ℂ) * ∑ r ∈ Finset.range t.succ, A r := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  change (∑ r ∈ Finset.range t.succ,
      A r * (h * ((r : ℂ) + 1) - ((m : ℂ) + (t : ℂ) + 1))) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hlead, hconst]
  dsimp only [A]
  simpa only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg, neg_add_rev,
    add_assoc, add_comm, add_left_comm] using hc

/-- Module-valued complex-weight low-pair collapse. -/
theorem sqLowPairC_vector_collapse {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (h : ℂ) (m : ℤ) (x : ℕ → M) (hx : (Function.support x).Finite) :
    (∑ᶠ p : ℕ × ℕ,
        (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + (p.2 : ℤ))
          * (h * ((p.1 : ℂ) + 1)
            - ((m : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) • x (p.1 + p.2))
      = ∑ᶠ t : ℕ,
          ((h - (m : ℂ) - 1) * sqBracketCoeffC h m (m + (t : ℤ))) • x t := by
  rw [finsum_prod_eq_finsum_antidiagonal_sq _
    (support_pair_smul_add_finite _ x hx)]
  refine finsum_congr fun t ↦ ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hc := sqBracketCoeffC_low_pair_collapse h m t
  rw [← hc, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r hr
  have hrt : r ≤ t := by rw [Finset.mem_range] at hr; omega
  rw [Nat.add_sub_of_le hrt]

/-- Module-valued complex-weight positive-tail collapse for fixed `q ≥ 1`. -/
theorem sqPositiveTailC_vector_collapse {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {q : ℕ} (hq : 1 ≤ q) (h : ℂ) (m : ℤ)
    (x : ℕ → M) (hx : (Function.support x).Finite) :
    (∑ᶠ p : ℕ × ℕ,
        ((sqBracketCoeffZ 2 1 ((p.1 + q + 1 : ℕ) : ℤ)
          * gBinom ((p.1 + q + 1 : ℕ) : ℤ) (q + 1))
          * sqBracketCoeffC h m (m + (p.2 : ℤ))) • x (p.1 + p.2))
      = ∑ᶠ t : ℕ,
          (sqBracketCoeffZ 2 1 ((q + 1 : ℕ) : ℤ)
            * sqBracketCoeffC (h - q) m (m + (t : ℤ))) • x t := by
  rw [finsum_prod_eq_finsum_antidiagonal_sq _
    (support_pair_smul_add_finite _ x hx)]
  refine finsum_congr fun t ↦ ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hc := sqBracketCoeffC_gBinom_collapse hq h m t
  rw [← hc, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro s hs
  have hst : s ≤ t := by rw [Finset.mem_range] at hs; omega
  rw [Nat.add_sub_of_le hst]

namespace SuperNearVOA

/-! ## The even-conformal-vector ordinary commutator -/

variable (V : SuperNearVOA VType)

/-! ## Natural-tail expansions -/

/-- A complex-weight square mode as its natural tail `i=m+n`. -/
theorem superVSqC_eq_nat_finsum (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    V.superVSqC a h m v = ∑ᶠ n : ℕ,
      sqBracketCoeffC h m (m + (n : ℤ)) • V.smul a (m + (n : ℤ)) v := by
  rw [V.superVSqC_apply, finsum_int_ge_eq_nat_shift]
  intro i hi
  rw [sqBracketCoeffC_of_lt h hi, zero_smul]

/-- `L[0]` as its natural Virasoro tail. -/
theorem superLsq_zero_eq_nat_finsum (v : VType) :
    V.superLsq 0 v = ∑ᶠ r : ℕ,
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) • V.L (r : ℤ) v := by
  rw [Lsq_apply, show (0 : ℤ) + 1 = 1 by ring,
    sqBracketCoeffZ_vacuum_of_ne 1 (by norm_num), mul_zero, zero_smul, sub_zero,
    show (1 : ℤ) = 0 + 1 by ring, vSqZ_omega_apply V 0 v]
  symm
  apply VertexOperatorAlgebra.finsum_nat_to_int
  · intro r hr
    rw [sqBracketCoeffZ_of_lt 2 (by omega), zero_smul]
  · intro r
    congr 2

theorem superDLNat_support_finite (v : VType) :
    (Function.support fun r : ℕ ↦
      sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) • V.L (r : ℤ) v).Finite := by
  have hs := (dL_support_finite V 0 v).preimage
    (f := fun r : ℕ ↦ (r : ℤ)) (Function.Injective.injOn Int.ofNat_injective)
  refine hs.subset fun r hr ↦ ?_
  simpa only [Set.mem_preimage] using hr

theorem superSqCNat_support_finite (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    (Function.support fun n : ℕ ↦
      sqBracketCoeffC h m (m + (n : ℤ)) • V.smul a (m + (n : ℤ)) v).Finite := by
  have hs := (V.superSqModeC_support_finite a h m v).preimage
    (f := fun n : ℕ ↦ m + (n : ℤ)) (by
      intro r s hrs
      have : (r : ℤ) = (s : ℤ) := add_left_cancel hrs
      exact_mod_cast this : Function.Injective fun n : ℕ ↦ m + (n : ℤ)).injOn
  refine hs.subset fun n hn ↦ ?_
  simpa only [Set.mem_preimage] using hn

/-! ## The locally finite square/ordinary commutator -/

theorem superLsq_zero_superVSqC_comp (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    V.superLsq 0 (V.superVSqC a h m v) = ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v) := by
  rw [V.superVSqC_eq_nat_finsum,
    map_finsum (V.superLsq 0) (V.superSqCNat_support_finite a h m v)]
  refine finsum_congr fun n ↦ ?_
  rw [map_smul, V.superLsq_zero_eq_nat_finsum,
    smul_finsum' _ (V.superDLNat_support_finite (V.smul a (m + (n : ℤ)) v))]
  refine finsum_congr fun r ↦ ?_
  rw [smul_smul, mul_comm]

theorem superSqCLJoint_support_finite (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) :
    (Function.support fun p : ℕ × ℕ ↦
      (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (p.2 : ℤ))) •
          V.smul a (m + (p.2 : ℤ)) (V.L (p.1 : ℤ) v)).Finite := by
  refine Set.Finite.subset
    ((V.superDLNat_support_finite v).biUnion fun r _ ↦
      (V.superSqCNat_support_finite a h m (V.L (r : ℤ) v)).image fun n ↦ (r, n)) ?_
  intro p hp
  simp only [Function.mem_support, ne_eq, smul_ne_zero_iff, mul_ne_zero_iff] at hp
  obtain ⟨⟨hdr, hcn⟩, hvec⟩ := hp
  simp only [Set.mem_iUnion, Set.mem_image, Function.mem_support, ne_eq,
    smul_ne_zero_iff, exists_prop]
  refine ⟨p.1, ⟨hdr, fun hz ↦ hvec (by rw [hz, V.smul_zero_rightε])⟩, p.2, ?_, rfl⟩
  exact ⟨hcn, hvec⟩

theorem superVSqC_superLsq_zero_comp (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    V.superVSqC a h m (V.superLsq 0 v) = ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v) := by
  have hraw : V.superVSqC a h m (V.superLsq 0 v) = ∑ᶠ r : ℕ, ∑ᶠ n : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v) := by
    rw [V.superLsq_zero_eq_nat_finsum,
      map_finsum (V.superVSqC a h m) (V.superDLNat_support_finite v)]
    refine finsum_congr fun r ↦ ?_
    rw [map_smul, V.superVSqC_eq_nat_finsum,
      smul_finsum' _ (V.superSqCNat_support_finite a h m (V.L (r : ℤ) v))]
    refine finsum_congr fun n ↦ ?_
    rw [smul_smul]
  rw [hraw]
  exact (finsum_finsum_comm_sq
    (fun r n : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v))
    (V.superSqCLJoint_support_finite a h m v)).symm

theorem superLsq_zero_superVSqC_comm_double
    (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    V.superLsq 0 (V.superVSqC a h m v) -
        V.superVSqC a h m (V.superLsq 0 v) =
      ∑ᶠ n : ℕ, ∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + (n : ℤ))) •
            (V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v)
              - V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)) := by
  rw [V.superLsq_zero_superVSqC_comp, V.superVSqC_superLsq_zero_comp]
  have hout1 : (Function.support fun n : ℕ ↦ ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v)).Finite := by
    refine (V.superSqCNat_support_finite a h m v).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hzero
    have heq : (∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + (n : ℤ))) •
            V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v)) =
        sqBracketCoeffC h m (m + (n : ℤ)) •
          V.superLsq 0 (V.smul a (m + (n : ℤ)) v) := by
      rw [V.superLsq_zero_eq_nat_finsum,
        smul_finsum' _ (V.superDLNat_support_finite (V.smul a (m + (n : ℤ)) v))]
      refine finsum_congr fun r ↦ ?_
      rw [smul_smul]
      congr 1
      ring
    apply hn
    rw [heq, ← map_smul, hzero, map_zero]
  have hout2 : (Function.support fun n : ℕ ↦ ∑ᶠ r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)).Finite := by
    refine (V.superSqCNat_support_finite a h m (V.superLsq 0 v)).subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hzero
    have hfinmap : (Function.support fun r : ℕ ↦
        sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
          V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)).Finite := by
      refine (V.superDLNat_support_finite v).subset ?_
      intro r hr
      simp only [Function.mem_support, ne_eq] at hr ⊢
      intro hz
      apply hr
      have hz' := congrArg (fun x ↦ V.smul a (m + (n : ℤ)) x) hz
      simpa only [SuperVertexAlgebra.smul_smul_right, V.smul_zero_rightε] using hz'
    have heq : (∑ᶠ r : ℕ,
        (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + (n : ℤ))) •
            V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)) =
        sqBracketCoeffC h m (m + (n : ℤ)) •
          V.smul a (m + (n : ℤ)) (V.superLsq 0 v) := by
      rw [V.superLsq_zero_eq_nat_finsum]
      change _ = sqBracketCoeffC h m (m + (n : ℤ)) •
        mode (V.Y a) (m + (n : ℤ))
          (∑ᶠ r : ℕ, sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) • V.L (r : ℤ) v)
      rw [map_finsum (mode (V.Y a) (m + (n : ℤ))) (V.superDLNat_support_finite v)]
      simp_rw [map_smul]
      have hfinmap' : (Function.support fun r : ℕ ↦
          sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
            mode (V.Y a) (m + (n : ℤ)) (V.L (r : ℤ) v)).Finite := hfinmap
      rw [smul_finsum' _ hfinmap']
      refine finsum_congr fun r ↦ ?_
      rw [smul_smul]
      congr 1
      ring
    exact hn (heq.trans hzero)
  rw [← finsum_sub_distrib hout1 hout2]
  refine finsum_congr fun n ↦ ?_
  have hin1 : (Function.support fun r : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v)).Finite := by
    refine (V.superDLNat_support_finite (V.smul a (m + (n : ℤ)) v)).subset ?_
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro hbase
    apply hr
    calc
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + (n : ℤ))) •
            V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v)
        = sqBracketCoeffC h m (m + (n : ℤ)) •
            (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
              V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v)) := by
            rw [smul_smul]
            congr 1
            ring
      _ = 0 := by rw [hbase, smul_zero]
  have hin2 : (Function.support fun r : ℕ ↦
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)).Finite := by
    refine (V.superDLNat_support_finite v).subset ?_
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro hbase
    apply hr
    have hmap : sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
        V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v) = 0 := by
      have hz := congrArg (fun x ↦ V.smul a (m + (n : ℤ)) x) hbase
      simpa only [SuperVertexAlgebra.smul_smul_right, V.smul_zero_rightε] using hz
    calc
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + (n : ℤ))) •
            V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)
        = sqBracketCoeffC h m (m + (n : ℤ)) •
            (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ) •
              V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)) := by
            rw [smul_smul]
            congr 1
            ring
      _ = 0 := by rw [hmap, smul_zero]
  rw [← finsum_sub_distrib hin1 hin2]
  refine finsum_congr fun r ↦ ?_
  rw [smul_sub]

/-- The ordinary Virasoro commutator for a parity-homogeneous state.  Because the conformal vector
is even, the super mode bracket is the ordinary commutator and no Koszul sign remains. -/
theorem superL_nat_mode_comm_of_mem_parity {p : ZMod 2} {a : VType}
    (ha : a ∈ V.parity p) (r : ℕ) (i : ℤ) :
    ⁅V.L (r : ℤ), mode (V.Y a) i⁆ =
      ∑ ℓ ∈ Finset.range (r + 2), gBinom ((r + 1 : ℕ) : ℤ) ℓ •
        mode (V.Y (V.L ((ℓ : ℤ) - 1) a))
          ((r + 1 : ℕ) + i - (ℓ : ℕ)) := by
  obtain ⟨N, hzero, hcomm⟩ :=
    V.commBoundε V.conformal_parity ha ((r + 1 : ℕ) : ℤ) i
  have hL : V.L (r : ℤ) = mode (V.Y V.conformalVector) ((r + 1 : ℕ) : ℤ) := by
    simp only [L_def]
    congr 2
  rw [hL]
  have hcomm' :
      ⁅mode (V.Y V.conformalVector) ((r + 1 : ℕ) : ℤ), mode (V.Y a) i⁆ =
        ∑ j : Fin N, gBinom ((r + 1 : ℕ) : ℤ) (j : ℕ) •
          mode (V.Y (V.smul V.conformalVector (j : ℕ) a))
            (((r + 1 : ℕ) : ℤ) + i - (j : ℕ)) := by
    simpa only [koszul_zero_left, modeBracketε, one_smul] using hcomm
  rw [hcomm']
  rw [VertexOperatorAlgebra.finN_gBinom_collapse (r + 1) N
    (fun ℓ ↦ mode (V.Y (V.smul V.conformalVector (ℓ : ℤ) a))
      (((r + 1 : ℕ) : ℤ) + i - (ℓ : ℤ)))
    (fun ℓ hN ↦ by
      change mode (V.Y (V.smul V.conformalVector (ℓ : ℤ) a))
        (((r + 1 : ℕ) : ℤ) + i - (ℓ : ℤ)) = 0
      rw [hzero ℓ hN, map_zero, mode_zero])]
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 2
  rw [L_def, SuperVertexAlgebra.smul_def]
  congr 2
  ring

/-- Split the even-conformal-vector commutator into the `L(-1)`/`L(0)` pair and the positive
Virasoro tail.  The inserted state is homogeneous both in parity and in complex weight. -/
theorem superL_nat_mode_comm_split {p : ZMod 2} {a : VType} {h : ℂ}
    (hpar : a ∈ V.parity p) (hwt : a ∈ V.grading h)
    (r : ℕ) (i : ℤ) (v : VType) :
    V.L (r : ℤ) (V.smul a i v) - V.smul a i (V.L (r : ℤ) v) =
      (h * ((r : ℂ) + 1) - ((r : ℂ) + (i : ℂ) + 1)) •
          V.smul a ((r : ℤ) + i) v
        + ∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
            V.smul (V.L ((q + 1 : ℕ) : ℤ) a)
              ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
  have hc := LinearMap.congr_fun (V.superL_nat_mode_comm_of_mem_parity hpar r i) v
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, LinearMap.sum_apply] at hc
  simp only [LinearMap.smul_apply] at hc
  have htail : (∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
      V.smul (V.L ((q + 1 : ℕ) : ℤ) a)
        ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v) =
      ∑ q ∈ Finset.range r, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        V.smul (V.L ((q + 1 : ℕ) : ℤ) a)
          ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
    apply finsum_eq_finsetSum_of_support_subset
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hqr
    push Not at hqr
    apply hq
    rw [gBinom_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]
  rw [htail]
  change V.L (r : ℤ) (mode (V.Y a) i v) -
      mode (V.Y a) i (V.L (r : ℤ) v) =
    (h * ((r : ℂ) + 1) - ((r : ℂ) + (i : ℂ) + 1)) •
        mode (V.Y a) ((r : ℤ) + i) v
      + ∑ q ∈ Finset.range r, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
          mode (V.Y (V.L ((q + 1 : ℕ) : ℤ) a))
            ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v
  rw [hc]
  rw [Finset.sum_range_succ' (n := r + 1),
    Finset.sum_range_succ' (f := fun ℓ : ℕ ↦
      gBinom ((r + 1 : ℕ) : ℤ) (ℓ + 1) •
        mode (V.Y (V.L (((ℓ + 1 : ℕ) : ℤ) - 1) a))
          ((r + 1 : ℕ) + i - (ℓ + 1 : ℕ)) v) (n := r)]
  have hg0 : gBinom ((r + 1 : ℕ) : ℤ) 0 = 1 := gBinom_zero _
  have hg1 : gBinom ((r + 1 : ℕ) : ℤ) 1 = ((r : ℂ) + 1) := by
    rw [gBinom_natCast]
    simp
  rw [hg0, hg1, one_smul,
    show (((0 : ℕ) : ℤ) - 1) = -1 by norm_num,
    show (((1 : ℕ) : ℤ) - 1) = 0 by norm_num]
  have hcastL : ∀ q : ℕ, ((((q + 1 : ℕ) + 1 : ℕ) : ℤ) - 1)
      = ((q + 1 : ℕ) : ℤ) := by intro q; push_cast; ring
  have hcastI : ∀ q : ℕ, ((r + 1 : ℕ) : ℤ) + i - ((q + 1 : ℕ) : ℤ)
      = (r : ℤ) + i - q := by intro q; push_cast; ring
  simp_rw [hcastL, hcastI]
  simp only [Nat.cast_zero, sub_zero]
  have hT : mode (V.Y (V.L (-1) a)) (((r + 1 : ℕ) : ℤ) + i) v =
      (-(((r + 1 : ℕ) : ℤ) + i)) • mode (V.Y a) ((r : ℤ) + i) v := by
    simpa only [SuperVertexAlgebra.smul_def,
      show (((r + 1 : ℕ) : ℤ) + i - 1) = (r : ℤ) + i by push_cast; ring] using
        V.smul_T_applyε a v (((r + 1 : ℕ) : ℤ) + i)
  have h0 : mode (V.Y (V.L 0 a)) ((r : ℤ) + i) v =
      h • mode (V.Y a) ((r : ℤ) + i) v := by
    rw [V.L0_eigenvalue hwt, map_smul, mode_smul, LinearMap.smul_apply]
  rw [hT, h0, smul_smul]
  have htailsame : (∑ x ∈ Finset.range r,
      gBinom ((r + 1 : ℕ) : ℤ) (x + 1 + 1) •
        mode (V.Y (V.L ((x + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((x + 1 : ℕ) : ℤ)) v) =
      ∑ q ∈ Finset.range r, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        mode (V.Y (V.L ((q + 1 : ℕ) : ℤ) a))
          ((r : ℤ) + i - ((q + 1 : ℕ) : ℤ)) v := by
    apply Finset.sum_congr rfl
    intro q _
    congr 3 <;> omega
  rw [htailsame]
  push_cast
  module

/-! ## Vector-valued scalar collapses -/

theorem superModeNat_support_finite (a : VType) (m : ℤ) (v : VType) :
    (Function.support fun t : ℕ ↦ V.smul a (m + (t : ℤ)) v).Finite := by
  obtain ⟨R, hR⟩ := V.regularity a v
  refine Set.Finite.subset (Set.finite_Iio ((R - m).toNat + 1)) ?_
  intro t ht
  simp only [Function.mem_support, ne_eq] at ht
  rw [Set.mem_Iio]
  by_contra hlarge
  push Not at hlarge
  apply ht
  apply hR
  have hself := Int.self_le_toNat (R - m)
  omega

theorem superSqLow_comm_collapse (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    (∑ᶠ p : ℕ × ℕ,
      (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (p.2 : ℤ))
        * (h * ((p.1 : ℂ) + 1)
          - ((m : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
            V.smul a (m + ((p.1 + p.2 : ℕ) : ℤ)) v) =
      (h - (m : ℂ) - 1) • V.superVSqC a h m v := by
  rw [sqLowPairC_vector_collapse h m
    (fun t : ℕ ↦ V.smul a (m + (t : ℤ)) v)
    (V.superModeNat_support_finite a m v), V.superVSqC_eq_nat_finsum,
    smul_finsum' _ (V.superSqCNat_support_finite a h m v)]
  refine finsum_congr fun t ↦ ?_
  rw [smul_smul]

theorem superSqPositive_comm_collapse {Q : ℕ} (hQ : 1 ≤ Q)
    (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    (∑ᶠ p : ℕ × ℕ,
      ((sqBracketCoeffZ 2 1 ((p.1 + Q + 1 : ℕ) : ℤ)
        * gBinom ((p.1 + Q + 1 : ℕ) : ℤ) (Q + 1))
        * sqBracketCoeffC h m (m + (p.2 : ℤ))) •
          V.smul (V.L (Q : ℤ) a)
            (m + ((p.1 + p.2 : ℕ) : ℤ)) v) =
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        V.superVSqC (V.L (Q : ℤ) a) (h - Q) m v := by
  rw [sqPositiveTailC_vector_collapse hQ h m
    (fun t : ℕ ↦ V.smul (V.L (Q : ℤ) a) (m + (t : ℤ)) v)
    (V.superModeNat_support_finite (V.L (Q : ℤ) a) m v),
    V.superVSqC_eq_nat_finsum,
    smul_finsum' _ (V.superSqCNat_support_finite (V.L (Q : ℤ) a) (h - Q) m v)]
  refine finsum_congr fun t ↦ ?_
  rw [smul_smul]

/-! ## Reindexed commutator terms -/

noncomputable def superSqLowCommTerm (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) (p : ℕ × ℕ) : VType :=
  (sqBracketCoeffZ 2 1 ((p.2 + 1 : ℕ) : ℤ)
    * sqBracketCoeffC h m (m + (p.1 : ℤ))
    * (h * ((p.2 : ℂ) + 1)
      - ((m : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
        V.smul a (m + ((p.1 + p.2 : ℕ) : ℤ)) v

noncomputable def superSqPositiveCommTerm (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) (Q : ℕ) (p : ℕ × ℕ) : VType :=
  ((sqBracketCoeffZ 2 1 ((p.2 + 1 : ℕ) : ℤ)
    * sqBracketCoeffC h m (m + (p.1 : ℤ)))
    * gBinom ((p.2 + 1 : ℕ) : ℤ) (Q + 1)) •
      V.smul (V.L (Q : ℤ) a)
        (m + ((p.1 + (p.2 - Q) : ℕ) : ℤ)) v

noncomputable def superSqPositiveReindexedTerm (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) (Q : ℕ) (p : ℕ × ℕ) : VType :=
  ((sqBracketCoeffZ 2 1 ((p.1 + Q + 1 : ℕ) : ℤ)
    * gBinom ((p.1 + Q + 1 : ℕ) : ℤ) (Q + 1))
    * sqBracketCoeffC h m (m + (p.2 : ℤ))) •
      V.smul (V.L (Q : ℤ) a)
        (m + ((p.1 + p.2 : ℕ) : ℤ)) v

theorem superSqLowCommTerm_support_finite (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) :
    (Function.support (V.superSqLowCommTerm a h m v)).Finite := by
  let g : ℕ × ℕ → VType := fun p ↦
    (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
      * sqBracketCoeffC h m (m + (p.2 : ℤ))
      * (h * ((p.1 : ℂ) + 1)
        - ((m : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
          V.smul a (m + ((p.1 + p.2 : ℕ) : ℤ)) v
  have hg : (Function.support g).Finite := support_pair_smul_add_finite
    (fun p : ℕ × ℕ ↦ sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
      * sqBracketCoeffC h m (m + (p.2 : ℤ))
      * (h * ((p.1 : ℂ) + 1)
        - ((m : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1)))
    (fun t : ℕ ↦ V.smul a (m + (t : ℤ)) v)
    (V.superModeNat_support_finite a m v)
  have hswap := hg.preimage (f := Prod.swap) (Function.Injective.injOn Prod.swap_injective)
  refine hswap.subset fun p hp ↦ ?_
  change g (Prod.swap p) ≠ 0
  rcases p with ⟨n, r⟩
  simpa only [g, superSqLowCommTerm, Prod.swap_prod_mk, Prod.fst, Prod.snd,
    Nat.add_comm] using hp

theorem superSqPositiveReindexedTerm_support_finite (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) (Q : ℕ) :
    (Function.support (V.superSqPositiveReindexedTerm a h m v Q)).Finite := by
  exact support_pair_smul_add_finite _ _
    (V.superModeNat_support_finite (V.L (Q : ℤ) a) m v)

theorem superSqPositiveCommTerm_support_finite (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) (Q : ℕ) :
    (Function.support (V.superSqPositiveCommTerm a h m v Q)).Finite := by
  let φ : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, Q + p.1)
  have hR := V.superSqPositiveReindexedTerm_support_finite a h m v Q
  refine Set.Finite.subset (hR.image φ) ?_
  intro p hp
  have hrQ : Q ≤ p.2 := by
    by_contra hr
    push Not at hr
    rw [Function.mem_support] at hp
    apply hp
    rw [superSqPositiveCommTerm, gBinom_natCast,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_smul]
  let s := p.2 - Q
  have hs : Q + s = p.2 := Nat.add_sub_of_le hrQ
  have hterm : V.superSqPositiveReindexedTerm a h m v Q (s, p.1) ≠ 0 := by
    change V.superSqPositiveCommTerm a h m v Q p ≠ 0 at hp
    simpa only [superSqPositiveCommTerm, superSqPositiveReindexedTerm,
      Prod.fst, Prod.snd, hs, Nat.add_sub_cancel_left, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm] using hp
  exact ⟨(s, p.1), hterm, by ext <;> simp [φ, hs]⟩

theorem superSqPositiveCommTerm_collapse {Q : ℕ} (hQ : 1 ≤ Q)
    (a : VType) (h : ℂ) (m : ℤ) (v : VType) :
    (∑ᶠ p : ℕ × ℕ, V.superSqPositiveCommTerm a h m v Q p) =
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        V.superVSqC (V.L (Q : ℤ) a) (h - Q) m v := by
  let φ : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, Q + p.1)
  have hinj : Function.Injective φ := by
    intro p q hpq
    apply Prod.ext
    · have := congrArg Prod.snd hpq
      dsimp only [φ] at this
      omega
    · have := congrArg Prod.fst hpq
      exact this
  have hsub : Function.support (V.superSqPositiveCommTerm a h m v Q) ⊆
      Set.range φ := by
    intro p hp
    have hrQ : Q ≤ p.2 := by
      by_contra hr
      push Not at hr
      rw [Function.mem_support] at hp
      apply hp
      rw [superSqPositiveCommTerm, gBinom_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_smul]
    exact ⟨(p.2 - Q, p.1), by ext <;> simp [φ, Nat.add_sub_of_le hrQ]⟩
  rw [← finsum_mem_of_support_subset_sq
      (V.superSqPositiveCommTerm a h m v Q) _ hsub,
    finsum_mem_range hinj]
  have hreindex : ∀ p : ℕ × ℕ,
      V.superSqPositiveCommTerm a h m v Q (φ p) =
        V.superSqPositiveReindexedTerm a h m v Q p := by
    rintro ⟨s, n⟩
    simp only [φ, superSqPositiveCommTerm, superSqPositiveReindexedTerm,
      Prod.fst, Prod.snd, Nat.add_sub_cancel_left, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm]
  rw [finsum_congr hreindex]
  exact V.superSqPositive_comm_collapse hQ a h m v

theorem superSqLowCommTerm_collapse (a : VType) (h : ℂ)
    (m : ℤ) (v : VType) :
    (∑ᶠ p : ℕ × ℕ, V.superSqLowCommTerm a h m v p) =
      (h - (m : ℂ) - 1) • V.superVSqC a h m v := by
  rw [← finsum_comp_equiv (Equiv.prodComm ℕ ℕ)]
  have heq : ∀ p : ℕ × ℕ,
      V.superSqLowCommTerm a h m v ((Equiv.prodComm ℕ ℕ) p) =
        (sqBracketCoeffZ 2 1 ((p.1 + 1 : ℕ) : ℤ)
          * sqBracketCoeffC h m (m + (p.2 : ℤ))
          * (h * ((p.1 : ℂ) + 1)
            - ((m : ℂ) + ((p.1 + p.2 : ℕ) : ℂ) + 1))) •
              V.smul a (m + ((p.1 + p.2 : ℕ) : ℤ)) v := by
    rintro ⟨r, n⟩
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, superSqLowCommTerm,
      Prod.fst, Prod.snd, Nat.add_comm]
  rw [finsum_congr heq]
  exact V.superSqLow_comm_collapse a h m v

/-! ## Collapse of the full double commutator -/

/-- The homogeneous square/ordinary commutator after regrouping.  The positive tail is cut off
by ordinary regularity of `Y(ω,z)a`, not by integrality of the weight. -/
theorem superLsq_zero_superVSqC_comm_collapsed {p : ZMod 2} {a : VType} {h : ℂ}
    (hpar : a ∈ V.parity p) (hwt : a ∈ V.grading h)
    (m : ℤ) (v : VType) :
    ∃ K : ℕ,
      (∀ q : ℕ, K ≤ q → V.L ((q + 1 : ℕ) : ℤ) a = 0) ∧
      V.superLsq 0 (V.superVSqC a h m v) -
          V.superVSqC a h m (V.superLsq 0 v) =
        (h - (m : ℂ) - 1) • V.superVSqC a h m v
          + ∑ Q ∈ Finset.range K,
              sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
                V.superVSqC (V.L ((Q + 1 : ℕ) : ℤ) a)
                  (h - (Q + 1 : ℕ)) m v := by
  obtain ⟨R, hR⟩ := V.regularity V.conformalVector a
  let K : ℕ := R.toNat
  have hLzero : ∀ q : ℕ, K ≤ q → V.L ((q + 1 : ℕ) : ℤ) a = 0 := by
    intro q hq
    rw [L_def]
    apply hR
    have hRnat := Int.self_le_toNat R
    dsimp only [K] at hq
    omega
  refine ⟨K, hLzero, ?_⟩
  rw [V.superLsq_zero_superVSqC_comm_double]
  let H : ℕ × ℕ → VType := fun z ↦ V.superSqLowCommTerm a h m v z
    + ∑ Q ∈ Finset.range K, V.superSqPositiveCommTerm a h m v (Q + 1) z
  have hterm : ∀ n r : ℕ,
      (sqBracketCoeffZ 2 1 ((r + 1 : ℕ) : ℤ)
        * sqBracketCoeffC h m (m + (n : ℤ))) •
          (V.L (r : ℤ) (V.smul a (m + (n : ℤ)) v)
            - V.smul a (m + (n : ℤ)) (V.L (r : ℤ) v)) = H (n, r) := by
    intro n r
    rw [V.superL_nat_mode_comm_split hpar hwt r (m + (n : ℤ)) v, smul_add]
    have htail : (∑ᶠ q : ℕ, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
        V.smul (V.L ((q + 1 : ℕ) : ℤ) a)
          ((r : ℤ) + (m + (n : ℤ)) - ((q + 1 : ℕ) : ℤ)) v) =
        ∑ q ∈ Finset.range K, gBinom ((r + 1 : ℕ) : ℤ) (q + 2) •
          V.smul (V.L ((q + 1 : ℕ) : ℤ) a)
            ((r : ℤ) + (m + (n : ℤ)) - ((q + 1 : ℕ) : ℤ)) v := by
      apply finsum_eq_finsetSum_of_support_subset
      intro q hq
      simp only [Function.mem_support, ne_eq] at hq
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hqK
      push Not at hqK
      exact hq (by rw [hLzero q hqK, V.smul_zero_leftε, smul_zero])
    rw [htail, Finset.smul_sum]
    change _ = V.superSqLowCommTerm a h m v (n, r)
      + ∑ Q ∈ Finset.range K, V.superSqPositiveCommTerm a h m v (Q + 1) (n, r)
    congr 1
    · simp only [superSqLowCommTerm, Prod.fst, Prod.snd, smul_smul]
      have hidx : (r : ℤ) + (m + (n : ℤ)) =
          m + ((n + r : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hidx]
      congr 1
      push_cast
      ring
    · apply Finset.sum_congr rfl
      intro Q hQ
      by_cases hQr : Q + 1 ≤ r
      · have hidx : (r : ℤ) + (m + (n : ℤ)) - ((Q + 1 : ℕ) : ℤ) =
            m + ((n + (r - (Q + 1)) : ℕ) : ℤ) := by
          push_cast [hQr]
          ring
        simp only [superSqPositiveCommTerm, Prod.fst, Prod.snd, smul_smul,
          Nat.add_sub_of_le hQr]
        rw [hidx]
      · have hbin : gBinom ((r + 1 : ℕ) : ℤ) (Q + 1 + 1) = 0 := by
          rw [gBinom_natCast, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        rw [hbin, zero_smul, smul_zero, superSqPositiveCommTerm,
          hbin, mul_zero, zero_smul]
  simp_rw [hterm]
  have hposUnion : (Function.support fun z : ℕ × ℕ ↦
      ∑ Q ∈ Finset.range K, V.superSqPositiveCommTerm a h m v (Q + 1) z).Finite := by
    refine Set.Finite.subset
      ((Finset.range K).finite_toSet.biUnion fun Q _ ↦
        V.superSqPositiveCommTerm_support_finite a h m v (Q + 1)) ?_
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    obtain ⟨Q, hQ, hQne⟩ : ∃ Q ∈ Finset.range K,
        V.superSqPositiveCommTerm a h m v (Q + 1) z ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hz (Finset.sum_eq_zero fun Q hQ ↦ hnone Q hQ)
    rw [Set.mem_iUnion]
    refine ⟨Q, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hQ, hQne⟩
  have hH : (Function.support H).Finite := by
    refine Set.Finite.subset
      ((V.superSqLowCommTerm_support_finite a h m v).union hposUnion) ?_
    intro z hz
    by_cases hlow : V.superSqLowCommTerm a h m v z = 0
    · right
      change (∑ Q ∈ Finset.range K,
        V.superSqPositiveCommTerm a h m v (Q + 1) z) ≠ 0
      intro hpos
      change H z ≠ 0 at hz
      exact hz (by simp only [H, hlow, hpos, add_zero])
    · left
      exact hlow
  rw [← finsum_curry H hH]
  change (∑ᶠ z : ℕ × ℕ,
      (V.superSqLowCommTerm a h m v z
        + ∑ Q ∈ Finset.range K,
            V.superSqPositiveCommTerm a h m v (Q + 1) z)) = _
  rw [finsum_add_distrib (V.superSqLowCommTerm_support_finite a h m v) hposUnion,
    V.superSqLowCommTerm_collapse,
    finsum_sum_comm (Finset.range K)
      (fun z Q ↦ V.superSqPositiveCommTerm a h m v (Q + 1) z)
      (fun Q _ ↦ V.superSqPositiveCommTerm_support_finite a h m v (Q + 1))]
  apply congrArg (fun z ↦ (h - (m : ℂ) - 1) • V.superVSqC a h m v + z)
  apply Finset.sum_congr rfl
  intro Q hQ
  exact V.superSqPositiveCommTerm_collapse (by omega) a h m v

/-! ## Reassembly through the official half grading -/

/-- On a doubled-weight homogeneous state, the global square mode of `L[0]a` is the leading
weight term plus the same positive Virasoro tail as in the collapsed commutator. -/
theorem superSqModeHalf_superLsq_zero_explicit
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {a : VType} (ha : a ∈ W.toSuperNearVOA.halfGrading d)
    (m : ℤ) (v : VType) (K : ℕ)
    (hK : ∀ q : ℕ, K ≤ q →
      W.toSuperNearVOA.L ((q + 1 : ℕ) : ℤ) a = 0) :
    superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq 0 a) v =
      halfWeight d • W.toSuperNearVOA.superVSqC a (halfWeight d) m v
        + ∑ Q ∈ Finset.range K,
            sqBracketCoeffZ 2 1 (((Q + 1) + 1 : ℕ) : ℤ) •
              W.toSuperNearVOA.superVSqC
                (W.toSuperNearVOA.L ((Q + 1 : ℕ) : ℤ) a)
                (halfWeight d - (Q + 1 : ℕ)) m v := by
  let F : VType →ₗ[ℂ] VType :=
    (LinearMap.applyₗ v).comp (superSqModeHalf W hhalf m)
  have hmap : F (W.toSuperNearVOA.superLsq 0 a) = ∑ᶠ Q : ℕ,
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        F (W.toSuperNearVOA.L (Q : ℤ) a) := by
    rw [W.toSuperNearVOA.superLsq_zero_eq_nat_finsum,
      map_finsum F (W.toSuperNearVOA.superDLNat_support_finite a)]
    refine finsum_congr fun Q ↦ ?_
    rw [map_smul]
  have hsub : Function.support (fun Q : ℕ ↦
      sqBracketCoeffZ 2 1 ((Q + 1 : ℕ) : ℤ) •
        F (W.toSuperNearVOA.L (Q : ℤ) a)) ⊆ Finset.range (K + 1) := by
    intro Q hQ
    simp only [Function.mem_support, ne_eq] at hQ
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hQK
    push Not at hQK
    have hQpos : 1 ≤ Q := by omega
    have hzero : W.toSuperNearVOA.L (Q : ℤ) a = 0 := by
      rw [show Q = (Q - 1) + 1 by omega]
      exact hK (Q - 1) (by omega)
    exact hQ (by rw [hzero, map_zero, smul_zero])
  rw [show superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq 0 a) v =
      F (W.toSuperNearVOA.superLsq 0 a) from rfl,
    hmap, finsum_eq_finsetSum_of_support_subset _ hsub,
    Finset.sum_range_succ']
  have hfamily : ∀ Q : ℕ,
      F (W.toSuperNearVOA.L (Q : ℤ) a) =
        W.toSuperNearVOA.superVSqC (W.toSuperNearVOA.L (Q : ℤ) a)
          (halfWeight d - Q) m v := by
    intro Q
    have hmem := superL_mem_halfGrading W ha (Q : ℤ)
    rw [show F (W.toSuperNearVOA.L (Q : ℤ) a) =
      superSqModeHalf W hhalf m (W.toSuperNearVOA.L (Q : ℤ) a) v from rfl,
      superSqModeHalf_of_mem_halfGrading W hhalf hmem]
    change W.toSuperNearVOA.superVSqC (W.toSuperNearVOA.L (Q : ℤ) a)
      (halfWeight (d - 2 * (Q : ℤ))) m v = _
    congr 3
    rw [halfWeight, halfWeight]
    push_cast
    ring
  simp_rw [hfamily]
  norm_num only [Nat.cast_zero, Nat.zero_add, Nat.cast_one, sub_zero]
  rw [show W.toSuperNearVOA.L (0 : ℤ) a = halfWeight d • a by
      exact W.toSuperNearVOA.L0_eigenvalue ha,
    W.toSuperNearVOA.superVSqC_smul_left, LinearMap.smul_apply,
    sqBracketCoeffZ_diag' 2 1, one_smul]
  abel

/-! ## The `L[0]` commutator and square-weight shift -/

/-- The `L[0]` commutator on a state homogeneous in both official gradings. -/
theorem superLsq_zero_superSqModeHalf_comm_of_mem_halfGrading_parity
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {p : ZMod 2} {a : VType}
    (hwt : a ∈ W.toSuperNearVOA.halfGrading d) (hpar : a ∈ W.parity p)
    (m : ℤ) (v : VType) :
    W.toSuperNearVOA.superLsq 0 (superSqModeHalf W hhalf m a v) -
        superSqModeHalf W hhalf m a (W.toSuperNearVOA.superLsq 0 v) =
      superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq 0 a) v -
        ((m : ℂ) + 1) • superSqModeHalf W hhalf m a v := by
  have hgrade : a ∈ W.grading (halfWeight d) := hwt
  obtain ⟨K, hK, hc⟩ :=
    W.toSuperNearVOA.superLsq_zero_superVSqC_comm_collapsed hpar hgrade m v
  have he := superSqModeHalf_superLsq_zero_explicit W hhalf hwt m v K hK
  rw [superSqModeHalf_of_mem_halfGrading W hhalf hwt m]
  change W.toSuperNearVOA.superLsq 0
        (W.toSuperNearVOA.superVSqC a (halfWeight d) m v) -
      W.toSuperNearVOA.superVSqC a (halfWeight d) m
        (W.toSuperNearVOA.superLsq 0 v) =
    superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq 0 a) v -
      ((m : ℂ) + 1) • W.toSuperNearVOA.superVSqC a (halfWeight d) m v
  rw [hc, he]
  module

/-- The homogeneous `L[0]` commutator with no parity hypothesis. -/
theorem superLsq_zero_superSqModeHalf_comm_of_mem_halfGrading
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    {d : ℤ} {a : VType} (ha : a ∈ W.toSuperNearVOA.halfGrading d)
    (m : ℤ) (v : VType) :
    W.toSuperNearVOA.superLsq 0 (superSqModeHalf W hhalf m a v) -
        superSqModeHalf W hhalf m a (W.toSuperNearVOA.superLsq 0 v) =
      superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq 0 a) v -
        ((m : ℂ) + 1) • superSqModeHalf W hhalf m a v := by
  obtain ⟨s, hs, -⟩ := W.toSuperNearVOA.exists_sum_parProj a
  rw [← hs]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  apply superLsq_zero_superSqModeHalf_comm_of_mem_halfGrading_parity W hhalf
  · exact W.toSuperNearVOA.parProj_mem_grading p ha
  · exact W.toSuperNearVOA.parProj_mem p a

/-- Zhu's square-bracket grading keystone for a half-integrally graded super VOA. -/
theorem superLsq_zero_superSqModeHalf_comm
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    (a : VType) (m : ℤ) (v : VType) :
    W.toSuperNearVOA.superLsq 0 (superSqModeHalf W hhalf m a v) -
        superSqModeHalf W hhalf m a (W.toSuperNearVOA.superLsq 0 v) =
      superSqModeHalf W hhalf m (W.toSuperNearVOA.superLsq 0 a) v -
        ((m : ℂ) + 1) • superSqModeHalf W hhalf m a v := by
  classical
  letI := halfGradingDecomposition W hhalf
  let da := DirectSum.decompose W.toSuperNearVOA.halfGrading a
  have ha_sum : a = ∑ d ∈ da.support, (da d : VType) := by
    exact (DirectSum.sum_support_decompose W.toSuperNearVOA.halfGrading a).symm
  rw [ha_sum]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ ↦
    superLsq_zero_superSqModeHalf_comm_of_mem_halfGrading W hhalf (da d).2 m v

/-- Global square modes carry square weights, independently of parity. -/
theorem superSqModeHalf_mem_superSqWeightSpace
    (W : SuperVertexOperatorAlgebra VType) (hhalf : IsHalfIntegerGraded W)
    {K L : ℂ} {a v : VType}
    (ha : a ∈ W.toSuperNearVOA.superSqWeightSpace K)
    (hv : v ∈ W.toSuperNearVOA.superSqWeightSpace L) (m : ℤ) :
    superSqModeHalf W hhalf m a v ∈
      W.toSuperNearVOA.superSqWeightSpace (K + L - (m : ℂ) - 1) := by
  rw [W.toSuperNearVOA.mem_superSqWeightSpace_iff] at ha hv ⊢
  have hc := superLsq_zero_superSqModeHalf_comm W hhalf a m v
  rw [ha, hv, map_smul] at hc
  have hKa : superSqModeHalf W hhalf m (K • a) v =
      K • superSqModeHalf W hhalf m a v := by
    rw [map_smul, LinearMap.smul_apply]
  rw [hKa] at hc
  rw [sub_eq_iff_eq_add] at hc
  rw [hc]
  module

end SuperNearVOA

end VOA
