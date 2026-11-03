/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperBlockRelations
import VOA.Modularity.BlockFiniteDim

/-!
# Analytic genus-one blocks for an integral-weight super VOA

This file is the analytic, untwisted-supertrace slice of the super Zhu program.  The coordinate
change, Eisenstein functions, and differential equation are parity-blind.  Koszul signs enter
only at the algebraic cusp, where the zero-mode relations must become supercommutators.

The definition below deliberately keeps these axes separate:

* `IsSuperAnalyticBlock` records the scalar holomorphic recursion on the ordinary upper
  half-plane;
* parity occurs only through the super vertex operators and, downstream, the signed cusp
  quotient;
* no modular group is part of the definition.

Thus the one-point determinacy proof is reusable for a `Gamma_theta` sector after replacing the
integral square-bracket coefficients and scalar coefficient functions appropriate to that sector.

## Main results

* `superLsq` and `superLsq_tail_eventually_zero`;
* `IsSuperAnalyticBlock` and the vector space `superAnalyticBlocks`;
* `IsSuperAnalyticBlock.superBlockRelSpan_le_kerAt`;
* `IsSuperAnalyticBlock.eq_zero_of_eq_zero_at`;
* `finrank_superAnalyticBlocks_le_card_of_superBlockRel`.

No signed Zhu commutator congruence is assumed here.
-/

namespace VOA

open Complex
open scoped BigOperators

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-- The square-bracket Virasoro operator for a super near-VOA.  Both the conformal vector and the
vacuum are even, so this scalar coordinate-change formula carries no Koszul factor. -/
noncomputable def superLsq (n : ℤ) : Module.End ℂ 𝒱 :=
  V.superVSqZ V.conformalVector 2 (n + 1)
    - (V.centralCharge / 24) • V.superVSqZ V.vacuum 0 (n + 1)

/-- The positive even tail of the square-bracket Virasoro operators is eventually zero. -/
theorem superLsq_tail_eventually_zero (v : 𝒱) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → V.superLsq (2 * (m + 1) - 2 : ℤ) v = 0 := by
  obtain ⟨Nω, hNω⟩ := V.superVSqZ_eventually_zero V.conformalVector 2 v
  obtain ⟨Nvac, hNvac⟩ := V.superVSqZ_eventually_zero V.vacuum 0 v
  refine ⟨(max Nω Nvac).toNat, fun m hm => ?_⟩
  have hi : max Nω Nvac ≤ (2 * (m + 1) - 2 : ℤ) + 1 := by omega
  have hω := hNω _ (le_trans (le_max_left _ _) hi)
  have hvac := hNvac _ (le_trans (le_max_right _ _) hi)
  rw [superLsq, LinearMap.sub_apply, LinearMap.smul_apply, hω, hvac, smul_zero, sub_zero]

/-- Analytic genus-one relations in the untwisted, integral-weight supertrace sector.

The zero-mode condition is the analytic shadow of Koszul cyclicity.  It is written without an
explicit sign because the sign appears only after identifying `a[0]v` modulo `superO` with the
homogeneous supercommutator of the two Zhu classes. -/
structure IsSuperAnalyticBlock (F : 𝒱 → ℂ → ℂ) : Prop where
  holo : ∀ v : 𝒱, DifferentiableOn ℂ (F v) (imGT 0)
  addv : ∀ (v w : 𝒱) (z : ℂ), F (v + w) z = F v z + F w z
  smulv : ∀ (c : ℂ) (v : 𝒱) (z : ℂ), F (c • v) z = c * F v z
  vanish : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ V.gradingZ (k : ℤ), ∀ v : 𝒱,
    F (V.superVSqZ a k 0 v) = 0
  negTwo : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ V.gradingZ (k : ℤ), ∀ (v : 𝒱), ∀ z ∈ imGT 0,
    F (V.superVSqZ a k (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z
            * F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z) = 0
  omega : ∀ (v : 𝒱), ∀ z ∈ imGT 0,
    F (V.superLsq (-2) v) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 1) z
            * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z

variable {V}

theorem IsSuperAnalyticBlock.zerov {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) (z : ℂ) : F 0 z = 0 := by
  have h := hF.smulv 0 0 z
  rw [zero_smul, zero_mul] at h
  exact h

theorem IsSuperAnalyticBlock.vanish_apply {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) (k : ℕ) (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ V.gradingZ (k : ℤ)) (v : 𝒱) (z : ℂ) :
    F (V.superVSqZ a k 0 v) z = 0 := by
  rw [hF.vanish k hk a ha v]
  rfl

/-- The super `[minus two]` tail as a finite sum. -/
theorem superNegTwo_finsum_eq_sum {F : 𝒱 → ℂ → ℂ} (hF0 : ∀ z : ℂ, F 0 z = 0)
    {a v : 𝒱} {k K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 1) z * F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z))
      = ∑ m ∈ Finset.range K, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 1) z * F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z) := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hm (by rw [hK m (by omega), hF0, mul_zero, mul_zero])

/-- The `G2`-free super `[minus two]` tail as a finite sum. -/
theorem superNegTwo_tail_finsum_eq_sum {F : 𝒱 → ℂ → ℂ}
    (hF0 : ∀ z : ℂ, F 0 z = 0) {a v : 𝒱} {k K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 2) z * F (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) z))
      = ∑ m ∈ Finset.range K, ((2 * (m + 2) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 2) z * F (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) z) := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  have hz := hK (m + 1) (by omega)
  rw [show (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2)
      = 2 * ((m : ℤ) + 2) - 2 from by push_cast; ring] at hz
  exact hm (by rw [hz, hF0, mul_zero, mul_zero])

/-- The super square-bracket Virasoro tail as a finite sum. -/
theorem superOmega_finsum_eq_sum {F : 𝒱 → ℂ → ℂ} (hF0 : ∀ z : ℂ, F 0 z = 0)
    {v : 𝒱} {K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → V.superLsq (2 * (m + 1) - 2 : ℤ) v = 0) (z : ℂ) :
    (∑ᶠ m : ℕ, zhuGC (m + 1) z
        * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z)
      = ∑ m ∈ Finset.range K, zhuGC (m + 1) z
        * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z := by
  classical
  refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hm (by rw [hK m (by omega), hF0, mul_zero])

/-- Condition (ii) with the `G2` term removed using the zero-mode condition. -/
theorem IsSuperAnalyticBlock.negTwo_tail {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) (k : ℕ) (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ V.gradingZ (k : ℤ)) (v : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    F (V.superVSqZ a k (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z
            * F (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) z) = 0 := by
  obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a k v
  have hlaw := hF.negTwo k hk a ha v z hz
  have hpeel : (∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
        * (zhuGC (m + 1) z
          * F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z))
      = ((1 : ℕ) : ℂ) * (zhuGC 1 z * F (V.superVSqZ a k 0 v) z)
        + ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z
            * F (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) z) := by
    rw [finsum_nat_peel (K := K) (fun m hm => by
      rw [hK m hm, hF.zerov z]
      ring)]
    congr 1
  rw [hpeel, hF.vanish_apply k hk ha v z] at hlaw
  simpa using hlaw

/-! ## Linearity of the super block conditions -/

theorem isSuperAnalyticBlock_zero :
    V.IsSuperAnalyticBlock (fun (_ : 𝒱) (_ : ℂ) => (0 : ℂ)) where
  holo := fun _ => differentiableOn_const 0
  addv := fun _ _ _ => by ring
  smulv := fun _ _ _ => by ring
  vanish := fun _ _ _ _ _ => rfl
  negTwo := fun _ _ _ _ _ _ _ => by
    rw [finsum_eq_zero_of_forall_eq_zero (fun _ => by ring)]
    ring
  omega := fun _ z _ => by
    rw [finsum_eq_zero_of_forall_eq_zero (fun _ => by ring), deriv_const]
    ring

theorem IsSuperAnalyticBlock.smul {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) (c : ℂ) :
    V.IsSuperAnalyticBlock (fun v z => c * F v z) where
  holo := fun v => (hF.holo v).const_mul c
  addv := fun v w z => by rw [hF.addv]; ring
  smulv := fun d v z => by rw [hF.smulv]; ring
  vanish := fun k hk a ha v => by
    funext z
    change c * F (V.superVSqZ a k 0 v) z = 0
    rw [hF.vanish_apply k hk ha v z, mul_zero]
  negTwo := fun k hk a ha v z hz => by
    obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a k v
    have hlaw := hF.negTwo k hk a ha v z hz
    rw [superNegTwo_finsum_eq_sum hF.zerov hK z] at hlaw
    rw [superNegTwo_finsum_eq_sum (F := fun v z => c * F v z)
      (fun z => by change c * F 0 z = 0; rw [hF.zerov, mul_zero]) hK z]
    have hpull : ∑ m ∈ Finset.range K, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z
            * (c * F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z))
        = c * ∑ m ∈ Finset.range K, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z
            * F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hpull]
    linear_combination c * hlaw
  omega := fun v z hz => by
    obtain ⟨K, hK⟩ := V.superLsq_tail_eventually_zero v
    have hlaw := hF.omega v z hz
    rw [superOmega_finsum_eq_sum hF.zerov hK z] at hlaw
    rw [superOmega_finsum_eq_sum (F := fun v z => c * F v z)
      (fun z => by change c * F 0 z = 0; rw [hF.zerov, mul_zero]) hK z]
    have hd : _root_.deriv (fun z => c * F v z) z = c * _root_.deriv (F v) z := by
      exact deriv_const_mul c
        ((hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
    rw [hd]
    have hpull : ∑ m ∈ Finset.range K, zhuGC (m + 1) z
          * (c * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z)
        = c * ∑ m ∈ Finset.range K, zhuGC (m + 1) z
          * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hpull]
    linear_combination c * hlaw

theorem IsSuperAnalyticBlock.add {F G : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) (hG : V.IsSuperAnalyticBlock G) :
    V.IsSuperAnalyticBlock (fun v z => F v z + G v z) where
  holo := fun v => (hF.holo v).add (hG.holo v)
  addv := fun v w z => by rw [hF.addv, hG.addv]; ring
  smulv := fun c v z => by rw [hF.smulv, hG.smulv]; ring
  vanish := fun k hk a ha v => by
    funext z
    change F (V.superVSqZ a k 0 v) z + G (V.superVSqZ a k 0 v) z = 0
    rw [hF.vanish_apply k hk ha v z, hG.vanish_apply k hk ha v z, add_zero]
  negTwo := fun k hk a ha v z hz => by
    obtain ⟨K, hK⟩ := V.superVSqZ_tail_eventually_zero a k v
    have hFlaw := hF.negTwo k hk a ha v z hz
    have hGlaw := hG.negTwo k hk a ha v z hz
    rw [superNegTwo_finsum_eq_sum hF.zerov hK z] at hFlaw
    rw [superNegTwo_finsum_eq_sum hG.zerov hK z] at hGlaw
    rw [superNegTwo_finsum_eq_sum (F := fun v z => F v z + G v z)
      (fun z => by change F 0 z + G 0 z = 0; rw [hF.zerov, hG.zerov, add_zero]) hK z]
    have hsplit : ∑ m ∈ Finset.range K, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z
            * (F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z
              + G (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z))
        = (∑ m ∈ Finset.range K, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z
              * F (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z))
          + ∑ m ∈ Finset.range K, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z
              * G (V.superVSqZ a k (2 * (m + 1) - 2 : ℤ) v) z) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    linear_combination hFlaw + hGlaw
  omega := fun v z hz => by
    obtain ⟨K, hK⟩ := V.superLsq_tail_eventually_zero v
    have hFlaw := hF.omega v z hz
    have hGlaw := hG.omega v z hz
    rw [superOmega_finsum_eq_sum hF.zerov hK z] at hFlaw
    rw [superOmega_finsum_eq_sum hG.zerov hK z] at hGlaw
    rw [superOmega_finsum_eq_sum (F := fun v z => F v z + G v z)
      (fun z => by change F 0 z + G 0 z = 0; rw [hF.zerov, hG.zerov, add_zero]) hK z]
    have hd : _root_.deriv (fun z => F v z + G v z) z
        = _root_.deriv (F v) z + _root_.deriv (G v) z := by
      exact deriv_add
        ((hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
        ((hG.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
    rw [hd]
    have hsplit : ∑ m ∈ Finset.range K, zhuGC (m + 1) z
          * (F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z
            + G (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z)
        = (∑ m ∈ Finset.range K, zhuGC (m + 1) z
            * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z)
          + ∑ m ∈ Finset.range K, zhuGC (m + 1) z
            * G (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsplit]
    linear_combination hFlaw + hGlaw

/-- The vector space of analytic blocks in the untwisted integral-weight supertrace sector. -/
def superAnalyticBlocks : Submodule ℂ (𝒱 → ℂ → ℂ) where
  carrier := {F | V.IsSuperAnalyticBlock F}
  add_mem' := fun hF hG => hF.add hG
  zero_mem' := isSuperAnalyticBlock_zero
  smul_mem' := fun c _ hF => hF.smul c

@[simp] theorem mem_superAnalyticBlocks (F : 𝒱 → ℂ → ℂ) :
    F ∈ V.superAnalyticBlocks ↔ V.IsSuperAnalyticBlock F := Iff.rfl

/-! ## Every block kills the relation space -/

/-- Evaluation of a super block at one point, regarded as a linear functional of the state. -/
noncomputable def IsSuperAnalyticBlock.linearAt {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) (z : ℂ) : 𝒱 →ₗ[ℂ] ℂ where
  toFun v := F v z
  map_add' v w := hF.addv v w z
  map_smul' c v := hF.smulv c v z

/-- Every analytic super block kills the deformed relation space at the evaluation point. -/
theorem IsSuperAnalyticBlock.superBlockRelSpan_le_kerAt {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) {z : ℂ} (hz : z ∈ imGT 0) :
    V.superBlockRelSpan z ≤ LinearMap.ker (hF.linearAt z) := by
  rw [superBlockRelSpan, Submodule.span_le]
  rintro x (⟨k, a, v, hk, ha, rfl⟩ | ⟨k, K, a, v, hk, ha, hK, rfl⟩)
  · exact hF.vanish_apply k hk ha v z
  · change F _ z = 0
    rw [hF.addv]
    have hsum : F (∑ m ∈ Finset.range K,
          (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuGC (m + 2) z)
            • V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) z
        = ∑ m ∈ Finset.range K, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z
            * F (V.superVSqZ a k (2 * (m + 2) - 2 : ℤ) v) z) := by
      induction Finset.range K using Finset.induction with
      | empty => simpa using hF.zerov z
      | insert m s hm ih =>
          rw [Finset.sum_insert hm, hF.addv, ih, Finset.sum_insert hm, hF.smulv]
          ring
    rw [hsum]
    have hlaw := hF.negTwo_tail k hk ha v hz
    rwa [superNegTwo_tail_finsum_eq_sum hF.zerov hK z] at hlaw

/-! ## One-point analytic determinacy -/

theorem IsSuperAnalyticBlock.analyticAt {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) {z : ℂ} (hz : z ∈ imGT 0) (v : 𝒱) :
    AnalyticAt ℂ (F v) z :=
  ((hF.holo v).analyticOnNhd (isOpen_imGT 0)) z hz

/-- The omega law solved for the derivative. -/
theorem IsSuperAnalyticBlock.deriv_eq_on {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) (v : 𝒱) {K : ℕ}
    (hK : ∀ m : ℕ, K ≤ m → V.superLsq (2 * (m + 1) - 2 : ℤ) v = 0)
    {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (F v) z
      = 2 * (Real.pi : ℂ) * Complex.I *
        (F (V.superLsq (-2) v) z
          - ∑ m ∈ Finset.range K, zhuGC (m + 1) z
            * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z) := by
  have hlaw := hF.omega v z hz
  rw [superOmega_finsum_eq_sum hF.zerov hK z] at hlaw
  have hc : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := two_pi_I_ne_zero
  calc
    _root_.deriv (F v) z
        = (2 * (Real.pi : ℂ) * Complex.I)
            * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z) := by
              rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = _ := by rw [hlaw]; ring

/-- If all values of a super block vanish at one point, all coefficient-weighted derivatives
vanish there. -/
theorem IsSuperAnalyticBlock.iteratedDeriv_coeff_eq_zero {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) {z0 : ℂ} (hz0 : z0 ∈ imGT 0)
    (hall : ∀ x : 𝒱, F x z0 = 0) (n : ℕ) :
    ∀ (g : ℂ → ℂ), AnalyticAt ℂ g z0 → ∀ v : 𝒱,
      iteratedDeriv n (fun z => g z * F v z) z0 = 0 := by
  induction n with
  | zero =>
      intro g _ v
      rw [iteratedDeriv_zero, hall v, mul_zero]
  | succ n ih =>
      intro g hg v
      obtain ⟨K, hK⟩ := V.superLsq_tail_eventually_zero v
      set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
      set a1 : ℂ → ℂ := fun z => _root_.deriv g z * F v z
      set a2 : ℂ → ℂ := fun z => (c * g z) * F (V.superLsq (-2) v) z
      set b : ℕ → ℂ → ℂ := fun m z =>
        (-c * g z * zhuGC (m + 1) z)
          * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) z
      set A : ℂ → ℂ := fun z => a1 z + a2 z
      set B : ℂ → ℂ := fun z => ∑ m ∈ Finset.range K, b m z
      have hEq : _root_.deriv (fun z => g z * F v z) =ᶠ[nhds z0]
          fun z => A z + B z := by
        filter_upwards [hg.eventually_analyticAt, (isOpen_imGT 0).mem_nhds hz0] with w hgw hw
        rw [deriv_fun_mul hgw.differentiableAt (hF.analyticAt hw v).differentiableAt,
          hF.deriv_eq_on v hK hw]
        simp only [A, B, a1, a2, b, c]
        rw [show g w * ((2 * (Real.pi : ℂ) * Complex.I) *
              (F (V.superLsq (-2) v) w - ∑ m ∈ Finset.range K,
                zhuGC (m + 1) w * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) w))
            = ((2 * (Real.pi : ℂ) * Complex.I) * g w) * F (V.superLsq (-2) v) w
              + (-(2 * (Real.pi : ℂ) * Complex.I) * g w)
                * ∑ m ∈ Finset.range K, zhuGC (m + 1) w
                  * F (V.superLsq (2 * (m + 1) - 2 : ℤ) v) w from by ring,
          Finset.mul_sum, ← add_assoc]
        congr 1
        exact Finset.sum_congr rfl (fun m _ => by ring)
      have ha1an : AnalyticAt ℂ a1 z0 := hg.deriv.mul (hF.analyticAt hz0 v)
      have ha2an : AnalyticAt ℂ a2 z0 := (analyticAt_const.mul hg).mul (hF.analyticAt hz0 _)
      have hban : ∀ m ∈ Finset.range K, AnalyticAt ℂ (b m) z0 := fun m _ =>
        ((analyticAt_const.mul hg).mul (analyticAt_zhuGC (m + 1) hz0)).mul
          (hF.analyticAt hz0 _)
      have hAan : AnalyticAt ℂ A z0 := ha1an.add ha2an
      have hBan : AnalyticAt ℂ B z0 := Finset.analyticAt_fun_sum _ hban
      rw [iteratedDeriv_succ', Filter.EventuallyEq.iteratedDeriv_eq n hEq,
        iteratedDeriv_add_of_analyticAt n hAan hBan,
        iteratedDeriv_add_of_analyticAt n ha1an ha2an,
        iteratedDeriv_sum_of_analyticAt (Finset.range K) b n hban,
        ih (_root_.deriv g) hg.deriv v,
        ih (fun z => c * g z) (analyticAt_const.mul hg) (V.superLsq (-2) v)]
      have hz : ∀ m ∈ Finset.range K, iteratedDeriv n (b m) z0 = 0 := fun m _ =>
        ih (fun z => -c * g z * zhuGC (m + 1) z)
          ((analyticAt_const.mul hg).mul (analyticAt_zhuGC (m + 1) hz0)) _
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      ring

/-- A super block vanishing at one point on every state vanishes on the upper half-plane. -/
theorem IsSuperAnalyticBlock.eq_zero_of_eq_zero_at {F : 𝒱 → ℂ → ℂ}
    (hF : V.IsSuperAnalyticBlock F) {z0 : ℂ} (hz0 : z0 ∈ imGT 0)
    (hall : ∀ x : 𝒱, F x z0 = 0) :
    ∀ (v : 𝒱), ∀ z ∈ imGT 0, F v z = 0 := by
  intro v
  have hloc : ∀ᶠ z in nhds z0, F v z = 0 := by
    refine eventuallyEq_zero_of_iteratedDeriv_eq_zero (hF.analyticAt hz0 v) (fun n => ?_)
    have h := hF.iteratedDeriv_coeff_eq_zero hz0 hall n
      (fun _ => 1) analyticAt_const v
    simpa using h
  intro z hz
  have h := eqOn_imGT_of_eventuallyEq (hF.holo v) (differentiableOn_const 0) hz0
    (by filter_upwards [hloc] with w hw using hw) hz
  exact h

/-! ## The finite determining-family bound -/

/-- The point-evaluation map used to bound the super block space. -/
noncomputable def superPtEval {ι : Type*} (t : ι → 𝒱) (z0 : ℂ) :
    (𝒱 → ℂ → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun F := fun i => F (t i) z0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem superPtEval_apply {ι : Type*} (t : ι → 𝒱) (z0 : ℂ)
    (F : 𝒱 → ℂ → ℂ) (i : ι) : superPtEval t z0 F i = F (t i) z0 := rfl

/-- The analytic super block space is bounded by any finite family spanning the state space
modulo the deformed super relation space at one point. -/
theorem finrank_superAnalyticBlocks_le_card_of_superBlockRel {z0 : ℂ}
    (hz0 : z0 ∈ imGT 0) (T : Finset 𝒱)
    (hT : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (T : Set 𝒱) ⊔ V.superBlockRelSpan z0) :
    FiniteDimensional ℂ (Submodule.map restrictImGT V.superAnalyticBlocks) ∧
      Module.finrank ℂ (Submodule.map restrictImGT V.superAnalyticBlocks) ≤ T.card := by
  classical
  set B : Submodule ℂ (𝒱 → ℂ → ℂ) :=
    Submodule.map restrictImGT V.superAnalyticBlocks
  have hinj : Function.Injective
      ((superPtEval (fun x : {y : 𝒱 // y ∈ T} => (x : 𝒱)) z0).domRestrict B) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨f, hf⟩ hker
    obtain ⟨F, hFmem, hFeq⟩ := hf
    have hFb : V.IsSuperAnalyticBlock F := hFmem
    have hTker : ∀ x ∈ T, F x z0 = 0 := by
      intro x hx
      have h := congrFun hker ⟨x, hx⟩
      simp only [LinearMap.domRestrict_apply, superPtEval_apply, Pi.zero_apply] at h
      rw [← hFeq, restrictImGT_apply _ hz0] at h
      exact h
    have hall : ∀ x : 𝒱, F x z0 = 0 := by
      intro x
      have hsub : (⊤ : Submodule ℂ 𝒱) ≤ LinearMap.ker (hFb.linearAt z0) := by
        rw [hT]
        refine sup_le ?_ (hFb.superBlockRelSpan_le_kerAt hz0)
        rw [Submodule.span_le]
        intro y hy
        exact hTker y hy
      exact hsub Submodule.mem_top
    have hzero := hFb.eq_zero_of_eq_zero_at hz0 hall
    refine Subtype.ext ?_
    show f = 0
    rw [← hFeq]
    funext v z
    by_cases hz : z ∈ imGT 0
    · rw [restrictImGT_apply _ hz, hzero v z hz]
      rfl
    · show Set.indicator (imGT 0) (F v) z = _
      rw [Set.indicator_of_notMem hz]
      rfl
  haveI : FiniteDimensional ℂ B :=
    FiniteDimensional.of_injective
      ((superPtEval (fun x : {y : 𝒱 // y ∈ T} => (x : 𝒱)) z0).domRestrict B) hinj
  refine ⟨inferInstance, ?_⟩
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (superPtEval (fun x : {y : 𝒱 // y ∈ T} => (x : 𝒱)) z0).domRestrict B) hinj
  have hcard : Module.finrank ℂ ({y : 𝒱 // y ∈ T} → ℂ) = T.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  rwa [hcard] at hle

end SuperNearVOA

end VOA
