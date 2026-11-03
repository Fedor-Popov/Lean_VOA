/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SqModeLinear
import VOA.Modularity.SqWeightNat

/-!
# Square-homogeneous genus-one blocks

`IsGradedBlock.negTwo` asks its first input to be simultaneously homogeneous for the ordinary
grading and for `L[0]`.  That is not Zhu's source-level condition: square-bracket modes are first
defined on ordinary-homogeneous inputs and then extended linearly.  This file records the corrected
normal form using `sqMode` and proves that every analytic block has it.

The slash action itself belongs to the square-weight decomposition and is developed below this
forward bridge.  No analyticity enters the algebraic extension of the two Zhu relations.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

section OrdinaryExtension

variable (W : VertexOperatorAlgebra V)

/-- Induction over the internal ordinary grading, kept local to the square-mode API. -/
theorem ordinaryGrading_induction {P : V → Prop}
    (hhom : ∀ k : ℤ, ∀ a ∈ W.grading k, P a) (hzero : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b)) (a : V) : P a := by
  have ha : a ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  exact Submodule.iSup_induction W.grading (motive := P) ha
    (fun k x hx ↦ hhom k x hx) hzero hadd

/-- The positive square-mode tail is eventually zero after linear extension in its first input. -/
theorem sqMode_tail_eventually_zero (a v : V) :
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → sqMode W (2 * (m + 2) - 2 : ℤ) a v = 0 := by
  refine ordinaryGrading_induction W (P := fun a ↦
    ∃ K : ℕ, ∀ m : ℕ, K ≤ m → sqMode W (2 * (m + 2) - 2 : ℤ) a v = 0) ?_ ?_ ?_ a
  · intro k x hx
    obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W x k.toNat v
    refine ⟨K, fun m hm ↦ ?_⟩
    rw [sqMode_of_mem_grading W hx]
    exact hK (m + 1) (by omega)
  · exact ⟨0, fun m _ ↦ by simp⟩
  · rintro x y ⟨Kx, hKx⟩ ⟨Ky, hKy⟩
    refine ⟨max Kx Ky, fun m hm ↦ ?_⟩
    rw [map_add, LinearMap.add_apply, hKx m (le_trans (le_max_left _ _) hm),
      hKy m (le_trans (le_max_right _ _) hm), add_zero]

end OrdinaryExtension

/-! ## The old bi-homogeneous domain is not vacuous in general -/

section PrimaryWeights

variable (W : VertexOperatorAlgebra V)

/-- An ordinary-homogeneous vector killed by all positive Virasoro modes is square-homogeneous of
the same weight.  Thus the bi-homogeneous domain in the two-mode predicate `SqModeWeighted` is not
empty in
general (even though it can miss `ω` when the central charge is nonzero). -/
theorem mem_sqWeightSpace_of_round_primary {k : ℤ} {a : V} (ha : a ∈ W.grading k)
    (hprimary : ∀ n : ℤ, 1 ≤ n → W.L n a = 0) : a ∈ sqWeightSpace W (k : ℂ) := by
  rw [mem_sqWeightSpace_iff, Lsq_zero_apply]
  rw [finsum_eq_single _ (0 : ℤ)]
  · rw [sqBracketCoeff_zero_diag, one_smul, W.L_zero_grading a ha]
  · intro n hn
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · rw [sqBracketCoeff_zero_of_neg hneg, zero_smul]
    · rw [hprimary n (by omega), smul_zero]

end PrimaryWeights

/-! ## The corrected normal form -/

/-- The tail summand in condition (ii), with square modes extended in the first input. -/
noncomputable def sqNegTwoTerm (W : VertexOperatorAlgebra V) (F : V → ℂ → ℂ)
    (a v : V) (z : ℂ) (m : ℕ) : ℂ :=
  ((2 * (m + 2) - 1 : ℕ) : ℂ) *
    (zhuGC (m + 2) z * F (sqMode W (2 * (m + 2) - 2 : ℤ) a v) z)

/-- Zhu's genus-one block conditions in the source-correct square-bracket normal form.

Linearity and conditions (i)--(ii) are global.  Condition (iii) is stated on an `L[0]` weight
space, exactly where the Serre derivative has a specified weight. -/
structure IsSqGradedBlock (W : VertexOperatorAlgebra V) (F : V → ℂ → ℂ) : Prop where
  holo : ∀ v : V, DifferentiableOn ℂ (F v) (imGT 0)
  addv : ∀ v w : V, ∀ z : ℂ, F (v + w) z = F v z + F w z
  smulv : ∀ c : ℂ, ∀ v : V, ∀ z : ℂ, F (c • v) z = c * F v z
  vanish : ∀ a v : V, F (sqMode W 0 a v) = 0
  negTwo : ∀ a v : V, ∀ z ∈ imGT 0,
    F (sqMode W (-2) a v) z + ∑ᶠ m : ℕ, sqNegTwoTerm W F a v z m = 0
  omega : ∀ (n : ℤ) (v : V), v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0,
    F (Lsq W (-2) v) z = serreDerivC n (F v) z
      + ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z

theorem IsSqGradedBlock.zerov {W : VertexOperatorAlgebra V} {F : V → ℂ → ℂ}
    (hF : IsSqGradedBlock W F) (z : ℂ) : F 0 z = 0 := by
  have h := hF.smulv 0 0 z
  simpa using h

section Forward

variable {W : VertexOperatorAlgebra V} {F : V → ℂ → ℂ}

private theorem sqNegTwoTerm_support_finite (hF : IsAnalyticBlock W F) (a v : V) (z : ℂ) :
    (Function.support fun m : ℕ ↦ sqNegTwoTerm W F a v z m).Finite := by
  obtain ⟨K, hK⟩ := sqMode_tail_eventually_zero W a v
  refine Set.Finite.subset (Set.finite_Iio K) (fun m hm ↦ ?_)
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Set.mem_Iio]
  by_contra hlt
  push_neg at hlt
  exact hm (by rw [sqNegTwoTerm, hK m hlt, hF.zerov]; ring)

private theorem analytic_vanish_all (hF : IsAnalyticBlock W F) :
    ∀ a v : V, F (sqMode W 0 a v) = 0 := by
  intro a v
  funext z
  refine ordinaryGrading_induction W (P := fun a ↦ F (sqMode W 0 a v) z = 0) ?_ ?_ ?_ a
  · intro k x hx
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have hx0 : x = 0 := by
        rw [W.positivity k hk, Submodule.mem_bot] at hx
        exact hx
      subst hx0
      rw [map_zero, LinearMap.zero_apply, hF.zerov]
    · rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [sqMode_of_mem_grading W (Submodule.smul_mem _ c W.vacuum_mem_grading_zero),
        vSqZ_smul_left, LinearMap.smul_apply, Int.toNat_zero, vSqZ_vacuum_scalar,
        sqBracketCoeffZ_vacuum_of_ne _ (by norm_num), zero_smul, smul_zero, hF.zerov]
    · have hkcast : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg (le_of_lt hk)).symm
      have hkpos : 1 ≤ k.toNat := by omega
      have hx' : x ∈ W.grading (k.toNat : ℤ) := by rwa [← hkcast]
      rw [sqMode_of_mem_grading W hx]
      exact congrFun (hF.vanish k.toNat hkpos x hx' v) z
  · change F (sqMode W 0 (0 : V) v) z = 0
    rw [map_zero, LinearMap.zero_apply, hF.zerov]
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply, hF.addv, hx, hy, add_zero]

private theorem analytic_negTwo_all (hF : IsAnalyticBlock W F) :
    ∀ a v : V, ∀ z ∈ imGT 0,
      F (sqMode W (-2) a v) z + ∑ᶠ m : ℕ, sqNegTwoTerm W F a v z m = 0 := by
  intro a v z hz
  refine ordinaryGrading_induction W (P := fun a ↦
    F (sqMode W (-2) a v) z + ∑ᶠ m : ℕ, sqNegTwoTerm W F a v z m = 0) ?_ ?_ ?_ a
  · intro k x hx
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have hx0 : x = 0 := by
        rw [W.positivity k hk, Submodule.mem_bot] at hx
        exact hx
      subst hx0
      have hlead : F (sqMode W (-2) (0 : V) v) z = 0 := by
        rw [map_zero, LinearMap.zero_apply, hF.zerov]
      have htail : ∀ m : ℕ, sqNegTwoTerm W F (0 : V) v z m = 0 := by
        intro m
        rw [sqNegTwoTerm, map_zero, LinearMap.zero_apply, hF.zerov]
        ring
      rw [hlead, finsum_congr htail, finsum_zero, add_zero]
    · rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      have hgrade : c • W.vacuum ∈ W.grading (0 : ℤ) :=
        Submodule.smul_mem _ c W.vacuum_mem_grading_zero
      rw [sqMode_of_mem_grading W hgrade, vSqZ_smul_left, LinearMap.smul_apply,
        Int.toNat_zero, vSqZ_vacuum_scalar,
        sqBracketCoeffZ_vacuum_of_ne _ (by norm_num), zero_smul,
        smul_zero, hF.zerov]
      have htail : ∀ m : ℕ, sqNegTwoTerm W F (c • W.vacuum) v z m = 0 := by
        intro m
        rw [sqNegTwoTerm, sqMode_of_mem_grading W hgrade, vSqZ_smul_left,
          LinearMap.smul_apply, Int.toNat_zero, vSqZ_vacuum_scalar,
          sqBracketCoeffZ_vacuum_of_ne _ (by omega), zero_smul, smul_zero, hF.zerov]
        ring
      rw [finsum_congr htail, finsum_zero, add_zero]
    · have hkcast : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg (le_of_lt hk)).symm
      have hkpos : 1 ≤ k.toNat := by omega
      have hx' : x ∈ W.grading (k.toNat : ℤ) := by rwa [← hkcast]
      rw [sqMode_of_mem_grading W hx]
      have hlaw := hF.negTwo_tail k.toNat hkpos hx' v hz
      simpa only [sqNegTwoTerm, sqMode_of_mem_grading W hx] using hlaw
  · change F (sqMode W (-2) (0 : V) v) z
        + ∑ᶠ m : ℕ, sqNegTwoTerm W F (0 : V) v z m = 0
    have hlead : F (sqMode W (-2) (0 : V) v) z = 0 := by
      rw [map_zero, LinearMap.zero_apply, hF.zerov]
    have htail : ∀ m : ℕ, sqNegTwoTerm W F (0 : V) v z m = 0 := by
      intro m
      rw [sqNegTwoTerm, map_zero, LinearMap.zero_apply, hF.zerov]
      ring
    rw [hlead, finsum_congr htail, finsum_zero, add_zero]
  · intro x y hx hy
    have htx := sqNegTwoTerm_support_finite hF x v z
    have hty := sqNegTwoTerm_support_finite hF y v z
    have hterm : ∀ m : ℕ,
        sqNegTwoTerm W F (x + y) v z m =
          sqNegTwoTerm W F x v z m + sqNegTwoTerm W F y v z m := by
      intro m
      rw [sqNegTwoTerm, sqNegTwoTerm, sqNegTwoTerm, map_add, LinearMap.add_apply, hF.addv]
      ring
    rw [map_add, LinearMap.add_apply, hF.addv, finsum_congr hterm,
      finsum_add_distrib htx hty]
    linear_combination hx + hy

/-- Every analytic block satisfies the source-correct square-homogeneous normal form. -/
theorem IsAnalyticBlock.toSqGradedBlock (hF : IsAnalyticBlock W F) :
    IsSqGradedBlock W F where
  holo := hF.holo
  addv := hF.addv
  smulv := hF.smulv
  vanish := analytic_vanish_all hF
  negTwo := analytic_negTwo_all hF
  omega := fun _ _ hv _ hz ↦ hF.omega_serre hv hz

end Forward

/-! ## Recovering the analytic presentation -/

section Reverse

variable {W : VertexOperatorAlgebra V} {F : V → ℂ → ℂ}

private theorem sqBlock_negTwo_round (hF : IsSqGradedBlock W F) (ka : ℕ) (hka : 1 ≤ ka)
    {a : V} (ha : a ∈ W.grading (ka : ℤ)) (v : V) {z : ℂ} (hz : z ∈ imGT 0) :
    F (vSqZ W a ka (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z) = 0 := by
  obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W a ka v
  let T : ℕ → ℂ := fun m ↦ ((2 * (m + 1) - 1 : ℕ) : ℂ)
    * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z)
  have hpeel : (∑ᶠ m : ℕ, T m) = T 0 + ∑ᶠ m : ℕ, T (m + 1) :=
    finsum_nat_peel (K := K) (fun m hm ↦ by
      dsimp only [T]
      rw [hK m hm, hF.zerov]
      ring)
  have h0 : T 0 = 0 := by
    dsimp only [T]
    have hv0 := congrFun (hF.vanish a v) z
    rw [sqMode_of_mem_grading W ha, Int.toNat_natCast] at hv0
    rw [show (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 by norm_num, hv0]
    simp
  have hshift : (∑ᶠ m : ℕ, T (m + 1)) = ∑ᶠ m : ℕ, sqNegTwoTerm W F a v z m := by
    refine finsum_congr (fun m ↦ ?_)
    dsimp only [T]
    rw [sqNegTwoTerm]
    have hmode : sqMode W (2 * (m + 2) - 2 : ℤ) a
        = vSqZ W a ka (2 * (m + 2) - 2 : ℤ) := by
      simpa only [Int.toNat_natCast] using
        (sqMode_of_mem_grading W ha (2 * (m + 2) - 2 : ℤ))
    rw [show (2 * (((m + 1 : ℕ)) + 1) - 1 : ℕ) = 2 * (m + 2) - 1 by omega,
      show (2 * (((m + 1 : ℕ)) + 1) - 2 : ℤ) = 2 * (m + 2) - 2 by
        push_cast; ring,
      hmode]
  have hlaw := hF.negTwo a v z hz
  rw [sqMode_of_mem_grading W ha, Int.toNat_natCast] at hlaw
  rw [hpeel, h0, zero_add, hshift, hlaw]

private theorem sqBlock_omega_round (hF : IsSqGradedBlock W F) {n : ℤ} {v : V}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) {z : ℂ} (hz : z ∈ imGT 0) :
    F (Lsq W (-2) v) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z := by
  change F (Lsq W (-2) v) z
    = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
      + ∑ᶠ m : ℕ, omegaTerm W F v z m
  obtain ⟨K, hK⟩ := Lsq_tail_eventually_zero W v
  have hpeel : (∑ᶠ m : ℕ, omegaTerm W F v z m)
      = omegaTerm W F v z 0 + ∑ᶠ m : ℕ, omegaTerm W F v z (m + 1) :=
    finsum_nat_peel (K := K) (fun m hm ↦ by
      rw [omegaTerm, hK m hm, hF.zerov]
      ring)
  have hL0 : Lsq W 0 v = (n : ℂ) • v := (mem_sqWeightSpace_iff W _ v).mp hv
  have h0 : omegaTerm W F v z 0
      = (n : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * (G2C z * F v z) := by
    rw [omegaTerm_zero, hL0, hF.smulv, zhuGC_one hz]
    ring
  have hshift : (∑ᶠ m : ℕ, omegaTerm W F v z (m + 1))
      = ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z :=
    finsum_congr (fun m ↦ omegaTerm_succ F v z m)
  rw [hpeel, h0, hshift, hF.omega n v hv z hz, serreDerivC]
  ring

private theorem sqBlock_omega_zero (hF : IsSqGradedBlock W F) {z : ℂ} (hz : z ∈ imGT 0) :
    F (Lsq W (-2) (0 : V)) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F 0) z
        + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) 0) z := by
  have hfun : F (0 : V) = 0 := by funext w; exact hF.zerov w
  have hd : _root_.deriv (0 : ℂ → ℂ) z = 0 := deriv_const z 0
  rw [map_zero, hF.zerov, hfun, hd]
  have htail : ∀ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) 0) z = 0 := by
    intro m
    rw [map_zero, hF.zerov, mul_zero]
  rw [finsum_congr htail, finsum_zero]
  ring

private theorem sqBlock_omega_add (hF : IsSqGradedBlock W F) {u v : V} {z : ℂ}
    (hz : z ∈ imGT 0)
    (hu : F (Lsq W (-2) u) z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F u) z
      + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) u) z)
    (hv : F (Lsq W (-2) v) z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
      + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z) :
    F (Lsq W (-2) (u + v)) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F (u + v)) z
        + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) (u + v)) z := by
  obtain ⟨Ku, hKu⟩ := Lsq_tail_eventually_zero W u
  obtain ⟨Kv, hKv⟩ := Lsq_tail_eventually_zero W v
  have hsu : (Function.support fun m : ℕ ↦
      zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) u) z).Finite := by
    refine Set.Finite.subset (Set.finite_Iio Ku) (fun m hm ↦ ?_)
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Set.mem_Iio]
    by_contra hlt
    push Not at hlt
    exact hm (by rw [hKu m hlt, hF.zerov, mul_zero])
  have hsv : (Function.support fun m : ℕ ↦
      zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z).Finite := by
    refine Set.Finite.subset (Set.finite_Iio Kv) (fun m hm ↦ ?_)
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Set.mem_Iio]
    by_contra hlt
    push Not at hlt
    exact hm (by rw [hKv m hlt, hF.zerov, mul_zero])
  have hfun : F (u + v) = F u + F v := by funext w; exact hF.addv u v w
  have hd : _root_.deriv (F (u + v)) z = _root_.deriv (F u) z + _root_.deriv (F v) z := by
    rw [hfun]
    exact deriv_add ((hF.holo u).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
      ((hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds hz))
  have hterm : ∀ m : ℕ,
      zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) (u + v)) z
        = zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) u) z
          + zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z := by
    intro m
    rw [map_add, hF.addv]
    ring
  rw [map_add, hF.addv, hd, finsum_congr hterm, finsum_add_distrib hsu hsv]
  linear_combination hu + hv

/-- The corrected square-homogeneous normal form is equivalent to the original analytic block
conditions.  The reverse direction uses only the proved natural square-weight spanning theorem;
it does not use square-mode weight covariance. -/
theorem IsSqGradedBlock.toAnalyticBlock (hF : IsSqGradedBlock W F) : IsAnalyticBlock W F where
  holo := hF.holo
  addv := hF.addv
  smulv := hF.smulv
  vanish := fun ka hka a ha v ↦ by
    have h := hF.vanish a v
    rw [sqMode_of_mem_grading W ha, Int.toNat_natCast] at h
    exact h
  negTwo := fun ka hka a ha v z hz ↦ sqBlock_negTwo_round hF ka hka ha v hz
  omega := fun v z hz ↦ by
    have hvtop : v ∈ ⨆ m : ℕ, sqWeightSpace W ((m : ℕ) : ℂ) := by
      rw [sqWeightSpace_nat_spans_top]
      exact Submodule.mem_top
    exact Submodule.iSup_induction (fun m : ℕ ↦ sqWeightSpace W ((m : ℕ) : ℂ))
      (motive := fun x ↦ F (Lsq W (-2) x) z
        = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F x) z
          + ∑ᶠ m : ℕ, zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) x) z)
      hvtop
      (fun m x hx ↦ sqBlock_omega_round hF
        (n := (m : ℤ)) (by simpa only [Int.cast_natCast] using hx) hz)
      (sqBlock_omega_zero hF hz)
      (fun _ _ hu hv ↦ sqBlock_omega_add hF hz hu hv)

end Reverse

/-! ## The source-correct slash operator -/

section SquareSlash

variable (W : VertexOperatorAlgebra V)

/-- The natural square-weight spaces form an internal direct sum. -/
theorem sqWeightSpaceNat_isInternal :
    DirectSum.IsInternal (fun n : ℕ ↦ sqWeightSpace W ((n : ℕ) : ℂ)) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_
    (sqWeightSpace_nat_spans_top W)
  exact (sqWeightSpace_iSupIndep W).comp (fun _ _ h ↦ Nat.cast_injective h)

/-- A globally linear family, packaged as a linear map in the vector input. -/
noncomputable def sqBlockLinear {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F) :
    V →ₗ[ℂ] (ℂ → ℂ) where
  toFun := F
  map_add' v w := by funext z; exact hF.addv v w z
  map_smul' c v := by funext z; exact hF.smulv c v z

/-- Slash by a fixed weight is linear in the function being slashed. -/
noncomputable def slashCLinear (n : ℤ) (gamma : SL(2, ℤ)) :
    (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f := slashC n gamma f
  map_add' f g := by
    funext z
    change (f (mobiusC gamma z) + g (mobiusC gamma z)) * denomC gamma z ^ (-n) = _
    rw [Pi.add_apply]
    change _ = f (mobiusC gamma z) * denomC gamma z ^ (-n)
      + g (mobiusC gamma z) * denomC gamma z ^ (-n)
    ring
  map_smul' c f := by
    funext z
    change (c * f (mobiusC gamma z)) * denomC gamma z ^ (-n)
      = c * (f (mobiusC gamma z) * denomC gamma z ^ (-n))
    ring

/-- The slash map on one square-weight summand. -/
noncomputable def sqSlashFamily {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) (n : ℕ) :
    sqWeightSpace W ((n : ℕ) : ℂ) →ₗ[ℂ] (ℂ → ℂ) :=
  (slashCLinear (n : ℤ) gamma).comp ((sqBlockLinear W hF).comp
    (sqWeightSpace W ((n : ℕ) : ℂ)).subtype)

/-- The source-correct slash action: decompose into square-weight summands, slash each summand by
its weight, and add.  Unlike `blockSlash`, this is a genuine global linear map. -/
noncomputable def sqBlockSlashLinear {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) : V →ₗ[ℂ] (ℂ → ℂ) := by
  letI := DirectSum.IsInternal.chooseDecomposition
    (fun n : ℕ ↦ sqWeightSpace W ((n : ℕ) : ℂ)) (sqWeightSpaceNat_isInternal W)
  exact (DFinsupp.lsum ℂ (sqSlashFamily W hF gamma)).comp
    (DirectSum.decomposeLinearEquiv (fun n : ℕ ↦ sqWeightSpace W ((n : ℕ) : ℂ))).toLinearMap

/-- Function-valued form of the source-correct slash. -/
noncomputable def sqBlockSlash {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) : V → ℂ → ℂ := sqBlockSlashLinear W hF gamma

@[simp] theorem sqBlockSlash_add {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) (v w : V) :
    sqBlockSlash W hF gamma (v + w) = sqBlockSlash W hF gamma v + sqBlockSlash W hF gamma w :=
  map_add (sqBlockSlashLinear W hF gamma) v w

@[simp] theorem sqBlockSlash_smul {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) (c : ℂ) (v : V) :
    sqBlockSlash W hF gamma (c • v) = c • sqBlockSlash W hF gamma v :=
  map_smul (sqBlockSlashLinear W hF gamma) c v

/-- On a homogeneous input, the linear extension is the usual slash of the matching weight. -/
theorem sqBlockSlash_of_mem {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) {n : ℕ} {v : V} (hv : v ∈ sqWeightSpace W ((n : ℕ) : ℂ)) :
    sqBlockSlash W hF gamma v = slashC (n : ℤ) gamma (F v) := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition
    (fun n : ℕ ↦ sqWeightSpace W ((n : ℕ) : ℂ)) (sqWeightSpaceNat_isInternal W)
  have hdec : DirectSum.decompose (fun n : ℕ ↦ sqWeightSpace W ((n : ℕ) : ℂ)) v
      = DirectSum.of (fun n : ℕ ↦ (sqWeightSpace W ((n : ℕ) : ℂ) : Submodule ℂ V))
        n ⟨v, hv⟩ :=
    DirectSum.decompose_coe
      (ℳ := fun n : ℕ ↦ (sqWeightSpace W ((n : ℕ) : ℂ) : Submodule ℂ V)) ⟨v, hv⟩
  change (DFinsupp.lsum ℂ (sqSlashFamily W hF gamma))
    (DirectSum.decompose (fun n : ℕ ↦ sqWeightSpace W ((n : ℕ) : ℂ)) v) = _
  rw [hdec]
  change (DFinsupp.lsum ℂ (sqSlashFamily W hF gamma))
    (DFinsupp.single n ⟨v, hv⟩) = _
  rw [DFinsupp.lsum_single]
  rfl

/-- Negative integer square-weight spaces vanish. -/
theorem sqWeightSpace_eq_bot_of_neg {n : ℤ} (hn : n < 0) :
    sqWeightSpace W (n : ℂ) = ⊥ := by
  have hind := sqWeightSpace_iSupIndep W (n : ℂ)
  have htop : (⊤ : Submodule ℂ V) ≤
      ⨆ j : {j : ℂ // j ≠ (n : ℂ)}, sqWeightSpace W (j : ℂ) := by
    rw [← sqWeightSpace_nat_spans_top W]
    refine iSup_le (fun m ↦ ?_)
    refine le_iSup_of_le
      (⟨(m : ℂ), fun h ↦ ?_⟩ : {j : ℂ // j ≠ (n : ℂ)}) le_rfl
    have : (m : ℤ) = n := by exact_mod_cast h
    omega
  have hsupp : (⨆ j : {j : ℂ // j ≠ (n : ℂ)}, sqWeightSpace W (j : ℂ)) = ⊤ :=
    eq_top_iff.mpr htop
  rw [iSup_subtype] at hsupp
  rw [hsupp] at hind
  exact disjoint_top.mp hind

/-- The corrected slash satisfies the same homogeneous-point relation as the old pointwise slash. -/
theorem isSlashOf_sqBlockSlash {F : V → ℂ → ℂ} (hF : IsSqGradedBlock W F)
    (gamma : SL(2, ℤ)) : IsSlashOf W gamma F (sqBlockSlash W hF gamma) := by
  intro n v hv z hz
  by_cases hv0 : v = 0
  · subst hv0
    have hF0 : F (0 : V) = 0 := by funext w; exact hF.zerov w
    change (sqBlockSlashLinear W hF gamma) 0 z = slashC n gamma (F 0) z
    rw [map_zero, hF0]
    change (0 : ℂ) = 0 * denomC gamma z ^ (-n)
    ring
  have hn : 0 ≤ n := by
    by_contra hn
    rw [sqWeightSpace_eq_bot_of_neg W (by omega), Submodule.mem_bot] at hv
    exact hv0 hv
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact congrFun (sqBlockSlash_of_mem W hF gamma (by simpa only [Int.cast_natCast] using hv)) z

end SquareSlash

end VOA
