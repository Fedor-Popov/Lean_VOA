/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuRecursionClose
import VOA.Modularity.GrowthBound
import VOA.Modules.ZhuModule

/-!
# Zhu's genus-one block conditions from the closed recursion

With `zhuRecursionPinned_holds` in hand, Zhu's condition (iii) on genus-one conformal blocks — the
`ω`-recursion `𝒵_M(L[−2]v) = q d/dq 𝒵_M(v) + Σ_k G_{2k} ⋆ 𝒵_M(L[2k−2]v)`, the seed of the modular
linear differential equation (Zhu 5.1.2, Gannon §5.3.5) — is a direct corollary: `o(ω) = L₀` acts by
the degree, and the two `c/24` shifts cancel.

## Status
Proved, axiom-clean, `pbw`-free.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (N : OrdVModule W M)

/-! ## The `ω`-specialisation: Zhu's block condition (iii), the seed of the modular ODE -/

/-- The formal Euler operator `q·d/dq` on `q`-series: `q^e ↦ e·q^e`. -/
noncomputable def qDeriv (χ : FormalQSeries) : FormalQSeries := fun e => e * χ e

/-- `tr(L₀·A·q^{L₀−c/24})(e) = (e + c/24)·tr(A·q^{L₀−c/24})(e)`. -/
theorem gradedTraceOp_L0_mul (A : Module.End ℂ M) (e : ℂ) :
    gradedTraceOp N (mode (N.YM W.conformalVector) 1 * A) e
      = (e + W.centralCharge / 24) * gradedTraceOp N A e := by
  haveI := N.finrank (e + W.centralCharge / 24)
  set α := e + W.centralCharge / 24 with hα
  have hblk : weightBlock N (mode (N.YM W.conformalVector) 1 * A) α = α • weightBlock N A α := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.isInternal α) (mode (N.YM W.conformalVector) 1 (A (y : M))) : M)
      = ((α • (internalProjTo N.isInternal α) (A (y : M)) : N.weight α) : M)
    -- `L₀` acts on `M_α` by `α`; the projection commutes with `L₀` since `L₀` preserves each weight
    have hproj : ∀ x : M, internalProjTo N.isInternal α (mode (N.YM W.conformalVector) 1 x)
        = α • internalProjTo N.isInternal α x := by
      intro x
      classical
      -- decompose `x` into its weight components
      letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
      have hdec := DirectSum.sum_support_decompose N.weight x
      conv_lhs => rw [← hdec]
      conv_rhs => rw [← hdec]
      rw [map_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      have hβ : ((DirectSum.decompose N.weight x β : N.weight β) : M) ∈ N.weight β :=
        (DirectSum.decompose N.weight x β).2
      rw [N.L0_weight β _ hβ, map_smul]
      by_cases hβα : β = α
      · subst hβα; rfl
      · rw [internalProjTo_eq_zero_of_ne' N hβ (Ne.symm hβα), smul_zero, smul_zero]
    rw [hproj]
  change LinearMap.trace ℂ _ (weightBlock N (mode (N.YM W.conformalVector) 1 * A) α)
    = α * LinearMap.trace ℂ _ (weightBlock N A α)
  rw [hblk, map_smul, smul_eq_mul]

/-- `o(ω) = L₀`. -/
theorem oMod_conformalVector : oMod N W.conformalVector = mode (N.YM W.conformalVector) 1 := by
  rw [oMod_of_mem_grading N W.conformalVector_mem_grading_two]
  norm_num

/-- **Zhu's condition (iii) — the `ω`-recursion, i.e. the seed of the modular linear
differential equation** (Zhu 5.1.2 / Gannon 5.3.17):

  `𝒵_M(L[−2]v) = q·(d/dq) 𝒵_M(v) + Σ_{k≥1} G_{2k} ⋆ 𝒵_M(L[2k−2]v)`.

The `−c/24` in `L[−2] = ω[−1] − (c/24)·id` and the `+c/24` in `tr(L₀ o(v) q^{L₀−c/24}) =
(q d/dq + c/24)𝒵_M(v)` cancel exactly — a consistency check on the ω̃-based `Lsq`. -/
theorem zhuRecursion_omega (v : 𝒱) :
    torusOnePoint N (Lsq W (-2) v)
      = qDeriv (torusOnePoint N v)
        + ∑ᶠ k : ℕ, qConv (zhuG (k + 1)) (torusOnePoint N (Lsq W (2 * (k + 1) - 2 : ℤ) v)) := by
  have hrec := zhuRecursionPinned_holds N (ka := 2) (by norm_num)
    W.conformalVector_mem_grading_two v
  rw [ZhuRecursionPinned, ZhuRecursionAt] at hrec
  -- `ω[−1] = L[−2] + (c/24)·id`
  have hm1 : vSqZ W W.conformalVector 2 (-1) v = Lsq W (-2) v + (W.centralCharge / 24) • v := by
    rw [Lsq_apply, show (-2 : ℤ) + 1 = -1 from by norm_num, sqBracketCoeffZ_vacuum_neg_one, mul_one,
      sub_add_cancel]
  -- `ω[2k+1] = L[2k]`
  have hodd : ∀ k : ℕ, vSqZ W W.conformalVector 2 (2 * (k + 1) - 1 : ℤ) v
      = Lsq W (2 * (k + 1) - 2 : ℤ) v := by
    intro k
    rw [Lsq_apply, show (2 * (k + 1) - 2 : ℤ) + 1 = 2 * (k + 1) - 1 from by ring,
      sqBracketCoeffZ_vacuum_of_ne _ (by omega), mul_zero, zero_smul, sub_zero]
  -- the two-point term is `(q d/dq + c/24)𝒵_M(v)`
  have htwo : torusTwoPoint N W.conformalVector v
      = qDeriv (torusOnePoint N v) + (W.centralCharge / 24) • torusOnePoint N v := by
    funext e
    rw [torusTwoPoint_eq_gradedTraceOp, oMod_conformalVector, gradedTraceOp_L0_mul, Pi.add_apply,
      Pi.smul_apply, qDeriv, smul_eq_mul]
    rw [show torusOnePoint N v = gradedTraceOp N (oMod N v) from rfl]
    ring
  rw [hm1, torusOnePoint_add, torusOnePoint_smul, htwo] at hrec
  simp_rw [hodd] at hrec
  -- cancel the `(c/24)·𝒵_M(v)` on both sides
  funext e
  have h := congrFun hrec e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [Pi.add_apply]
  linear_combination h


/-! ## Block condition (ii): the `L[−1]`-derivation and Zhu's `[−2]`-identity (Prop. 4.3.3) -/

section LsqDerivation

open PowerSeries

/-- The generating function of the `a[m]`-weights: `G_m = (1+w)^{k−1}·u^m`. -/
noncomputable def sqGen (k : ℕ) (m : ℤ) : PowerSeries ℂ :=
  ((onePlusXUnit ^ ((k : ℤ) - 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
    * ((uUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)

theorem sqBracketCoeffZ_eq_coeff_sqGen (k : ℕ) (m : ℤ) (d : ℕ) :
    sqBracketCoeffZ k m (m + d) = coeff d (sqGen k m) := sqBracketCoeffZ_eq_coeff k m d

/-- **The differential identity behind the `L[−1]`-derivation**:
`w(1+w)·G_m′ = (k−1)w·G_m + m·G_{m−1} − m(1+w)·G_m`  (for `k ≥ 1`). -/
theorem sqGen_ode {k : ℕ} (hk : 1 ≤ k) (m : ℤ) :
    X * (1 + X) * derivativeFun (sqGen k m)
      = PowerSeries.C (((k : ℂ) - 1)) * X * sqGen k m + PowerSeries.C (m : ℂ) * sqGen k (m - 1)
        - PowerSeries.C (m : ℂ) * (1 + X) * sqGen k m := by
  set A : PowerSeries ℂ := (1 + X) ^ (k - 1) with hA
  set U : PowerSeries ℂ := ((uUnit ^ m : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) with hU
  set U' : PowerSeries ℂ := ((uUnit ^ (m - 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) with hU'
  have hGm : sqGen k m = A * U := by
    rw [sqGen, onePlusXUnit_zpow_of_one_le hk]
  have hGm1 : sqGen k (m - 1) = A * U' := by
    rw [sqGen, onePlusXUnit_zpow_of_one_le hk]
  -- `U = U' · u`
  have hUU : U = U' * uSeries := by
    rw [hU, hU', ← uUnit_coe, ← Units.val_mul, ← zpow_add_one, sub_add_cancel]
  -- `(1+X)·A′ = (k−1)·A`
  have hAode : (1 + X) * derivativeFun A = PowerSeries.C ((k : ℂ) - 1) * A := by
    have h := onePlusX_pow_ode (k - 1)
    rw [smul_eq_C_mul] at h
    rw [hA]
    convert h using 3
    rw [Nat.cast_sub hk, Nat.cast_one]
  -- `U′ = m·U'·u′`
  have hUder : derivativeFun U = PowerSeries.C (m : ℂ) * U' * derivativeFun uSeries := by
    rw [hU, derivativeFun_uUnit_zpow, hU', map_intCast]
  -- the `u`-ODE: `(1+X)(u + X u′) = 1`
  have hODE := uSeries_ODE
  rw [hGm, hGm1, derivativeFun_mul]
  linear_combination (X * U) * hAode + (X * (1 + X) * A) * hUder
    + (PowerSeries.C (m : ℂ) * A * U') * hODE + (PowerSeries.C (m : ℂ) * (1 + X) * A) * hUU

/-- **The `L[−1]`-derivation coefficient identity**:
`(k−1−i)·c(k,m,i) − (i+1)·c(k,m,i+1) = −m·c(k,m−1,i)`  (`k ≥ 1`, all `m i : ℤ`). -/
theorem sqBracketCoeffZ_derivation {k : ℕ} (hk : 1 ≤ k) (m i : ℤ) :
    ((k : ℂ) - 1 - i) * sqBracketCoeffZ k m i - ((i : ℂ) + 1) * sqBracketCoeffZ k m (i + 1)
      = -(m : ℂ) * sqBracketCoeffZ k (m - 1) i := by
  rcases lt_trichotomy i (m - 1) with hlt | heq | hgt
  · rw [sqBracketCoeffZ_of_lt k (by omega), sqBracketCoeffZ_of_lt k (by omega),
      sqBracketCoeffZ_of_lt k (by omega)]
    ring
  · subst heq
    rw [sqBracketCoeffZ_of_lt k (by omega), show m - 1 + 1 = m from by ring, sqBracketCoeffZ_diag',
      sqBracketCoeffZ_diag']
    push_cast
    ring
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, i = m + j := ⟨(i - m).toNat, by omega⟩
    subst hj
    rw [show m + (j : ℤ) + 1 = m + ((j + 1 : ℕ) : ℤ) from by push_cast; ring,
      show m + (j : ℤ) = (m - 1) + ((j + 1 : ℕ) : ℤ) from by push_cast; ring,
      sqBracketCoeffZ_eq_coeff_sqGen, sqBracketCoeffZ_eq_coeff_sqGen,
      show (m - 1) + ((j + 1 : ℕ) : ℤ) = m + (j : ℤ) from by push_cast; ring,
      sqBracketCoeffZ_eq_coeff_sqGen]
    have h := congrArg (coeff (j + 1)) (sqGen_ode hk m)
    rw [map_sub, map_add] at h
    simp only [map_add, mul_assoc, mul_add, add_mul, one_mul, PowerSeries.coeff_C_mul,
      coeff_succ_X_mul, coeff_derivativeFun, coeff_X_mul_derivativeFun] at h
    push_cast
    linear_combination -h

end LsqDerivation

section LsqCommutator

variable {W : VertexOperatorAlgebra 𝒱}

/-- `[L₋₁, a₍ᵢ₎] = −i·a₍ᵢ₋₁₎` on `𝒱` (translation covariance, from the commutator formula at
`ω₍₀₎ = L₋₁` and `Y(L₋₁a) = ∂Y(a)`). -/
theorem L_neg_one_mode_comm (a v : 𝒱) (i : ℤ) :
    W.L (-1) (mode (W.Y a) i v) - mode (W.Y a) i (W.L (-1) v) = (-i : ℂ) • mode (W.Y a) (i - 1) v := by
  have h := mode_commutator (adjointWeakModule W) W.conformalVector a v 0 i
  change mode (W.Y W.conformalVector) 0 (mode (W.Y a) i v) - mode (W.Y a) i (mode (W.Y W.conformalVector) 0 v)
    = ∑ᶠ j : ℤ, cbz 0 j • mode (W.Y (W.smul W.conformalVector j a)) (0 + i - j) v at h
  rw [finsum_eq_single _ (0 : ℤ) (fun j hj => by rw [cbz_zero_left, if_neg hj, zero_smul]),
    cbz_zero_left, if_pos rfl, one_smul, zero_add, sub_zero] at h
  rw [VertexOperatorAlgebra.L_def, show (-1 : ℤ) + 1 = 0 from by norm_num, h,
    show W.smul W.conformalVector 0 a = mode (W.Y W.conformalVector) 0 a from rfl,
    W.translation a, mode_deriv, ← Int.cast_neg, Int.cast_smul_eq_zsmul]
  rfl

/-- `[L₀, a₍ᵢ₎] = (k−i−1)·a₍ᵢ₎` on `𝒱` for `a ∈ 𝒱ₖ`. -/
theorem L_zero_mode_comm {k : ℤ} {a : 𝒱} (ha : a ∈ W.grading k) (v : 𝒱) (i : ℤ) :
    W.L 0 (mode (W.Y a) i v) - mode (W.Y a) i (W.L 0 v) = ((k : ℂ) - i - 1) • mode (W.Y a) i v := by
  have h := mode_commutator (adjointWeakModule W) W.conformalVector a v 1 i
  change mode (W.Y W.conformalVector) 1 (mode (W.Y a) i v) - mode (W.Y a) i (mode (W.Y W.conformalVector) 1 v)
    = ∑ᶠ j : ℤ, cbz 1 j • mode (W.Y (W.smul W.conformalVector j a)) (1 + i - j) v at h
  have hsupp : (Function.support fun j : ℤ =>
      cbz 1 j • mode (W.Y (W.smul W.conformalVector j a)) (1 + i - j) v) ⊆ ↑({0, 1} : Finset ℤ) := by
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hc
    push_neg at hc
    refine hj ?_
    by_cases hneg : j < 0
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · push_neg at hneg
      rw [cbz_eq_zero_of_lt (by norm_num) (by omega), zero_smul]
  rw [finsum_eq_finset_sum_of_support_subset _ hsupp, Finset.sum_pair (by norm_num)] at h
  have hc0 : cbz 1 0 = 1 := cbz_zero 1
  have hc1 : cbz 1 1 = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num), show ((1 : ℤ)).toNat = 1 from rfl,
      show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, gBinom_natCast]
    simp
  rw [hc0, hc1, one_smul, one_smul, sub_zero, add_sub_cancel_left,
    show W.smul W.conformalVector 0 a = mode (W.Y W.conformalVector) 0 a from rfl,
    show W.smul W.conformalVector 1 a = mode (W.Y W.conformalVector) 1 a from rfl,
    W.translation a, mode_deriv, W.L0_grading a ha, map_smul, mode_smul, LinearMap.smul_apply,
    LinearMap.smul_apply] at h
  rw [VertexOperatorAlgebra.L_def, zero_add, h, show (1 + i - 1 : ℤ) = i from by ring,
    ← Int.cast_smul_eq_zsmul ℂ, ← add_smul]
  congr 1
  push_cast
  ring

/-- **The `L[−1]`-derivation**: `[L[−1], a[m]] = −m·a[m−1]` for homogeneous `a ∈ 𝒱ₖ`, `k ≥ 1`
(Zhu, Lemma 4.3.1 style; `L[−1] = L₋₁ + L₀`, `Lsq_neg_one`). -/
theorem Lsq_neg_one_vSqZ_comm {k : ℕ} (hk : 1 ≤ k) {a : 𝒱} (ha : a ∈ W.grading (k : ℤ)) (m : ℤ)
    (v : 𝒱) :
    Lsq W (-1) (vSqZ W a k m v) - vSqZ W a k m (Lsq W (-1) v)
      = (-(m : ℂ)) • vSqZ W a k (m - 1) v := by
  obtain ⟨R, hR⟩ := W.regularity a v
  -- pointwise commutator with `a₍ᵢ₎`
  have hcomm : ∀ i : ℤ, (W.L (-1) + W.L 0) (mode (W.Y a) i v) - mode (W.Y a) i ((W.L (-1) + W.L 0) v)
      = (-i : ℂ) • mode (W.Y a) (i - 1) v + ((k : ℂ) - i - 1) • mode (W.Y a) i v := by
    intro i
    have h1 := L_neg_one_mode_comm (W := W) a v i
    have h2 := L_zero_mode_comm ha v i
    rw [Int.cast_natCast] at h2
    simp only [LinearMap.add_apply, map_add]
    rw [← h1, ← h2]
    abel
  -- expand `a[m]` and distribute
  have hfinL : (Function.support fun i : ℤ =>
      sqBracketCoeffZ k m i • mode (W.Y a) i v).Finite := sqModeZ_support_finite W a k m v
  have hexp : Lsq W (-1) (vSqZ W a k m v) - vSqZ W a k m (Lsq W (-1) v)
      = ∑ᶠ i : ℤ, sqBracketCoeffZ k m i •
          ((W.L (-1) + W.L 0) (mode (W.Y a) i v) - mode (W.Y a) i ((W.L (-1) + W.L 0) v)) := by
    rw [Lsq_neg_one, vSqZ_apply, vSqZ_apply, map_finsum _ hfinL]
    have hfin2 : (Function.support fun i : ℤ =>
        sqBracketCoeffZ k m i • mode (W.Y a) i ((W.L (-1) + W.L 0) v)).Finite :=
      sqModeZ_support_finite W a k m ((W.L (-1) + W.L 0) v)
    rw [← finsum_sub_distrib (by
        refine hfinL.subset (fun i hi => ?_)
        simp only [Function.mem_support, ne_eq] at hi ⊢
        intro h0; exact hi (by rw [h0, map_zero])) hfin2]
    refine finsum_congr (fun i => ?_)
    rw [map_smul, smul_sub]
  rw [hexp]
  simp_rw [hcomm]
  -- split into the two families and reindex the shifted one
  have hfinA : (Function.support fun i : ℤ =>
      sqBracketCoeffZ k m i • ((-i : ℂ) • mode (W.Y a) (i - 1) v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc m R) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hc; push_neg at hc
      exact hi (by rw [sqBracketCoeffZ_of_lt k hc, zero_smul])
    · by_contra hc; push_neg at hc
      exact hi (by rw [hR (i - 1) (by omega), smul_zero, smul_zero])
  have hfinB : (Function.support fun i : ℤ =>
      sqBracketCoeffZ k m i • (((k : ℂ) - i - 1) • mode (W.Y a) i v)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc m R) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hc; push_neg at hc
      exact hi (by rw [sqBracketCoeffZ_of_lt k hc, zero_smul])
    · by_contra hc; push_neg at hc
      exact hi (by rw [hR i (by omega), smul_zero, smul_zero])
  simp_rw [smul_add]
  rw [finsum_add_distrib hfinA hfinB]
  -- reindex `i ↦ i + 1` in the first family
  have hshift : (∑ᶠ i : ℤ, sqBracketCoeffZ k m i • ((-i : ℂ) • mode (W.Y a) (i - 1) v))
      = ∑ᶠ i : ℤ, sqBracketCoeffZ k m (i + 1) • ((-(i + 1) : ℂ) • mode (W.Y a) i v) := by
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    refine finsum_congr (fun i => ?_)
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    push_cast
    ring_nf
  rw [hshift, ← finsum_add_distrib]
  · rw [vSqZ_apply, smul_finsum' _ (sqModeZ_support_finite W a k (m - 1) v)]
    refine finsum_congr (fun i => ?_)
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    have := sqBracketCoeffZ_derivation hk m i
    push_cast at this ⊢
    linear_combination this
  · refine Set.Finite.subset (Set.finite_Icc (m - 1) R) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    simp only [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hc; push_neg at hc
      exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
    · by_contra hc; push_neg at hc
      exact hi (by rw [hR i (by omega), smul_zero, smul_zero])
  · exact hfinB

end LsqCommutator


/-! ## Zhu's `[−2]`-identity (Prop. 4.3.3) — block condition (ii) -/

section NegTwo

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (N : OrdVModule W M)

/-- `𝒵_M(L[−1]x) = 0` for every `x` (`o(L₋₁x + L₀x) = 0`, Gannon 5.3.9b). -/
theorem torusOnePoint_Lsq_neg_one (x : 𝒱) : torusOnePoint N (Lsq W (-1) x) = 0 := by
  rw [Lsq_neg_one, show torusOnePoint N ((W.L (-1) + W.L 0) x) = gradedTraceOp N (oMod N ((W.L (-1) + W.L 0) x)) from rfl,
    LinearMap.add_apply, oMod_L_translation_all N x]
  have h := gradedTraceOp_sub N (0 : Module.End ℂ M) 0
  rw [sub_self, sub_self] at h
  exact h

/-- `qConv` is homogeneous in its second argument. -/
theorem qConv_smul_right (f : ℕ → ℂ) (c : ℂ) (g : FormalQSeries) :
    qConv f (c • g) = c • qConv f g := by
  funext e
  simp only [qConv, Pi.smul_apply, smul_eq_mul]
  rw [mul_finsum]
  exact finsum_congr (fun n => by ring)

/-- **Zhu's `[−2]`-identity (Prop. 4.3.3) — genus-one block condition (ii)**: for homogeneous
`a ∈ 𝒱_{kₐ}`, `kₐ ≥ 1`, and every `v`,

  `𝒵_M(a[−2]v) + Σ_{k≥1} (2k−1)·G_{2k} ⋆ 𝒵_M(a[2k−2]v) = 0`.

Proof: `0 = 𝒵_M(L[−1](a[−1]v)) = 𝒵_M(a[−1]L[−1]v) + 𝒵_M(a[−2]v)` by the `L[−1]`-derivation
`[L[−1], a[−1]] = a[−2]`; expand `𝒵_M(a[−1]L[−1]v)` by the closed recursion: the two-point term dies
(`o(L[−1]v) = 0`) and `a[2k−1]L[−1]v = L[−1](a[2k−1]v) + (2k−1)a[2k−2]v`. -/
theorem zhuRecursion_neg_two {ka : ℕ} (hk : 1 ≤ ka) {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ))
    (v : 𝒱) :
    torusOnePoint N (vSqZ W a ka (-2) v)
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1)) (torusOnePoint N (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)) = 0 := by
  set w : 𝒱 := Lsq W (-1) v with hw
  have hrec := zhuRecursionPinned_holds N hk ha w
  rw [ZhuRecursionPinned, ZhuRecursionAt] at hrec
  -- left side: `a[−1]w = L[−1](a[−1]v) − a[−2]v`
  have hL : vSqZ W a ka (-1) w = Lsq W (-1) (vSqZ W a ka (-1) v) - vSqZ W a ka (-2) v := by
    have h := Lsq_neg_one_vSqZ_comm hk ha (-1) v
    rw [show (-1 : ℤ) - 1 = -2 from by norm_num, show (-((-1 : ℤ) : ℂ)) = 1 from by push_cast; ring,
      one_smul] at h
    rw [hw, ← h]
    abel
  -- two-point term vanishes: `o(w) = 0`
  have htwo : torusTwoPoint N a w = 0 := by
    rw [torusTwoPoint_eq_gradedTraceOp, hw, Lsq_neg_one, LinearMap.add_apply,
      oMod_L_translation_all N v, mul_zero]
    have h := gradedTraceOp_sub N (0 : Module.End ℂ M) 0
    rw [sub_self, sub_self] at h
    exact h
  -- `𝒵(a[−1]w) = −𝒵(a[−2]v)`
  have hLZ : torusOnePoint N (vSqZ W a ka (-1) w) = -torusOnePoint N (vSqZ W a ka (-2) v) := by
    funext e
    have h1 : torusOnePoint N (vSqZ W a ka (-1) w) e = onePointAt N e (vSqZ W a ka (-1) w) := rfl
    rw [h1, hL, map_sub, onePointAt_apply, onePointAt_apply,
      show onePoint N (Lsq W (-1) (vSqZ W a ka (-1) v)) = torusOnePoint N (Lsq W (-1) (vSqZ W a ka (-1) v)) from rfl,
      torusOnePoint_Lsq_neg_one, Pi.zero_apply, zero_sub, Pi.neg_apply]
    rfl
  -- tail terms: `a[2k−1]w = L[−1](a[2k−1]v) + (2k−1)·a[2k−2]v`
  have htail : ∀ m : ℕ, torusOnePoint N (vSqZ W a ka (2 * (m + 1) - 1 : ℤ) w)
      = ((2 * (m + 1) - 1 : ℕ) : ℂ) • torusOnePoint N (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) := by
    intro m
    have h := Lsq_neg_one_vSqZ_comm hk ha (2 * (m + 1) - 1 : ℤ) v
    rw [show (2 * (m + 1) - 1 - 1 : ℤ) = 2 * (m + 1) - 2 from by ring, ← hw,
      sub_eq_iff_eq_add] at h
    have hc : (((2 * (m + 1) - 1 : ℕ) : ℂ)) = ((2 * (m + 1) - 1 : ℤ) : ℂ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (m + 1))]; ring
    have hidx : vSqZ W a ka (2 * (m + 1) - 1 : ℤ) w
        = Lsq W (-1) (vSqZ W a ka (2 * (m + 1) - 1 : ℤ) v)
          + ((2 * (m + 1) - 1 : ℕ) : ℂ) • vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v := by
      rw [hc, h, neg_smul]
      abel
    rw [hidx, torusOnePoint_add, torusOnePoint_smul, torusOnePoint_Lsq_neg_one, zero_add]
  rw [hLZ, htwo, zero_add] at hrec
  simp_rw [htail, qConv_smul_right] at hrec
  rw [neg_eq_iff_eq_neg] at hrec
  rw [hrec, neg_add_cancel]

/-- The `a[0]`-vanishing for **every** `v` (from `zhuVanishing_holds` by linearity). -/
theorem torusOnePoint_vSqZ_zero_eq_zero {ka : ℕ} (hk : 1 ≤ ka) {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ))
    (v : 𝒱) : torusOnePoint N (vSqZ W a ka 0 v) = 0 := by
  have hv : v ∈ ⨆ l : ℤ, W.grading l := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (motive := fun v => torusOnePoint N (vSqZ W a ka 0 v) = 0)
    W.grading hv (fun l u hu => ?_) ?_ (fun u w hu hw => ?_)
  · have h := zhuVanishing_holds N hk ha hu
    rwa [ZhuVanishingAt] at h
  · show torusOnePoint N (vSqZ W a ka 0 0) = 0
    rw [map_zero, torusOnePoint_zero]
  · show torusOnePoint N (vSqZ W a ka 0 (u + w)) = 0
    rw [map_add, torusOnePoint_add, hu, hw, add_zero]

end NegTwo

/-! ## Zhu's genus-one conformal-block conditions, and the trace functions satisfy them -/

section FormalBlock

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Zhu's genus-one conformal-block conditions** (Zhu §5.1, Def. 5.1.1, in formal `q`-series
form) for a linear family `S : 𝒱 → ℂ⟦q⟧`:
* (i) `S(a[0]v) = 0`;
* (ii) `S(a[−2]v) + Σ_{k≥1}(2k−1)G_{2k} ⋆ S(a[2k−2]v) = 0`;
* (iii) `S(L[−2]v) = q·d/dq S(v) + Σ_{k≥1} G_{2k} ⋆ S(L[2k−2]v)`,
for homogeneous `a ∈ 𝒱_{kₐ}`, `kₐ ≥ 1`, and all `v` — with the pinned family `zhuG`. -/
structure IsFormalBlock (W : VertexOperatorAlgebra 𝒱) (S : 𝒱 →ₗ[ℂ] FormalQSeries) : Prop where
  vanish : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱, S (vSqZ W a ka 0 v) = 0
  negTwo : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱,
    S (vSqZ W a ka (-2) v)
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1)) (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)) = 0
  omega : ∀ v : 𝒱, S (Lsq W (-2) v)
    = qDeriv (S v) + ∑ᶠ m : ℕ, qConv (zhuG (m + 1)) (S (Lsq W (2 * (m + 1) - 2 : ℤ) v))

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The one-point functions of a module, as a linear map `𝒱 → ℂ⟦q⟧`. -/
noncomputable def torusOnePointHom (N : OrdVModule W M) : 𝒱 →ₗ[ℂ] FormalQSeries where
  toFun := torusOnePoint N
  map_add' := torusOnePoint_add N
  map_smul' := fun c v => torusOnePoint_smul N c v

@[simp] theorem torusOnePointHom_apply (N : OrdVModule W M) (v : 𝒱) :
    torusOnePointHom N v = torusOnePoint N v := rfl

/-- **The trace functions of every module are genus-one conformal blocks** — all three of
Zhu's conditions hold for `v ↦ 𝒵_M(v;q)`: (i) `zhuVanishing_holds`, (ii) `zhuRecursion_neg_two`,
(iii) `zhuRecursion_omega`.  This is the formal half of Zhu's Theorem 5.3.1 (the analytic half is
convergence, `ConvergenceBridge`/`GrowthBound`). -/
theorem torusOnePointHom_isFormalBlock (N : OrdVModule W M) : IsFormalBlock W (torusOnePointHom N) where
  vanish := fun _ hk _ ha v => torusOnePoint_vSqZ_zero_eq_zero N hk ha v
  negTwo := fun _ hk _ ha v => zhuRecursion_neg_two N hk ha v
  omega := fun v => zhuRecursion_omega N v

end FormalBlock

end VOA
