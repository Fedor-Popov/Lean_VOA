/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ExpLogBinomial
import VOA.Modules.ZhuModule

/-!
# DLM Lemma 9.2(c) — the `q → 0` degeneration of Zhu's `[−2]`-family

At the cusp the second genus-one block family degenerates to Zhu's `∘`-product:

  `a[−2]v + Σ_{n ≥ 2} (2n−1)·G_{2n}(∞)·a[2n−2]v  =  a ∘ v + (1/12)·a[0]v`,

where `G_{2n}(∞) = zhuG n 0 = −B_{2n}/(2n)!` is the constant term of Zhu's Eisenstein family and
`a ∘ v = Pres W k a v 0`.  (The `1/12` is the `G₂`-anomaly: the repo's `negTwo` normal form runs
`n ≥ 2`, Zhu's kernel runs `n ≥ 1`, and the missing `n = 1` term is `(2·1−1)·zhuG 1 0 = −1/12`.)

## The proof, in one line

Everything is the Bernoulli identity `B(z)²·e^z = B(z) − z·B′(z)` — equivalently
`e^z/(e^z−1)² = z^{−2} + Σ_{n≥1}(2n−1)g_n z^{2n−2}` — pushed through `z = log(1+w)`, where
`B(log(1+w)) = u` (`uSeries_eq_bernoulli_subst_log`) and `e^{log(1+w)} = 1+w`
(`exp_subst_log`).  Coefficients come out by `coeff_mul_subst_log`.

Engine-confirmed first: `certificates/mathematica/cusp_degeneration_verify.wl` (`k = 1..6`, order `w^10`).

## Main results

* `bernoulliSq_mul_exp` — `B²·e^z = B − z·B′`;
* `coeff_bernoulliSq_mul_exp` — `[z^n](B²e^z) = (1−n)·B_n/n!`;
* `bernoulliSq_mul_exp_subst_log` — `(B²e^z)(log(1+w)) = u²·(1+w)`;
* `sqBracketCoeffZ_neg_two_cusp` — the coefficient identity (I3).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators
open PowerSeries

/-! ## The Bernoulli square identity -/

/-- **`B(z)²·e^z = B(z) − z·B′(z)`.**  Differentiate `B·(e^z−1) = z`, multiply by `B`, and use
`B·(e^z−1) = z` again. -/
theorem bernoulliSq_mul_exp :
    (bernoulliPowerSeries ℂ) ^ 2 * exp ℂ
      = bernoulliPowerSeries ℂ - X * derivative ℂ (bernoulliPowerSeries ℂ) := by
  have hBE : bernoulliPowerSeries ℂ * (exp ℂ - 1) = X := bernoulliPowerSeries_mul_exp_sub_one ℂ
  have hd := congrArg (derivative ℂ) hBE
  rw [Derivation.leibniz, map_sub, derivative_exp, Derivation.map_one_eq_zero, sub_zero,
    derivative_X, smul_eq_mul, smul_eq_mul] at hd
  -- hd : B * exp + (exp - 1) * B' = 1
  have hmul := congrArg (fun f => bernoulliPowerSeries ℂ * f) hd
  simp only [mul_add, mul_one] at hmul
  -- B*(B*exp) + B*((exp-1)*B') = B
  have hrw : bernoulliPowerSeries ℂ * ((exp ℂ - 1) * derivative ℂ (bernoulliPowerSeries ℂ))
      = X * derivative ℂ (bernoulliPowerSeries ℂ) := by
    rw [← mul_assoc, hBE]
  rw [hrw] at hmul
  have hsq : bernoulliPowerSeries ℂ * (bernoulliPowerSeries ℂ * exp ℂ)
      = (bernoulliPowerSeries ℂ) ^ 2 * exp ℂ := by ring
  rw [hsq] at hmul
  linear_combination hmul

/-- `[z^n](B²·e^z) = (1−n)·B_n/n!`. -/
theorem coeff_bernoulliSq_mul_exp (n : ℕ) :
    coeff n ((bernoulliPowerSeries ℂ) ^ 2 * exp ℂ)
      = (1 - (n : ℂ)) * (((bernoulli n : ℚ) : ℂ) / (n.factorial : ℂ)) := by
  rw [bernoulliSq_mul_exp, map_sub, coeff_X_mul_derivative, coeff_bernoulliPowerSeries]
  ring

/-- **The substituted form**: `(B²·e^z)|_{z = log(1+w)} = u²·(1+w)`. -/
theorem bernoulliSq_mul_exp_subst_log :
    ((bernoulliPowerSeries ℂ) ^ 2 * exp ℂ).subst (log ℂ) = uSeries ^ 2 * (1 + X) := by
  rw [← substLogHom_apply, map_mul, map_pow, substLogHom_apply, substLogHom_apply,
    ← uSeries_eq_bernoulli_subst_log, exp_subst_log]

/-! ## The `[−2]`-series and its coefficients -/

/-- `(1+w)^{k−1}·u^{−2}` — the series whose `log`-expansion carries the whole `[−2]`-family. -/
noncomputable def negTwoSeries (k : ℕ) : PowerSeries ℂ :=
  (1 + X : PowerSeries ℂ) ^ (k - 1) * (↑(uUnit ^ (-2 : ℤ)) : PowerSeries ℂ)

theorem uUnit_zpow_mul_uSeries_pow (n : ℕ) :
    (↑(uUnit ^ (-2 : ℤ)) : PowerSeries ℂ) * uSeries ^ n
      = (↑(uUnit ^ ((n : ℤ) - 2)) : PowerSeries ℂ) := by
  rw [← uUnit_zpow_natCast n, ← Units.val_mul, ← zpow_add uUnit,
    show (-2 : ℤ) + (n : ℤ) = (n : ℤ) - 2 from by ring]

/-- `[w^r]((1+w)^{k−1}u^{−2}·log(1+w)^n) = c(k, n−2, r−2)`. -/
theorem coeff_negTwoSeries_log_pow {k : ℕ} (hk : 1 ≤ k) (n r : ℕ) :
    coeff r (negTwoSeries k * (log ℂ) ^ n)
      = sqBracketCoeffZ k ((n : ℤ) - 2) ((r : ℤ) - 2) := by
  have hlog : ((log ℂ) : PowerSeries ℂ) ^ n = X ^ n * uSeries ^ n := by
    rw [← logOnePlusXSeries_eq_log, logOnePlusX_eq_X_mul_u, mul_pow]
  have hrw : negTwoSeries k * (log ℂ) ^ n
      = X ^ n * ((1 + X : PowerSeries ℂ) ^ (k - 1)
          * (↑(uUnit ^ ((n : ℤ) - 2)) : PowerSeries ℂ)) := by
    rw [hlog, negTwoSeries, ← uUnit_zpow_mul_uSeries_pow n]
    ring
  rw [hrw, PowerSeries.coeff_X_pow_mul', sqBracketCoeffZ, onePlusXUnit_zpow_of_one_le hk]
  by_cases h : n ≤ r
  · rw [if_pos h, if_pos (by omega),
      show ((r : ℤ) - 2 - ((n : ℤ) - 2)).toNat = r - n from by omega]
  · rw [if_neg h, if_neg (by omega)]

/-- The substituted master series: `[w^r]((1+w)^{k−1}u^{−2}·u²(1+w)) = C(k,r)`. -/
theorem coeff_negTwoSeries_mul_master {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    coeff r (negTwoSeries k * (uSeries ^ 2 * (1 + X))) = cbz (k : ℤ) (r : ℤ) := by
  have hu : (↑(uUnit ^ (-2 : ℤ)) : PowerSeries ℂ) * uSeries ^ 2 = 1 := by
    rw [uUnit_zpow_mul_uSeries_pow 2]
    norm_num
  have hrw : negTwoSeries k * (uSeries ^ 2 * (1 + X)) = (1 + X : PowerSeries ℂ) ^ k := by
    rw [negTwoSeries, show (1 + X : PowerSeries ℂ) ^ (k - 1)
        * ↑(uUnit ^ (-2 : ℤ)) * (uSeries ^ 2 * (1 + X))
      = (1 + X : PowerSeries ℂ) ^ (k - 1)
        * ((↑(uUnit ^ (-2 : ℤ)) : PowerSeries ℂ) * uSeries ^ 2) * (1 + X) from by ring, hu,
      mul_one, ← pow_succ]
    congr 1
    omega
  rw [hrw, onePlusX_pow_eq_binomSeries, coeff_binomSeries]

/-! ## Reindexing the even tail -/

/-- `Σ_{n < 2N+4} [4 ≤ n ∧ Even n]·g(n) = Σ_{m < N} g(2m+4)`. -/
theorem sum_range_two_mul_add_four (g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N + 4), (if 4 ≤ n ∧ Even n then g n else 0)
      = ∑ m ∈ Finset.range N, g (2 * m + 4) := by
  induction N with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, Nat.mul_zero, Nat.zero_add]
      refine Finset.sum_eq_zero (fun n hn => ?_)
      rw [Finset.mem_range] at hn
      exact if_neg (fun h => absurd h.1 (by omega))
  | succ N ih =>
      have h4 : (if 4 ≤ 2 * N + 4 ∧ Even (2 * N + 4) then g (2 * N + 4) else 0)
          = g (2 * N + 4) := if_pos ⟨by omega, by rw [Nat.even_iff]; omega⟩
      have h5 : (if 4 ≤ 2 * N + 4 + 1 ∧ Even (2 * N + 4 + 1) then g (2 * N + 4 + 1) else 0)
          = 0 := if_neg (by rintro ⟨-, hev⟩; rw [Nat.even_iff] at hev; omega)
      rw [show 2 * (N + 1) + 4 = (2 * N + 4) + 1 + 1 from by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, h5, ih, Finset.sum_range_succ, h4, add_zero]

/-- Even reindexing to a `finsum`. -/
theorem sum_range_even_four_eq_finsum (f : ℕ → ℂ) (r : ℕ) (hf : ∀ n, r < n → f n = 0) :
    ∑ n ∈ Finset.range (r + 1), (if 4 ≤ n ∧ Even n then f n else 0)
      = ∑ᶠ m : ℕ, f (2 * m + 4) := by
  have h1 : ∑ n ∈ Finset.range (r + 1), (if 4 ≤ n ∧ Even n then f n else 0)
      = ∑ n ∈ Finset.range (2 * (r + 1) + 4), (if 4 ≤ n ∧ Even n then f n else 0) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun n _ hn => ?_)
    rw [Finset.mem_range, not_lt] at hn
    rw [hf n (by omega), ite_self]
  rw [h1, sum_range_two_mul_add_four, finsum_eq_sum_of_support_subset (s := Finset.range (r + 1))]
  intro m hm
  simp only [Function.mem_support, ne_eq] at hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  exact hm (hf _ (by omega))

/-! ## The coefficient identity (I3) -/

theorem coeff_bernoulliSq_mul_exp_odd {n : ℕ} (hn : Odd n) :
    coeff n ((bernoulliPowerSeries ℂ) ^ 2 * exp ℂ) = 0 := by
  rw [coeff_bernoulliSq_mul_exp]
  rcases eq_or_ne n 1 with rfl | h1
  · norm_num
  · have h1' : 1 < n := by
      rcases hn with ⟨t, rfl⟩
      omega
    rw [bernoulli_eq_zero_of_odd hn h1']
    norm_num

theorem coeff_bernoulliSq_mul_exp_zero :
    coeff 0 ((bernoulliPowerSeries ℂ) ^ 2 * exp ℂ) = 1 := by
  rw [coeff_bernoulliSq_mul_exp, bernoulli_zero]
  norm_num

theorem coeff_bernoulliSq_mul_exp_two :
    coeff 2 ((bernoulliPowerSeries ℂ) ^ 2 * exp ℂ) = -(1 / 12) := by
  rw [coeff_bernoulliSq_mul_exp, bernoulli_two]
  norm_num

theorem coeff_bernoulliSq_mul_exp_even_four (m : ℕ) :
    coeff (2 * m + 4) ((bernoulliPowerSeries ℂ) ^ 2 * exp ℂ)
      = ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0 := by
  rw [coeff_bernoulliSq_mul_exp, zhuG_zero, show 2 * (m + 2) = 2 * m + 4 from by ring,
    show 2 * m + 4 - 1 = 2 * m + 3 from by omega]
  push_cast
  ring

/-- **(I3) — DLM Lemma 9.2(c) at the level of coefficients.**

`c(k,−2,m) + Σ_{n ≥ 2} (2n−1)·G_{2n}(∞)·c(k,2n−2,m) = C(k, m+2) + (1/12)·c(k,0,m)`.

Everything is the Bernoulli identity `B²e^z = B − zB′` pushed through `z = log(1+w)`. -/
theorem sqBracketCoeffZ_neg_two_cusp {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    sqBracketCoeffZ k (-2) ((r : ℤ) - 2)
        + ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
            * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) ((r : ℤ) - 2)
      = cbz (k : ℤ) (r : ℤ) + (1 / 12) * sqBracketCoeffZ k 0 ((r : ℤ) - 2) := by
  classical
  set F : ℕ → ℂ := fun n =>
    coeff n ((bernoulliPowerSeries ℂ) ^ 2 * exp ℂ)
      * sqBracketCoeffZ k ((n : ℤ) - 2) ((r : ℤ) - 2) with hF
  have hmaster : ∑ n ∈ Finset.range (r + 1), F n = cbz (k : ℤ) (r : ℤ) := by
    have h := coeff_negTwoSeries_mul_master hk r
    rw [← bernoulliSq_mul_exp_subst_log, coeff_mul_subst_log] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun n _ => by
      rw [hF, coeff_negTwoSeries_log_pow hk])
  have hFvanish : ∀ n : ℕ, r < n → F n = 0 := by
    intro n hn
    rw [hF]
    simp only
    rw [sqBracketCoeffZ_of_lt k (by omega : (r : ℤ) - 2 < (n : ℤ) - 2), mul_zero]
  have hext : ∑ n ∈ Finset.range (r + 1), F n = ∑ n ∈ Finset.range (r + 3), F n := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun n _ hn => ?_)
    rw [Finset.mem_range, not_lt] at hn
    exact hFvanish n (by omega)
  have hpoint : ∀ n ∈ Finset.range (r + 3), F n
      = (if n = 0 then F 0 else 0) + (if n = 2 then F 2 else 0)
        + (if 4 ≤ n ∧ Even n then F n else 0) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | h0
    · rw [if_pos rfl, if_neg (by omega), if_neg (fun h => absurd h.1 (by omega))]
      ring
    rcases eq_or_ne n 2 with rfl | h2
    · rw [if_neg (by omega), if_pos rfl, if_neg (fun h => absurd h.1 (by omega))]
      ring
    by_cases hev : Even n
    · have h4 : 4 ≤ n := by
        rw [Nat.even_iff] at hev
        omega
      rw [if_neg h0, if_neg h2, if_pos ⟨h4, hev⟩]
      ring
    · have hz : F n = 0 := by
        rw [hF]
        simp only
        rw [coeff_bernoulliSq_mul_exp_odd (Nat.not_even_iff_odd.mp hev), zero_mul]
      rw [if_neg h0, if_neg h2, if_neg (fun h => absurd h.2 hev), hz]
      ring
  rw [hext, Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (r + 3)) 0 (fun _ => F 0),
    Finset.sum_ite_eq' (Finset.range (r + 3)) 2 (fun _ => F 2),
    if_pos (Finset.mem_range.mpr (by omega)), if_pos (Finset.mem_range.mpr (by omega)),
    show r + 3 = (r + 2) + 1 from rfl,
    sum_range_even_four_eq_finsum F (r + 2) (fun n hn => hFvanish n (by omega))] at hmaster
  have hF0 : F 0 = sqBracketCoeffZ k (-2) ((r : ℤ) - 2) := by
    rw [hF]
    simp only [Nat.cast_zero, zero_sub, coeff_bernoulliSq_mul_exp_zero, one_mul]
  have hF2 : F 2 = -(1 / 12) * sqBracketCoeffZ k 0 ((r : ℤ) - 2) := by
    rw [hF]
    simp only [coeff_bernoulliSq_mul_exp_two]
    norm_num
  have hFm : ∀ m : ℕ, F (2 * m + 4)
      = ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
        * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) ((r : ℤ) - 2) := by
    intro m
    rw [hF]
    simp only
    rw [coeff_bernoulliSq_mul_exp_even_four m,
      show (((2 * m + 4 : ℕ) : ℤ) - 2) = 2 * ((m : ℤ) + 2) - 2 from by push_cast; ring]
  rw [hF0, hF2, funext hFm] at hmaster
  linear_combination hmaster

/-! ## The vector identity: the `q → 0` limit of Zhu's `[−2]`-family is `a ∘ v` -/

section Vector

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- Every square-bracket mode with `−2 ≤ M` is a finite sum over a common window. -/
theorem vSqZ_eq_sum_Ico {k : ℕ} {M : ℤ} (hM : -2 ≤ M) (a v : 𝒱) {P : ℕ}
    (hP : ∀ i : ℤ, (P : ℤ) ≤ i → W.smul a i v = 0) :
    vSqZ W a k M v
      = ∑ i ∈ Finset.Ico (-2 : ℤ) (P : ℤ), sqBracketCoeffZ k M i • W.smul a i v := by
  classical
  rw [vSqZ_apply]
  refine finsum_eq_finsetSum_of_support_subset _ (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi
  simp only [Finset.coe_Ico, Set.mem_Ico]
  constructor
  · by_contra hc
    push_neg at hc
    exact hi (by rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul])
  · by_contra hc
    push_neg at hc
    exact hi (by rw [show mode (W.Y a) i v = W.smul a i v from rfl, hP i hc, smul_zero])

/-- Zhu's `a ∘ v = Pres W k a v 0` on the same window. -/
theorem pres_zero_eq_sum_Ico {k : ℕ} (a v : 𝒱) {P : ℕ}
    (hP : ∀ i : ℤ, (P : ℤ) ≤ i → W.smul a i v = 0) (hkP : k ≤ P) :
    Pres W k a v 0
      = ∑ i ∈ Finset.Ico (-2 : ℤ) (P : ℤ), cbz (k : ℤ) (i + 2) • W.smul a i v := by
  classical
  have hmapset : Finset.Ico (-2 : ℤ) (P : ℤ)
      = (Finset.range (P + 2)).map ⟨fun j : ℕ => (j : ℤ) - 2, fun x y h => by simpa using h⟩ := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(i + 2).toNat, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hmapset, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ j ∈ Finset.range (P + 2),
      cbz (k : ℤ) (((j : ℤ) - 2) + 2) • W.smul a ((j : ℤ) - 2) v
        = cbz ((k : ℤ) + ((0 : ℕ) : ℤ)) (j : ℤ) • W.smul a ((j : ℤ) - 2 - ((0 : ℕ) : ℤ)) v := by
    intro j _
    rw [show (((j : ℤ) - 2) + 2) = (j : ℤ) from by ring,
      show ((k : ℤ) + ((0 : ℕ) : ℤ)) = (k : ℤ) from by push_cast; ring,
      show ((j : ℤ) - 2 - ((0 : ℕ) : ℤ)) = (j : ℤ) - 2 from by push_cast; ring]
  rw [Finset.sum_congr rfl hterm, Pres]
  have hsub : Finset.range (k + 0 + 1) ⊆ Finset.range (P + 2) :=
    Finset.range_mono (by omega)
  refine Finset.sum_subset hsub (fun j _ hj => ?_)
  rw [Finset.mem_range, not_lt] at hj
  rw [show ((k : ℤ) + ((0 : ℕ) : ℤ)) = (k : ℤ) from by push_cast; ring,
    cbz_lt (by omega) (by omega : (k : ℤ) < (j : ℤ)), zero_smul]

/-- **DLM Lemma 9.2(c)** — the `q → 0` limit of the (`G₂`-free) `[−2]`-family:

`a[−2]v + Σ_{m} (2(m+2)−1)·G_{2(m+2)}(∞)·a[2(m+2)−2]v = a ∘ v + (1/12)·a[0]v`. -/
theorem negTwoFamily_cusp {k : ℕ} (hk : 1 ≤ k) (a v : 𝒱) :
    vSqZ W a k (-2) v
        + ∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
            • vSqZ W a k (2 * ((m : ℤ) + 2) - 2) v
      = Pres W k a v 0 + (1 / 12 : ℂ) • vSqZ W a k 0 v := by
  classical
  obtain ⟨N, hN⟩ := W.toPreVertexAlgebra.smul_eventually_zero a v
  set P : ℕ := (max N (k : ℤ)).toNat with hPdef
  have hP : ∀ i : ℤ, (P : ℤ) ≤ i → W.smul a i v = 0 := by
    intro i hi
    exact hN i (by omega)
  have hkP : k ≤ P := by omega
  set S : Finset ℤ := Finset.Ico (-2 : ℤ) (P : ℤ) with hS
  -- every mode in sight, on the common window
  have hmode : ∀ M : ℤ, -2 ≤ M → vSqZ W a k M v
      = ∑ i ∈ S, sqBracketCoeffZ k M i • W.smul a i v :=
    fun M hM => vSqZ_eq_sum_Ico W hM a v hP
  -- the `m`-family dies past `P`
  have hzero : ∀ m : ℕ, P ≤ m → vSqZ W a k (2 * ((m : ℤ) + 2) - 2) v = 0 := by
    intro m hm
    rw [hmode _ (by omega)]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [sqBracketCoeffZ_of_lt k (by omega), zero_smul]
  have hfin : ∑ᶠ m : ℕ, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • vSqZ W a k (2 * ((m : ℤ) + 2) - 2) v
      = ∑ m ∈ Finset.range P, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • vSqZ W a k (2 * ((m : ℤ) + 2) - 2) v := by
    refine finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push_neg at hc
    exact hm (by rw [hzero m hc, smul_zero])
  -- collect everything on the window
  have hswap : ∑ m ∈ Finset.range P, (((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0)
        • vSqZ W a k (2 * ((m : ℤ) + 2) - 2) v
      = ∑ i ∈ S, (∑ m ∈ Finset.range P, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
          * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i) • W.smul a i v := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hmode _ (by omega), Finset.smul_sum]),
      Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl (fun m _ => by rw [smul_smul])
  have hmfin : ∀ i ∈ S, ∑ m ∈ Finset.range P, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
        * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i
      = ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ) * zhuG (m + 2) 0
        * sqBracketCoeffZ k (2 * ((m : ℤ) + 2) - 2) i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    refine (finsum_eq_finsetSum_of_support_subset _ (fun m hm => ?_)).symm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push_neg at hc
    exact hm (by rw [sqBracketCoeffZ_of_lt k (by omega), mul_zero])
  rw [hfin, hswap, Finset.sum_congr rfl (fun i hi => by rw [hmfin i hi]),
    hmode _ (by omega), hmode (0 : ℤ) (by omega),
    pres_zero_eq_sum_Ico W a v hP hkP, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Ico] at hi
  rw [smul_smul, ← add_smul, ← add_smul]
  congr 1
  have hkey := sqBracketCoeffZ_neg_two_cusp hk (i + 2).toNat
  rw [show (((i + 2).toNat : ℤ) - 2) = i from by omega,
    show (((i + 2).toNat : ℤ)) = i + 2 from by omega] at hkey
  linear_combination hkey

end Vector

end VOA
