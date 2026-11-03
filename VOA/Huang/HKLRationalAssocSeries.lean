/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocAssociator
import VOA.Huang.HKLLocRational
import VOA.Core.FieldCombinatorics

/-!
# From the formal associator relation to equality of convergent expansions

Pure analysis on `ℤ`-indexed coefficient sequences, the analytic core of the associativity of
the `A`-action of a `W`-module (`HKLRationalAssoc`).

For sequences `P, Q : ℤ → ℂ` (the product coefficients `f(a_{D-k} b_k x)` and the iterate
coefficients `f((a_r b)_{D-r} x)`), vanishing for large index, related by the **associator form of
the Jacobi identity**

  `Σ_{i ≤ K} C(K,i) Q(ℓ+i) = Σ_{i ≥ 0} C(i-ℓ-1, i) P(D-K-ℓ+i)`   (all `ℓ ∈ ℤ`),

and whose product series `Σ_k P_k (1+s)^{k-D-1}` and iterate series `Σ_r Q_r s^{-r-1}` converge for
`s ∈ (0,1)`, the two series are **equal** on `(0,1)` (`assoc_series_eq`).

Proof: `c_ℓ := Σ_i C(K,i) Q(ℓ+i)` has finite support, so `E(s) = Σ c_ℓ s^{-ℓ-1}` is a Laurent
polynomial; `(1+s)^K Σ Q_r s^{-r-1} = E(s)` on `(0,1)`; `(1+s)^K Σ P_k (1+s)^{k-D-1} = E(s)` for
`s ≥ 3` (binomial expansion of `(1+s)^e` in `1/s` and an absolutely convergent double sum); in the
variable `t = 1/(1+s)` both sides are holomorphic on the unit disc and agree on `(0, 1/4]`, so
they agree at every `t ∈ (1/2, 1)` (identity theorem).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HKLRational

open VOA Complex Filter Topology

/-- `|C(e,i)| ≤ C(i + |e|, |e|)`. -/
theorem norm_cbz_le (e : ℤ) (i : ℕ) :
    ‖cbz e i‖ ≤ ((i + e.natAbs).choose e.natAbs : ℝ) := by
  rcases le_or_gt 0 e with he | he
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le he
    rw [cbz_apply_nonneg _ (by positivity), show ((i : ℤ)).toNat = i from by simp,
      VOA.Huang.AssocAssociator.gBinom_natCast, Int.natAbs_natCast, Complex.norm_natCast]
    have h1 : a.choose i ≤ (i + a).choose i := Nat.choose_le_choose i (by omega)
    have h2 : (i + a).choose i = (i + a).choose a := Nat.choose_symm_add
    exact_mod_cast h1.trans h2.le
  · obtain ⟨s, hs⟩ : ∃ s : ℕ, e = -(s : ℤ) - 1 := ⟨e.natAbs - 1, by omega⟩
    have hna : e.natAbs = s + 1 := by omega
    rw [hna, cbz_apply_nonneg _ (by positivity), show ((i : ℤ)).toNat = i from by simp, hs,
      VOA.FieldCombinatorics.gBinom_negsucc]
    have hfac : ((s + i).factorial : ℂ) / ((s.factorial : ℂ) * (i.factorial : ℂ)) =
        ((s + i).choose i : ℂ) := by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left i s)
      rw [Nat.add_sub_cancel] at h
      have hs0 : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
      have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      rw [div_eq_iff (mul_ne_zero hs0 hi0)]
      exact_mod_cast (by rw [← h]; ring : (s + i).factorial = (s + i).choose i * (s.factorial * i.factorial))
    rw [mul_div_assoc, hfac, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    have h1 : (s + i).choose i ≤ (i + (s + 1)).choose i := Nat.choose_le_choose i (by omega)
    have h2 : (i + (s + 1)).choose i = (i + (s + 1)).choose (s + 1) := Nat.choose_symm_add
    exact_mod_cast h1.trans h2.le

/-- The binomial expansion of `(1+x)^e` in powers of `1/x`, for `‖x‖ > 1`. -/
theorem hasSum_one_add_zpow (e : ℤ) {x : ℂ} (hx : 1 < ‖x‖) :
    HasSum (fun i : ℕ => cbz e i * x ^ (e - i)) ((1 + x) ^ e) := by
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; linarith
  have hy : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hx
  have h := (VOA.Huang.AssocAssociator.hasSum_cbz_pow e hy).mul_right (x ^ e)
  convert h using 1
  · funext i
    rw [mul_assoc, zpow_sub₀ hx0, zpow_natCast, inv_pow, div_eq_mul_inv, mul_comm (x ^ e)]
  · rw [← mul_zpow]
    congr 1
    field_simp
    ring

/-- `b^n ≤ a^n` for `0 < a ≤ b` and `n ≤ 0`. -/
theorem zpow_le_zpow_of_nonpos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {n : ℤ} (hn : n ≤ 0) :
    b ^ n ≤ a ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos ha m) (pow_le_pow_left₀ ha.le hab m)

/-- **The product side for large `s`**: for `s ≥ 3` the product series, multiplied by
`(1+s)^K`, is the coefficient series `Σ_ℓ c_ℓ s^{-ℓ-1}` with
`c_ℓ = Σ_i C(i-ℓ-1, i) P(D-K-ℓ+i)` (binomial expansion and an absolutely convergent double sum). -/
theorem prod_tsum_eq_large (P : ℤ → ℂ) (D : ℤ) (K : ℕ) (k1 : ℤ) (hP : ∀ k, k1 ≤ k → P k = 0)
    (hProd : Summable fun k : ℤ => P k * (((3 / 2 : ℝ) : ℂ)) ^ (k - D - 1))
    {s : ℝ} (hs : 3 ≤ s) :
    ∑' k : ℤ, P k * (1 + (s : ℂ)) ^ (k + K - D - 1) =
      ∑' ℓ : ℤ, (∑' i : ℕ, cbz (i - ℓ - 1) i * P (D - K - ℓ + i)) * (s : ℂ) ^ (-ℓ - 1) := by
  set x : ℂ := (s : ℂ) with hxdef
  have hs0 : 0 < s := by linarith
  have hnx : ‖x‖ = s := by rw [hxdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  have hx : 1 < ‖x‖ := by rw [hnx]; linarith
  let e : ℤ → ℤ := fun k => k + K - D - 1
  let G : ℤ × ℕ → ℂ := fun p => P p.1 * (cbz (e p.1) p.2 * x ^ (e p.1 - p.2))
  have hrow : ∀ k : ℤ, HasSum (fun i : ℕ => G (k, i)) (P k * (1 + x) ^ (e k)) := fun k =>
    (hasSum_one_add_zpow (e k) hx).mul_left (P k)
  -- absolute summability of `G`
  let B : ℤ × ℕ → ℝ := fun p => ‖P p.1‖ * (((p.2 + (e p.1).natAbs).choose (e p.1).natAbs : ℝ) *
    s ^ (e p.1 - p.2))
  have hB0 : 0 ≤ B := fun p => by positivity
  have hGB : ∀ p, ‖G p‖ ≤ B p := by
    intro p
    simp only [G, B, norm_mul, norm_zpow, hnx]
    gcongr
    exact norm_cbz_le _ _
  have hsinv : ‖s⁻¹‖ < 1 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos hs0]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have hBrow : ∀ k : ℤ, HasSum (fun i : ℕ => B (k, i))
      (‖P k‖ * s ^ (e k) * (1 / (1 - s⁻¹) ^ ((e k).natAbs + 1))) := by
    intro k
    have h := (hasSum_choose_mul_geometric_of_norm_lt_one ((e k).natAbs) hsinv).mul_left
      (‖P k‖ * s ^ (e k))
    convert h using 1
    funext i
    simp only [B]
    rw [zpow_sub₀ hs0.ne', zpow_natCast, inv_pow]
    ring
  have hProdn : Summable fun k : ℤ => ‖P k * (((3 / 2 : ℝ) : ℂ)) ^ (k - D - 1)‖ :=
    summable_norm_iff.mpr hProd
  have hBs : Summable B := by
    refine (summable_prod_of_nonneg hB0).2 ⟨fun k => (hBrow k).summable, ?_⟩
    refine Summable.of_norm_bounded_eventually
      (hProdn.mul_left (s / (s - 1) * (s - 1) ^ (K : ℤ))) ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_Ioo (D + 1 - K) k1).subset fun k hk => ?_
    simp only [Set.mem_setOf_eq, not_le] at hk
    simp only [Set.mem_Ioo]
    by_contra hcon
    rw [not_and_or, not_lt, not_lt] at hcon
    apply hk.not_ge
    rw [(hBrow k).tsum_eq]
    rcases hcon with hk1 | hk1
    · -- `e k ≤ 0`
      obtain ⟨m, hm⟩ : ∃ m : ℕ, e k = -(m : ℤ) := ⟨(e k).natAbs, by simp only [e]; omega⟩
      have hmn : (e k).natAbs = m := by rw [hm]; simp
      have hs1 : 0 < s - 1 := by linarith
      have hs1' : s - 1 ≠ 0 := hs1.ne'
      have h1s : 0 < 1 - s⁻¹ := by
        have : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
        linarith
      have key : s ^ (e k) * (1 / (1 - s⁻¹) ^ ((e k).natAbs + 1)) =
          s / (s - 1) * (s - 1) ^ (e k) := by
        have h1 : 1 - s⁻¹ = (s - 1) / s := by field_simp
        rw [hmn, hm, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, h1, div_pow]
        field_simp
        ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc, key, norm_mul, norm_zpow]
      have hn32 : ‖(((3 / 2 : ℝ) : ℂ))‖ = 3 / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [hn32]
      have hez : e k = (k - D - 1) + K := by simp only [e]; ring
      have hk2 : k - D - 1 ≤ 0 := by omega
      have hle : (s - 1) ^ (k - D - 1) ≤ (3 / 2 : ℝ) ^ (k - D - 1) :=
        zpow_le_zpow_of_nonpos (by norm_num) (by linarith) hk2
      rw [hez, zpow_add₀ hs1']
      calc ‖P k‖ * (s / (s - 1) * ((s - 1) ^ (k - D - 1) * (s - 1) ^ (K : ℤ)))
          = s / (s - 1) * (s - 1) ^ (K : ℤ) * (‖P k‖ * (s - 1) ^ (k - D - 1)) := by ring
        _ ≤ s / (s - 1) * (s - 1) ^ (K : ℤ) * (‖P k‖ * (3 / 2 : ℝ) ^ (k - D - 1)) := by
          gcongr
    · have hs1 : 0 < s - 1 := by linarith
      simp only [hP k hk1, norm_zero, zero_mul]
      positivity
  have hGs : Summable G := Summable.of_norm_bounded hBs hGB
  -- the reindexing involution
  let σ : ℤ × ℕ ≃ ℤ × ℕ :=
    { toFun := fun p => (D - K - p.1 + p.2, p.2)
      invFun := fun p => (D - K - p.1 + p.2, p.2)
      left_inv := fun p => by ext <;> (simp only; try ring)
      right_inv := fun p => by ext <;> (simp only; try ring) }
  have hGσ : ∀ ℓ : ℤ, ∀ i : ℕ, G (σ (ℓ, i)) =
      (cbz (i - ℓ - 1) i * P (D - K - ℓ + i)) * x ^ (-ℓ - 1) := by
    intro ℓ i
    simp only [G, σ, Equiv.coe_fn_mk, e]
    rw [show D - K - ℓ + i + K - D - 1 = (i : ℤ) - ℓ - 1 by ring,
      show (i : ℤ) - ℓ - 1 - i = -ℓ - 1 by ring]
    ring
  have hGσs : Summable (G ∘ σ) := hGs.comp_injective σ.injective
  calc ∑' k : ℤ, P k * (1 + x) ^ (k + K - D - 1)
      = ∑' k : ℤ, ∑' i : ℕ, G (k, i) := tsum_congr fun k => (hrow k).tsum_eq.symm
    _ = ∑' p, G p := hGs.tsum_prod.symm
    _ = ∑' p, G (σ p) := (σ.tsum_eq G).symm
    _ = ∑' ℓ : ℤ, ∑' i : ℕ, G (σ (ℓ, i)) := hGσs.tsum_prod
    _ = ∑' ℓ : ℤ, (∑' i : ℕ, cbz (i - ℓ - 1) i * P (D - K - ℓ + i)) * x ^ (-ℓ - 1) := by
      refine tsum_congr fun ℓ => ?_
      simp_rw [hGσ]
      exact tsum_mul_right

/-- Points of a real segment accumulate at `1/8` in `ℂ`. -/
theorem frequently_real_near {p : ℂ → Prop}
    (h : ∀ x : ℝ, 0 < x → x ≤ 1 / 4 → p (x : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (((1 / 8 : ℝ)) : ℂ), p z := by
  let u : ℕ → ℝ := fun n => 1 / 8 + 1 / 8 * (1 / ((n : ℝ) + 1))
  have hu : Tendsto (fun n => ((u n : ℝ) : ℂ)) atTop (𝓝[≠] (((1 / 8 : ℝ)) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto u atTop (𝓝 (1 / 8 + 1 / 8 * 0)) := (h0.const_mul _).const_add _
      rw [mul_zero, add_zero] at h1
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj, u]
      have : 0 < 1 / 8 * (1 / ((n : ℝ) + 1)) := by positivity
      linarith
  refine hu.frequently (Frequently.of_forall fun n => h (u n) (by positivity) ?_)
  simp only [u]
  have : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  nlinarith

/-- **Equality of the iterate and product expansions** (the analytic core of the
associativity of a module action). -/
theorem assoc_series_eq (P Q : ℤ → ℂ) (D : ℤ) (K : ℕ) (k1 r0 : ℤ)
    (hP : ∀ k, k1 ≤ k → P k = 0) (hQ : ∀ r, r0 ≤ r → Q r = 0)
    (hrel : ∀ ℓ : ℤ, ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) * Q (ℓ + i) =
      ∑' i : ℕ, cbz (i - ℓ - 1) i * P (D - K - ℓ + i))
    (hProd : ∀ s : ℝ, 0 < s → s < 1 →
      Summable fun k : ℤ => P k * (1 + (s : ℂ)) ^ (k - D - 1))
    (hIt : ∀ s : ℝ, 0 < s → s < 1 → Summable fun r : ℤ => Q r * (s : ℂ) ^ (-r - 1))
    {s₀ : ℝ} (hs0 : 0 < s₀) (hs1 : s₀ < 1) :
    ∑' r : ℤ, Q r * (s₀ : ℂ) ^ (-r - 1) = ∑' k : ℤ, P k * (1 + (s₀ : ℂ)) ^ (k - D - 1) := by
  classical
  let c : ℤ → ℂ := fun ℓ => ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) * Q (ℓ + i)
  let S : Finset ℤ := Finset.Ioo (D - K - k1) r0
  have hcS : ∀ ℓ, ℓ ∉ S → c ℓ = 0 := by
    intro ℓ hℓ
    simp only [S, Finset.mem_Ioo, not_and_or, not_lt] at hℓ
    rcases hℓ with h | h
    · simp only [c]
      rw [hrel ℓ]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      rw [hP _ (by omega), mul_zero]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [hQ _ (by omega), mul_zero]
  let E : ℂ → ℂ := fun z => ∑ ℓ ∈ S, c ℓ * z ^ (-ℓ - 1)
  have hE : ∀ z : ℂ, ∑' ℓ : ℤ, c ℓ * z ^ (-ℓ - 1) = E z := fun z =>
    tsum_eq_sum fun ℓ hℓ => by rw [hcS ℓ hℓ, zero_mul]
  -- Step 2: the iterate side on `(0, 1)`
  have hstep2 : ∀ s : ℝ, 0 < s → s < 1 →
      (1 + (s : ℂ)) ^ K * ∑' r : ℤ, Q r * (s : ℂ) ^ (-r - 1) = E s := by
    intro s hs0 hs1
    set x : ℂ := (s : ℂ)
    have hx0 : x ≠ 0 := by simp [x, hs0.ne']
    have hsum := hIt s hs0 hs1
    have hshift : ∀ i : ℕ, Summable fun ℓ : ℤ => (K.choose i : ℂ) * Q (ℓ + i) * x ^ (-ℓ - 1) := by
      intro i
      have h := (hsum.comp_injective (Equiv.addRight (i : ℤ)).injective).mul_left
        ((K.choose i : ℂ) * x ^ (i : ℤ))
      refine h.congr fun ℓ => ?_
      simp only [Function.comp, Equiv.coe_addRight]
      rw [show -(ℓ + (i : ℤ)) - 1 = -ℓ - 1 - i by ring, zpow_sub₀ hx0, zpow_natCast]
      field_simp
    have hpow : (1 + x) ^ K = ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) * x ^ (i : ℤ) := by
      rw [add_comm, add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, mul_one, zpow_natCast, mul_comm]
    rw [hpow, Finset.sum_mul, ← hE]
    have hterm : ∀ i ∈ Finset.range (K + 1),
        (K.choose i : ℂ) * x ^ (i : ℤ) * ∑' r : ℤ, Q r * x ^ (-r - 1) =
          ∑' ℓ : ℤ, (K.choose i : ℂ) * Q (ℓ + i) * x ^ (-ℓ - 1) := by
      intro i _
      rw [← tsum_mul_left, ← (Equiv.addRight (i : ℤ)).tsum_eq]
      refine tsum_congr fun ℓ => ?_
      simp only [Equiv.coe_addRight]
      rw [show -(ℓ + (i : ℤ)) - 1 = -ℓ - 1 - i by ring, zpow_sub₀ hx0, zpow_natCast]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum fun i _ => hshift i]
    refine tsum_congr fun ℓ => ?_
    simp only [c, Finset.sum_mul]
  -- Step 3: the product side for `s ≥ 3`
  have hP32 : Summable fun k : ℤ => P k * (((3 / 2 : ℝ)) : ℂ) ^ (k - D - 1) := by
    have h := hProd (1 / 2) (by norm_num) (by norm_num)
    convert h using 3
    push_cast
    norm_num
  have hstep3 : ∀ s : ℝ, 3 ≤ s →
      (1 + (s : ℂ)) ^ K * ∑' k : ℤ, P k * (1 + (s : ℂ)) ^ (k - D - 1) = E s := by
    intro s hs
    have hs1 : (1 + (s : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_ne_zero]; linarith
    rw [← tsum_mul_left]
    have e1 : ∀ k : ℤ, (1 + (s : ℂ)) ^ K * (P k * (1 + (s : ℂ)) ^ (k - D - 1)) =
        P k * (1 + (s : ℂ)) ^ (k + K - D - 1) := by
      intro k
      rw [show k + (K : ℤ) - D - 1 = (k - D - 1) + K by ring, zpow_add₀ hs1, zpow_natCast]
      ring
    rw [tsum_congr e1, prod_tsum_eq_large P D K k1 hP hP32 hs, ← hE]
    refine tsum_congr fun ℓ => ?_
    rw [← hrel ℓ]
  -- Step 4: the variable `t = 1/(1+s)`
  let M : ℕ := (k1 - D).toNat
  have hM : k1 ≤ D + 2 + M := by simp only [M]; omega
  let a : ℕ → ℂ := fun n => P (D + 1 + M - n)
  let φ : ℂ → ℂ := fun t => ∑' n : ℕ, a n * t ^ n
  let ψ : ℂ → ℂ := fun t => ∑ ℓ ∈ S, c ℓ * (t ^ ((M : ℤ) + K + ℓ + 1) * (1 - t) ^ (-ℓ - 1))
  have hexpS : ∀ ℓ ∈ S, 0 ≤ (M : ℤ) + K + ℓ + 1 := by
    intro ℓ hℓ
    simp only [S, Finset.mem_Ioo] at hℓ
    omega
  -- `φ` and `ψ` against the series, at real `t ∈ (0,1)`, `s = 1/t - 1`
  have hφ_eq : ∀ t : ℝ, 0 < t → t < 1 →
      φ t = (t : ℂ) ^ M * ∑' k : ℤ, P k * (1 + ((1 / t - 1 : ℝ) : ℂ)) ^ (k - D - 1) := by
    intro t ht0 ht1
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have h1s : (1 + ((1 / t - 1 : ℝ) : ℂ)) = (t : ℂ)⁻¹ := by push_cast; ring
    let g : ℕ → ℤ := fun n => D + 1 + M - n
    have hg : Function.Injective g := fun n m h => by simp only [g] at h; omega
    let f : ℤ → ℂ := fun k => P k * (1 + ((1 / t - 1 : ℝ) : ℂ)) ^ (k - D - 1)
    have hsupp : Function.support f ⊆ Set.range g := by
      intro k hk
      have hPk : P k ≠ 0 := fun h0 => hk (by simp only [f, h0, zero_mul])
      have hk1 : k < k1 := by
        by_contra h; exact hPk (hP k (not_lt.mp h))
      exact ⟨(D + 1 + M - k).toNat, by simp only [g]; omega⟩
    rw [← hg.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [a, f, g, h1s]
    rw [show D + 1 + (M : ℤ) - n - D - 1 = (M : ℤ) - n by ring, inv_zpow', neg_sub,
      zpow_sub₀ ht, zpow_natCast, zpow_natCast]
    field_simp
  have hψ_eq : ∀ t : ℝ, 0 < t → t < 1 →
      ψ t = (t : ℂ) ^ ((M : ℤ) + K) * E ((1 / t - 1 : ℝ) : ℂ) := by
    intro t ht0 ht1
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have h1t : (1 - (t : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]; linarith
    have hs : ((1 / t - 1 : ℝ) : ℂ) = (1 - (t : ℂ)) / t := by push_cast; field_simp
    simp only [ψ, E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [hs, div_zpow, show (M : ℤ) + K + ℓ + 1 = ((M : ℤ) + K) - (-ℓ - 1) by ring,
      zpow_sub₀ ht]
    field_simp
  -- agreement for `t ∈ (0, 1/4]`
  have hagree : ∀ t : ℝ, 0 < t → t ≤ 1 / 4 → φ t = ψ t := by
    intro t ht0 ht1
    have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hs3 : 3 ≤ 1 / t - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ ht0]; linarith
    rw [hφ_eq t ht0 (by linarith), hψ_eq t ht0 (by linarith), ← hstep3 _ hs3]
    have h1s : (1 + ((1 / t - 1 : ℝ) : ℂ)) = (t : ℂ)⁻¹ := by push_cast; ring
    rw [h1s, inv_pow, zpow_add₀ ht, zpow_natCast, zpow_natCast]
    field_simp
  -- analyticity on the unit disc
  have ha : ∀ q : ℂ, ‖q‖ < 1 → Summable fun n => a n * q ^ n := by
    intro q hq
    obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hq (by norm_num : (1 / 2 : ℝ) < 1))
    have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht1
    have hts : Summable fun n => a n * (t : ℂ) ^ n := by
      have hsum := hProd (1 / t - 1) (by
          rw [sub_pos, lt_div_iff₀ ht0]; linarith)
        (by
          have : (1 / 2 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht1
          rw [sub_lt_iff_lt_add, div_lt_iff₀ ht0]; nlinarith)
      have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have h1s : (1 + ((1 / t - 1 : ℝ) : ℂ)) = (t : ℂ)⁻¹ := by push_cast; ring
      have hc := (hsum.comp_injective (fun n m h => by simp only at h; omega :
        Function.Injective fun n : ℕ => D + 1 + (M : ℤ) - n)).mul_left ((t : ℂ) ^ M)
      refine hc.congr fun n => ?_
      simp only [Function.comp, a, h1s]
      rw [show D + 1 + (M : ℤ) - n - D - 1 = (M : ℤ) - n by ring, inv_zpow', neg_sub,
        zpow_sub₀ ht, zpow_natCast, zpow_natCast]
      field_simp
    refine Summable.of_norm_bounded (summable_norm_iff.mpr hts) fun n => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    gcongr
    exact (le_max_left _ _).trans ht1.le
  have hφd : DifferentiableOn ℂ φ (Metric.ball 0 1) := fun z hz =>
    (VOA.Huang.HKLLoc.differentiableAt_powerSeries a ha
      (by simpa using hz)).differentiableWithinAt
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 1) := by
    intro z hz
    have hz1 : 1 - z ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination -h
      rw [this, Metric.mem_ball, dist_zero_right, norm_one] at hz
      exact lt_irrefl _ hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun ℓ hℓ => ?_
    refine DifferentiableAt.const_mul (DifferentiableAt.mul ?_ ?_) _
    · exact (differentiableAt_zpow).mpr (Or.inr (hexpS ℓ hℓ))
    · exact ((differentiableAt_zpow).mpr (Or.inl hz1)).comp z
        ((differentiableAt_const _).sub differentiableAt_id)
  have hEq : Set.EqOn φ ψ (Metric.ball 0 1) := by
    refine (hφd.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
      (hψd.analyticOnNhd Metric.isOpen_ball) (convex_ball 0 1).isPreconnected
      (z₀ := (((1 / 8 : ℝ)) : ℂ)) ?_ ?_
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    · exact frequently_real_near fun x hx0 hx1 => hagree x hx0 hx1
  -- Step 5: conclusion at `t₀ = 1/(1+s₀)`
  set t₀ : ℝ := 1 / (1 + s₀) with ht₀
  have ht0 : 0 < t₀ := by positivity
  have ht1 : t₀ < 1 := by rw [ht₀, div_lt_one (by linarith)]; linarith
  have hst : 1 / t₀ - 1 = s₀ := by rw [ht₀]; field_simp; ring
  have hmem : ((t₀ : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  have key := hEq hmem
  rw [hφ_eq t₀ ht0 ht1, hψ_eq t₀ ht0 ht1, hst, ← hstep2 s₀ hs0 hs1] at key
  have ht : ((t₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have h1s : (1 + (s₀ : ℂ)) = ((t₀ : ℝ) : ℂ)⁻¹ := by
    rw [← hst]; push_cast; ring
  have htM : ((t₀ : ℝ) : ℂ) ^ M ≠ 0 := pow_ne_zero _ ht
  have htK : ((t₀ : ℝ) : ℂ) ^ K ≠ 0 := pow_ne_zero _ ht
  have hK : ((t₀ : ℝ) : ℂ) ^ ((M : ℤ) + K) * (1 + (s₀ : ℂ)) ^ K = ((t₀ : ℝ) : ℂ) ^ M := by
    rw [h1s, zpow_add₀ ht, zpow_natCast, zpow_natCast, inv_pow, mul_assoc,
      mul_inv_cancel₀ htK, mul_one]
  rw [← mul_assoc, hK] at key
  exact (mul_left_cancel₀ htM key).symm

end VOA.Huang.HKLRational
