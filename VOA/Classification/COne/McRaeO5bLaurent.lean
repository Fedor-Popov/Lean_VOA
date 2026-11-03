/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5bResidue
import VOA.Huang.HKLLocRational
import VOA.Huang.AssocAssociator

/-! # O5b, analytic part: three Laurent expansions of one function satisfy the residue identity

Let `Ψ` be holomorphic on `ℂ ∖ {0, 1}` with Laurent expansions

* `Σ s_n ζ^n` on `|ζ| > 1`, `s_n = 0` for `n ≫ 0`,
* `Σ t_n ζ^n` on `0 < |ζ| < 1`, `t_n = 0` for `n ≪ 0`,
* `Σ q_m (ζ-1)^m` on `0 < |ζ - 1| < 1`, `q_m = 0` for `m ≪ 0`.

Then for all `a, ℓ ∈ ℤ`: `resInf a ℓ s - resZero a ℓ t = resOne a ℓ q` (`residue_of_glue`).

Proof. With `N` the pole order at `1`, `(ζ-1)^N Ψ` is bounded near `1`, so the library's gluing
criterion (`HKLLoc.conv_eq_of_glue`, Liouville) gives `conv N s = conv N t =: c`, of finite
support `S`. Hence `Ψ = R := Σ_{k ∈ S} c_k ζ^k (ζ-1)^{-N}` near `∞`, and by the identity theorem
on the connected set `ℂ ∖ {0, 1}` everywhere. The three expansions of `R` are `Einf`, `Ezero`,
`Eone` (binomial series, `hasSum_einf` etc.), so by uniqueness of Laurent coefficients
(`laurent_zero_unique`, `laurent_inf_unique`) `s, t, q` are these expansions; then `residue_E`.

Mathlib and the library's `HKLLoc` analysis. No `sorry`, no new axioms.
-/

noncomputable section
namespace VOA.Classification.COne.McRaeO5b
open VOA Complex Filter Topology Set
open scoped BigOperators

/-! ## Uniqueness of Laurent coefficients -/

/-- A Laurent series with finitely many negative powers vanishing on the punctured unit disc is
zero. -/
theorem laurent_zero_unique {u : ℤ → ℂ} {n₁ : ℤ} (hu : ∀ n, n < n₁ → u n = 0)
    (h : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → HasSum (fun n : ℤ => u n * ζ ^ n) 0) : u = 0 := by
  set i : ℕ := (-n₁).toNat with hi
  have hd : (fun k : ℕ => u ((k : ℤ) - i)) = 0 := by
    apply VOA.Huang.HKLLoc.coeffs_eq_zero_of_hasSum_zero'
    intro ζ hζ0 hζ1
    have h1 := VOA.Huang.HKLLoc.hasSum_shift hζ0 (h ζ hζ0 hζ1) i
    have h2 := VOA.Huang.HKLLoc.hasSum_nat_of_int (α := fun k : ℤ => u (k - i)) 0
      (fun k _ => hu _ (by omega)) h1
    simpa using h2
  funext n
  rcases lt_or_ge n (-(i : ℤ)) with hn | hn
  · exact hu n (by omega)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = n + i := ⟨(n + i).toNat, by omega⟩
    have := congrFun hd k
    simp only [Pi.zero_apply] at this ⊢
    rwa [hk, add_sub_cancel_right] at this

/-- A Laurent series with finitely many positive powers vanishing on `|ζ| > 1` is zero. -/
theorem laurent_inf_unique {u : ℤ → ℂ} {n₀ : ℤ} (hu : ∀ n, n₀ < n → u n = 0)
    (h : ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℤ => u n * ζ ^ n) 0) : u = 0 := by
  have hv : (fun m : ℤ => u (-m)) = 0 := by
    refine laurent_zero_unique (n₁ := -n₀) (fun m hm => hu _ (by omega)) ?_
    intro w hw0 hw1
    have hζ : 1 < ‖w⁻¹‖ := by
      rw [norm_inv]; exact one_lt_inv₀ (norm_pos_iff.mpr hw0) |>.mpr hw1
    have h1 := h w⁻¹ hζ
    rw [← (Equiv.neg ℤ).hasSum_iff] at h1
    refine h1.congr_fun fun m => ?_
    simp only [Function.comp_apply, Equiv.neg_apply, inv_zpow', neg_neg]
  funext n
  have := congrFun hv (-n)
  simpa using this

/-! ## The three binomial expansions -/

theorem hasSum_einf (A B : ℤ) {ζ : ℂ} (hζ : 1 < ‖ζ‖) :
    HasSum (fun n : ℤ => einf A B n * ζ ^ n) (ζ ^ A * (ζ - 1) ^ B) := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ; linarith
  have hy : ‖-ζ⁻¹‖ < 1 := by
    rw [norm_neg, norm_inv]; exact inv_lt_one_of_one_lt₀ hζ
  have h := (VOA.Huang.AssocAssociator.hasSum_cbz_pow B hy).mul_left (ζ ^ (A + B))
  have hval : ζ ^ (A + B) * (1 + -ζ⁻¹) ^ B = ζ ^ A * (ζ - 1) ^ B := by
    have e : 1 + -ζ⁻¹ = (ζ - 1) / ζ := by field_simp; ring
    rw [e, div_zpow, zpow_add₀ hζ0]
    field_simp
  rw [hval] at h
  let g : ℕ → ℤ := fun i => A + B - i
  have hg : Function.Injective g := fun i j hij => by simpa [g] using hij
  have hf : ∀ n ∉ Set.range g, einf A B n * ζ ^ n = 0 := by
    intro n hn
    have : A + B < n := by
      by_contra hc
      exact hn ⟨(A + B - n).toNat, by simp only [g]; omega⟩
    rw [einf_eq_zero this, zero_mul]
  refine (hg.hasSum_iff hf).mp (h.congr_fun fun i => ?_)
  simp only [Function.comp_apply, g, einf, show A + B - (A + B - (i : ℤ)) = i by ring,
    negOnePow_natCast]
  rw [zpow_sub₀ hζ0, zpow_natCast,
    show (-ζ⁻¹) ^ i = (-1) ^ i * (ζ ^ i)⁻¹ by rw [neg_eq_neg_one_mul, mul_pow, inv_pow]]
  field_simp

theorem hasSum_ezero (A B : ℤ) {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ1 : ‖ζ‖ < 1) :
    HasSum (fun n : ℤ => ezero A B n * ζ ^ n) (ζ ^ A * (ζ - 1) ^ B) := by
  have hy : ‖-ζ‖ < 1 := by rwa [norm_neg]
  have h := (VOA.Huang.AssocAssociator.hasSum_cbz_pow B hy).mul_left (ζ ^ A * (-1 : ℂ) ^ B)
  have hval : ζ ^ A * (-1 : ℂ) ^ B * (1 + -ζ) ^ B = ζ ^ A * (ζ - 1) ^ B := by
    rw [mul_assoc, ← mul_zpow, show (-1 : ℂ) * (1 + -ζ) = ζ - 1 by ring]
  rw [hval] at h
  let g : ℕ → ℤ := fun i => A + i
  have hg : Function.Injective g := fun i j hij => by simpa [g] using hij
  have hf : ∀ n ∉ Set.range g, ezero A B n * ζ ^ n = 0 := by
    intro n hn
    have : n < A := by
      by_contra hc
      exact hn ⟨(n - A).toNat, by simp only [g]; omega⟩
    rw [ezero_eq_zero this, zero_mul]
  refine (hg.hasSum_iff hf).mp (h.congr_fun fun i => ?_)
  simp only [Function.comp_apply, g, ezero, show B + (A + (i : ℤ)) - A = B + i by ring,
    show A + (i : ℤ) - A = i by ring, negOnePow_add'', negOnePow_natCast, negOnePow_eq_zpow B]
  rw [zpow_add₀ hζ0, zpow_natCast, neg_pow]
  ring

theorem hasSum_eone (A B : ℤ) {r : ℂ} (hr0 : r ≠ 0) (hr1 : ‖r‖ < 1) :
    HasSum (fun m : ℤ => eone A B m * r ^ m) ((1 + r) ^ A * r ^ B) := by
  have h := (VOA.Huang.AssocAssociator.hasSum_cbz_pow A hr1).mul_left (r ^ B)
  rw [mul_comm] at h
  let g : ℕ → ℤ := fun j => B + j
  have hg : Function.Injective g := fun i j hij => by simpa [g] using hij
  have hf : ∀ m ∉ Set.range g, eone A B m * r ^ m = 0 := by
    intro m hm
    have : m < B := by
      by_contra hc
      exact hm ⟨(m - B).toNat, by simp only [g]; omega⟩
    rw [eone_eq_zero this, zero_mul]
  refine (hg.hasSum_iff hf).mp (h.congr_fun fun j => ?_)
  simp only [Function.comp_apply, g, eone, show B + (j : ℤ) - B = j by ring]
  rw [zpow_add₀ hr0, zpow_natCast]
  ring

/-- The rational function `Σ_{k ∈ S} c_k ζ^k (ζ-1)^B`. -/
def ratFun (S : Finset ℤ) (c : ℤ → ℂ) (B : ℤ) (ζ : ℂ) : ℂ := ∑ k ∈ S, c k * (ζ ^ k * (ζ - 1) ^ B)

theorem hasSum_Einf (S : Finset ℤ) (c : ℤ → ℂ) (B : ℤ) {ζ : ℂ} (hζ : 1 < ‖ζ‖) :
    HasSum (fun n : ℤ => Einf S c B n * ζ ^ n) (ratFun S c B ζ) := by
  have h := hasSum_sum (s := S) fun k _ => (hasSum_einf k B hζ).mul_left (c k)
  refine h.congr_fun fun n => ?_
  simp only [Einf, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hasSum_Ezero (S : Finset ℤ) (c : ℤ → ℂ) (B : ℤ) {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ1 : ‖ζ‖ < 1) :
    HasSum (fun n : ℤ => Ezero S c B n * ζ ^ n) (ratFun S c B ζ) := by
  have h := hasSum_sum (s := S) fun k _ => (hasSum_ezero k B hζ0 hζ1).mul_left (c k)
  refine h.congr_fun fun n => ?_
  simp only [Ezero, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hasSum_Eone (S : Finset ℤ) (c : ℤ → ℂ) (B : ℤ) {r : ℂ} (hr0 : r ≠ 0) (hr1 : ‖r‖ < 1) :
    HasSum (fun m : ℤ => Eone S c B m * r ^ m) (ratFun S c B (1 + r)) := by
  have h := hasSum_sum (s := S) fun k _ => (hasSum_eone k B hr0 hr1).mul_left (c k)
  have hv : ratFun S c B (1 + r) = ∑ k ∈ S, c k * ((1 + r) ^ k * r ^ B) := by
    simp only [ratFun, add_sub_cancel_left]
  rw [hv]
  refine h.congr_fun fun m => ?_
  simp only [Eone, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## The main theorem -/

theorem differentiableAt_ratFun (S : Finset ℤ) (c : ℤ → ℂ) (B : ℤ) {ζ : ℂ} (h0 : ζ ≠ 0)
    (h1 : ζ ≠ 1) : DifferentiableAt ℂ (ratFun S c B) ζ := by
  unfold ratFun
  refine DifferentiableAt.fun_sum fun k _ => (differentiableAt_const _).mul ?_
  exact (differentiableAt_id.zpow (Or.inl h0)).mul
    ((differentiableAt_id.sub_const 1).zpow (Or.inl (sub_ne_zero.mpr h1)))

theorem isPreconnected_compl_zero_one : IsPreconnected (({0, 1} : Set ℂ)ᶜ) :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by rw [rank_real_complex]; norm_num)
    ((Set.countable_singleton 1).insert 0)).isPreconnected

/-- **The residue identity from three Laurent expansions of one function.** -/
theorem residue_of_glue {s t q : ℤ → ℂ} {n₀ n₁ m₁ : ℤ}
    (hs0 : ∀ n, n₀ < n → s n = 0) (ht0 : ∀ n, n < n₁ → t n = 0) (hq0 : ∀ m, m < m₁ → q m = 0)
    {Ψ : ℂ → ℂ} (hΨ : ∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ 1 → DifferentiableAt ℂ Ψ ζ)
    (hS : ∀ ζ : ℂ, 1 < ‖ζ‖ → HasSum (fun n : ℤ => s n * ζ ^ n) (Ψ ζ))
    (hT : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → HasSum (fun n : ℤ => t n * ζ ^ n) (Ψ ζ))
    (hQ : ∀ r : ℂ, r ≠ 0 → ‖r‖ < 1 → HasSum (fun m : ℤ => q m * r ^ m) (Ψ (1 + r)))
    (a ℓ : ℤ) : resInf a ℓ s - resZero a ℓ t = resOne a ℓ q := by
  classical
  set N : ℕ := (-m₁).toNat with hN
  -- the regular part at `1`
  have hd : ∀ r : ℂ, r ≠ 0 → ‖r‖ < 1 →
      HasSum (fun k : ℕ => q ((k : ℤ) - N) * r ^ k) (r ^ N * Ψ (1 + r)) := by
    intro r hr0 hr1
    have h1 := VOA.Huang.HKLLoc.hasSum_shift hr0 (hQ r hr0 hr1) N
    have h2 := VOA.Huang.HKLLoc.hasSum_nat_of_int (α := fun k : ℤ => q (k - N)) 0
      (fun k _ => hq0 _ (by omega)) h1
    simpa using h2
  have hsum : ∀ r : ℂ, ‖r‖ < 1 → Summable fun k : ℕ => q ((k : ℤ) - N) * r ^ k := by
    intro r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
      rw [Finset.mem_singleton] at hk
      rw [zero_pow hk, mul_zero]
    · exact (hd r hr0 hr).summable
  set g : ℂ → ℂ := fun r => ∑' k : ℕ, q ((k : ℤ) - N) * r ^ k with hg
  have hcont : ContinuousAt g 0 :=
    (VOA.Huang.HKLLoc.differentiableAt_powerSeries _ hsum (by simp)).continuousAt
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  have hB : ∀ ζ : ℂ, ζ ≠ 1 → ‖ζ - 1‖ < min δ 1 → ‖(ζ - 1) ^ N * Ψ ζ‖ ≤ ‖g 0‖ + 1 := by
    intro ζ hζ1 hζδ
    have hr0 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
    have hr1 : ‖ζ - 1‖ < 1 := lt_of_lt_of_le hζδ (min_le_right _ _)
    have e : (ζ - 1) ^ N * Ψ ζ = g (ζ - 1) := by
      have := (hd (ζ - 1) hr0 hr1).tsum_eq
      rw [show 1 + (ζ - 1) = ζ by ring] at this
      exact this.symm
    rw [e]
    have hδ' : dist (ζ - 1) 0 < δ := by
      rw [dist_zero_right]; exact lt_of_lt_of_le hζδ (min_le_left _ _)
    have hdist := hδg hδ'
    rw [dist_eq_norm] at hdist
    have := norm_sub_norm_le (g (ζ - 1)) (g 0)
    linarith
  have hconv := VOA.Huang.HKLLoc.conv_eq_of_glue (N := N) hs0 ht0 hS hT hΨ
    (lt_min hδ one_pos) hB
  -- the Laurent polynomial `(ζ-1)^N Ψ`
  set c : ℤ → ℂ := VOA.Huang.HKLLoc.conv N s with hc
  set S : Finset ℤ := Finset.Icc n₁ (n₀ + N) with hS'
  have hcS : ∀ k ∉ S, c k = 0 := by
    intro k hk
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    rcases hk with hk | hk
    · show c k = 0
      rw [hconv k]; exact VOA.Huang.HKLLoc.conv_eq_zero_of_lt ht0 hk
    · exact VOA.Huang.HKLLoc.conv_eq_zero_of_gt hs0 hk
  have hΨR : ∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ 1 → Ψ ζ = ratFun S c (-(N : ℤ)) ζ := by
    have hout : ∀ ζ : ℂ, 1 < ‖ζ‖ → Ψ ζ = ratFun S c (-(N : ℤ)) ζ := by
      intro ζ hζ
      have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ; linarith
      have hζ1 : ζ - 1 ≠ 0 := by
        intro h; rw [sub_eq_zero] at h; rw [h, norm_one] at hζ; exact lt_irrefl _ hζ
      have h1 := VOA.Huang.HKLLoc.hasSum_conv N hζ0 (hS ζ hζ)
      have h2 : HasSum (fun k : ℤ => c k * ζ ^ k) (∑ k ∈ S, c k * ζ ^ k) :=
        hasSum_sum_of_ne_finset_zero fun k hk => by rw [hcS k hk, zero_mul]
      have e := h1.unique h2
      unfold ratFun
      simp_rw [← mul_assoc, ← Finset.sum_mul, ← e, zpow_neg, zpow_natCast]
      field_simp
    have hU : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
    have hmem : ∀ ζ : ℂ, ζ ∈ (({0, 1} : Set ℂ)ᶜ) ↔ ζ ≠ 0 ∧ ζ ≠ 1 := by
      intro ζ; simp [not_or]
    have hΨa : AnalyticOnNhd ℂ Ψ (({0, 1} : Set ℂ)ᶜ) :=
      DifferentiableOn.analyticOnNhd (fun ζ hζ => ((hΨ ζ ((hmem ζ).mp hζ).1
        ((hmem ζ).mp hζ).2)).differentiableWithinAt) hU
    have hRa : AnalyticOnNhd ℂ (ratFun S c (-(N : ℤ))) (({0, 1} : Set ℂ)ᶜ) :=
      DifferentiableOn.analyticOnNhd (fun ζ hζ => (differentiableAt_ratFun S c _
        ((hmem ζ).mp hζ).1 ((hmem ζ).mp hζ).2).differentiableWithinAt) hU
    have h2 : (2 : ℂ) ∈ (({0, 1} : Set ℂ)ᶜ) := (hmem 2).mpr ⟨by norm_num, by norm_num⟩
    have hev : Ψ =ᶠ[𝓝 (2 : ℂ)] ratFun S c (-(N : ℤ)) := by
      have ho : IsOpen {ζ : ℂ | 1 < ‖ζ‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [ho.mem_nhds (by norm_num : (1 : ℝ) < ‖(2 : ℂ)‖)] with ζ hζ
      exact hout ζ hζ
    have := hΨa.eqOn_of_preconnected_of_eventuallyEq hRa isPreconnected_compl_zero_one h2 hev
    intro ζ h0 h1
    exact this ((hmem ζ).mpr ⟨h0, h1⟩)
  -- identification of the three expansions
  have hsE : s = Einf S c (-(N : ℤ)) := by
    have hu := laurent_inf_unique (u := fun n => s n - Einf S c (-(N : ℤ)) n) (n₀ := n₀)
      (fun n hn => by
        dsimp only
        rw [hs0 n hn, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        rw [einf_eq_zero (by omega), mul_zero])
      (fun ζ hζ => by
        have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ; linarith
        have hζ1 : ζ ≠ 1 := by rintro rfl; simp at hζ
        have := (hS ζ hζ).sub (hasSum_Einf S c (-(N : ℤ)) hζ)
        rw [← hΨR ζ hζ0 hζ1, sub_self] at this
        exact this.congr_fun fun n => by ring)
    funext n
    exact sub_eq_zero.mp (congrFun hu n)
  have htE : t = Ezero S c (-(N : ℤ)) := by
    have hu := laurent_zero_unique (u := fun n => t n - Ezero S c (-(N : ℤ)) n) (n₁ := n₁)
      (fun n hn => by
        dsimp only
        rw [ht0 n hn, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        rw [ezero_eq_zero (by omega), mul_zero])
      (fun ζ hζ0 hζ => by
        have hζ1 : ζ ≠ 1 := by rintro rfl; simp at hζ
        have := (hT ζ hζ0 hζ).sub (hasSum_Ezero S c (-(N : ℤ)) hζ0 hζ)
        rw [← hΨR ζ hζ0 hζ1, sub_self] at this
        exact this.congr_fun fun n => by ring)
    funext n
    exact sub_eq_zero.mp (congrFun hu n)
  have hqE : q = Eone S c (-(N : ℤ)) := by
    have hu := laurent_zero_unique (u := fun m => q m - Eone S c (-(N : ℤ)) m)
      (n₁ := min m₁ (-(N : ℤ)))
      (fun m hm => by
        dsimp only
        rw [hq0 m (by omega), zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [eone_eq_zero (by omega), mul_zero])
      (fun r hr0 hr => by
        have h10 : 1 + r ≠ 0 := by
          intro h
          have : r = -1 := by linear_combination h
          rw [this, norm_neg, norm_one] at hr; exact lt_irrefl _ hr
        have h11 : 1 + r ≠ 1 := by intro h; apply hr0; linear_combination h
        have := (hQ r hr0 hr).sub (hasSum_Eone S c (-(N : ℤ)) hr0 hr)
        rw [← hΨR (1 + r) h10 h11, sub_self] at this
        exact this.congr_fun fun n => by ring)
    funext m
    exact sub_eq_zero.mp (congrFun hu m)
  rw [hsE, htE, hqE]
  exact residue_E S c (-(N : ℤ)) a ℓ

end VOA.Classification.COne.McRaeO5b
