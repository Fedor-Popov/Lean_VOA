/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHighEndpoint

/-!
# The jet-ideal Poincaré lemma in `T`-degree `n + 1`

`JetPoincare n N (n + 1) E` for **every** `N` and `E`.  For `F` of degree `n + 1` the derivatives
`∂_M F` (`M ≥ N`) are homogeneous of degree `n` in `J_n`, hence scalar multiples
`a_M (Tⁿ)_{Q - M}` (`Q = E - n - 1`) of a single jet.  The symmetry of the mixed derivatives
`∂_L ∂_M F = ∂_M ∂_L F` forces `a_M = a_L` whenever `L + M ≤ Q`, because `(T^{n-1})_q ≠ 0`.  Then
the explicit primitive

  `ψ = c (T^{n+1})_Q + Σ_{M = N}^{Q} (a_M - (n+1) c) T_M (Tⁿ)_{Q - M}`,   `c = a_N / (n + 1)`,

lies in `J_n` and has `∂_M ψ = ∂_M F` for every `M ≥ N` (the terms with `Q - M ≥ N` have zero
coefficient, and the others involve only jets of index `< N`).  So `F - ψ` involves only
`T_0, …, T_{N-1}`.

* `hc_mem_jetSpanT`, `eq_smul_jg` — the degree-`n` part of an element of `J_n` is a
  `ℂ`-combination of jets; in a fixed weight it is a multiple of one jet;
* `jg_ne_zero` — `(Tⁿ)_q ≠ 0` for `n ≥ 1`;
* `jetPoincare_degSucc` — **`JetPoincare n N (n + 1) E`** for all `N`, `E`;
* `jetPoincare_of_wt_lt` — **`JetPoincare n N k E` for `E < 2N + k`** (no monomial has two
  indices `≥ N`, so `F = F_0 + Σ_{M ≥ N} T_M ∂_M F`);
* `modelSocleMembership_of_le_three` — **`ModelSocleMembership n r` for every `r ≤ n + 3`**,
  unconditionally;
* `JetPoincareHigh2 n` (slots `N ≥ 2`, `k ≥ n + 2`) and its core `JetPoincareCore n` (also
  `E ≥ 2N + k`); `twoSeries_gradedUnitary_of_strictModel_jetPoincare2`,
  `twoSeries_gradedUnitary_of_strictModel_jetPoincareCore` — the endpoint with those inputs.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

namespace HighDegSucc

open HighJet HighReduce HighEndpoint SingTailDiag LiftDegN

theorem jg_isHomogeneous (n j : ℕ) : (jg n j).IsHomogeneous n := by
  have h := jg_isWH 1 0 n j
  have hw : (fun m : ℕ => 1 + 0 * m) = (1 : ℕ → ℕ) := by funext m; simp
  rw [hw] at h
  simpa using h

/-- The degree-`m` component of `f * g` for `g` homogeneous of degree `m`. -/
theorem hc_mul_of_isHomogeneous {f g : TPoly} {m : ℕ} (hg : g.IsHomogeneous m) :
    homogeneousComponent m (f * g) = MvPolynomial.C (coeff 0 f) * g := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [Finset.sum_mul, map_sum, Finset.sum_eq_single 0]
  · rw [homogeneousComponent_zero, homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr ((isHomogeneous_C _ _).mul hg)), zero_add, if_pos rfl]
  · intro i _ hi
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      ((homogeneousComponent_isHomogeneous i f).mul hg)), if_neg (by omega)]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

/-- The degree-`n` component of an element of `J_n` is a `ℂ`-combination of jets. -/
theorem hc_mem_jetSpanT {n : ℕ} {G : TPoly} (hG : G ∈ jetIdealT n) :
    homogeneousComponent n G ∈ jetSpanT n := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
  rw [Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_eq_mul, hc_mul_of_isHomogeneous (jg_isHomogeneous n j), ← smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem pw_jg (n w j : ℕ) : pw w (jg n j) = if w = j + n then jg n j else 0 := by
  have := coeff_tSer_pow_isWH n j
  split_ifs with h
  · rw [h]; exact this.weightedHomogeneousComponent_same
  · exact this.weightedHomogeneousComponent_ne w h

theorem eq_sum_pw {n w : ℕ} {G : TPoly} (hG : G ∈ jetIdealT n) (hh : G.IsHomogeneous n)
    (hw : IsWeightedHomogeneous wT G w) :
    ∃ c : ℕ →₀ ℂ, G = c.sum fun j a => a • pw w (jg n j) := by
  have h1 : homogeneousComponent n G = G := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hh), if_pos rfl]
  have h2 : pw w G = G := hw.weightedHomogeneousComponent_same
  have hS := hc_mem_jetSpanT hG
  rw [h1] at hS
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hS
  refine ⟨c, ?_⟩
  conv_lhs => rw [← h2, ← hc]
  rw [Finsupp.sum, map_sum, Finsupp.sum]
  simp only [map_smul]

/-- A homogeneous element of `J_n` of degree `n` and weight `w ≥ n` is a multiple of
`(Tⁿ)_{w-n}`. -/
theorem eq_smul_jg {n w : ℕ} (hnw : n ≤ w) {G : TPoly} (hG : G ∈ jetIdealT n)
    (hh : G.IsHomogeneous n) (hw : IsWeightedHomogeneous wT G w) :
    ∃ a : ℂ, G = a • jg n (w - n) := by
  obtain ⟨c, hc⟩ := eq_sum_pw hG hh hw
  refine ⟨c (w - n), ?_⟩
  rw [hc, Finsupp.sum]
  have hcond : ∀ j, (w = j + n) ↔ (j = w - n) := fun j => by omega
  simp only [pw_jg, hcond, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hm, zero_smul]

/-- A homogeneous element of `J_n` of degree `n` and weight `w < n` vanishes. -/
theorem eq_zero_of_lt {n w : ℕ} (hwn : w < n) {G : TPoly} (hG : G ∈ jetIdealT n)
    (hh : G.IsHomogeneous n) (hw : IsWeightedHomogeneous wT G w) : G = 0 := by
  obtain ⟨c, hc⟩ := eq_sum_pw hG hh hw
  rw [hc, Finsupp.sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pw_jg, if_neg (by omega), smul_zero]

/-! ### Auxiliary facts -/

theorem pderiv_comm_T (u v : ℕ) (p : TPoly) :
    pderiv u (pderiv v p) = pderiv v (pderiv u p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s h =>
    rw [pderiv_mul, pderiv_mul, map_add, map_add, pderiv_mul, pderiv_mul]
    simp only [pderiv_X, Pi.single_apply, h]
    by_cases hsu : s = u <;> by_cases hsv : s = v <;> simp_all <;> ring

/-- The value of `(Tⁿ)_q` at `T_m = 1` is a positive integer. -/
theorem jg_eval_one : ∀ (n q : ℕ), 1 ≤ n →
    ∃ c : ℕ, 1 ≤ c ∧ aeval (fun _ : ℕ => (1 : ℂ)) (jg n q) = c
  | 0, _, h => absurd h (by omega)
  | 1, q, _ => ⟨1, le_rfl, by simp [jg, tSer]⟩
  | n + 2, q, _ => by
    have ih : ∀ p : ℕ, ∃ c : ℕ, 1 ≤ c ∧ aeval (fun _ : ℕ => (1 : ℂ)) (jg (n + 1) p) = c :=
      fun p => jg_eval_one (n + 1) p (by omega)
    choose c hc1 hc2 using ih
    refine ⟨∑ p ∈ Finset.antidiagonal q, c p.1, ?_, ?_⟩
    · calc 1 ≤ c (0, q).1 := hc1 _
        _ ≤ ∑ p ∈ Finset.antidiagonal q, c p.1 :=
          Finset.single_le_sum (f := fun p : ℕ × ℕ => c p.1) (fun _ _ => Nat.zero_le _)
            (Finset.mem_antidiagonal.mpr (by simp))
    · rw [jg, pow_succ, PowerSeries.coeff_mul, map_sum, Nat.cast_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, ← jg, hc2, tSer, PowerSeries.coeff_mk, aeval_X, mul_one]

/-- `(Tⁿ)_q ≠ 0` for `n ≥ 1`. -/
theorem jg_ne_zero {n : ℕ} (hn : 1 ≤ n) (q : ℕ) : jg n q ≠ 0 := by
  intro h
  obtain ⟨c, hc, he⟩ := jg_eval_one n q hn
  rw [h, map_zero] at he
  have : (c : ℂ) ≠ 0 := by exact_mod_cast (show c ≠ 0 by omega)
  exact this he.symm

theorem jg_succ_mem (n Q : ℕ) : jg (n + 1) Q ∈ jetIdealT n := by
  rw [jg, pow_succ, PowerSeries.coeff_mul]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (jg_mem n p.1)

/-- If `F` has weight `E < M + 1`, it does not involve `T_M`. -/
theorem pderiv_eq_zero_of_wt {F : TPoly} {E M : ℕ} (hF : IsWeightedHomogeneous wT F E)
    (h : E < M + 1) : pderiv M F = 0 := by
  rw [as_sum F, map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [pderiv_monomial]
  have hsE := hF (mem_support_iff.mp hs)
  by_cases hsM : s M = 0
  · rw [hsM]; simp
  · exfalso
    have := weight_sub_single (w := wT) (Nat.one_le_iff_ne_zero.mpr hsM)
    simp only [wT] at this
    omega

theorem eq_zero_of_wt_lt {F : TPoly} {k E : ℕ} (hk : F.IsHomogeneous k)
    (hw : IsWeightedHomogeneous wT F E) (h : E < k) : F = 0 := by
  rw [as_sum F]
  refine Finset.sum_eq_zero fun s hs => ?_
  exfalso
  have h1 : Finsupp.weight 1 s = k := hk (mem_support_iff.mp hs)
  have h2 : Finsupp.weight wT s = E := hw (mem_support_iff.mp hs)
  have hle : Finsupp.weight 1 s ≤ Finsupp.weight wT s := by
    rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Pi.one_apply, smul_eq_mul, mul_one, wT]; nlinarith
  omega

theorem mem_jetIdealT_one {k E : ℕ} (hk : 1 ≤ k) {F : TPoly}
    (hF : F ∈ tMonW TPoly MvPolynomial.X k (E : ℤ)) : F ∈ jetIdealT 1 := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, -, rfl⟩ := hP
    obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
      rcases l with _ | ⟨x, l'⟩
      · simp at hl; omega
      · exact ⟨x, l', rfl⟩
    rw [List.map_cons, List.prod_cons]
    refine Ideal.mul_mem_right _ _ ?_
    have : (MvPolynomial.X x : TPoly) = jg 1 x := by simp [jg, tSer]
    rw [this]; exact jg_mem 1 x
  | zero => exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => exact add_mem hP hQ
  | smul c P _ hP => rw [smul_eq_C_mul]; exact Ideal.mul_mem_left _ _ hP

/-- **The jet-ideal Poincaré lemma in `T`-degree `n + 1`.** -/
theorem jetPoincare_degSucc {n : ℕ} (hn : 1 ≤ n) (N E : ℕ) : JetPoincare n N (n + 1) E := by
  intro F hF hder
  -- `n = 1`: `J_1` contains every `T_m`
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (mem_jetIdealT_one (by omega) hF)]
    exact Submodule.zero_mem _
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hFh : F.IsHomogeneous (n' + 1 + 1) := homogeneous_of_tMonW hF
  have hFw : IsWeightedHomogeneous wT F E := by
    rw [← pw_tMonW hF]; exact weightedHomogeneousComponent_isWeightedHomogeneous E F
  rcases Nat.lt_or_ge E (n' + 1 + 1) with hEs | hEl
  · rw [eq_zero_of_wt_lt hFh hFw hEs, map_zero]; exact Submodule.zero_mem _
  set Q := E - (n' + 2) with hQ
  -- the derivatives are multiples of single jets
  have hderw : ∀ M, M + 1 ≤ E →
      IsWeightedHomogeneous wT (pderiv M F) (E - (M + 1)) := fun M hM =>
    hFw.pderiv (by simp only [wT]; omega)
  have hderh : ∀ M, (pderiv M F).IsHomogeneous (n' + 1) := fun M => by
    have := hFh.pderiv (i := M); simpa using this
  have hex : ∀ M, ∃ a : ℂ, N ≤ M → M ≤ Q → pderiv M F = a • jg (n' + 1) (Q - M) := by
    intro M
    by_cases hM : N ≤ M ∧ M ≤ Q
    · obtain ⟨a, ha⟩ := eq_smul_jg (show n' + 1 ≤ E - (M + 1) by omega) (hder M hM.1) (hderh M)
        (hderw M (by omega))
      refine ⟨a, fun _ _ => ?_⟩
      rw [ha, show E - (M + 1) - (n' + 1) = Q - M by omega]
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hM⟩
  choose a ha using hex
  have hzero : ∀ M, N ≤ M → Q < M → pderiv M F = 0 := by
    intro M hNM hQM
    rcases Nat.lt_or_ge E (M + 1) with h | h
    · exact pderiv_eq_zero_of_wt hFw h
    · exact eq_zero_of_lt (show E - (M + 1) < n' + 1 by omega) (hder M hNM) (hderh M) (hderw M h)
  -- symmetry of mixed derivatives
  have hsym : ∀ L M, N ≤ L → N ≤ M → L + M ≤ Q → a M = a L := by
    intro L M hL hM hLM
    have h := pderiv_comm_T L M F
    rw [ha M hM (by omega), ha L hL (by omega), (pderiv L).map_smul, (pderiv M).map_smul,
      pderiv_jg, pderiv_jg, if_pos (by omega), if_pos (by omega),
      show Q - M - L = Q - L - M by omega] at h
    have h2 : (a M - a L) • (((n' + 1 : ℕ) : TPoly) * jg n' (Q - L - M)) = 0 := by
      rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exfalso
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n')) h4
      · exact jg_ne_zero (by omega) _ h4
  -- the primitive
  set c : ℂ := if 2 * N ≤ Q then a N / ((n' + 2 : ℕ) : ℂ) else 0 with hc
  set ψ : TPoly := c • jg (n' + 2) Q + ∑ M ∈ Finset.Icc N Q,
    (a M - ((n' + 2 : ℕ) : ℂ) * c) • (MvPolynomial.X M * jg (n' + 1) (Q - M)) with hψ
  have hcoef : ∀ M ∈ Finset.Icc N Q, ∀ L, N ≤ L → L ≤ Q - M →
      a M - ((n' + 2 : ℕ) : ℂ) * c = 0 := by
    intro M hM L hL hLM
    have hM' := Finset.mem_Icc.mp hM
    have h2N : 2 * N ≤ Q := by omega
    rw [hc, if_pos h2N, hsym N M le_rfl hM'.1 (by omega), mul_div_cancel₀]
    · ring
    · exact_mod_cast (Nat.succ_ne_zero (n' + 1))
  have hψd : ∀ L, N ≤ L → pderiv L ψ = pderiv L F := by
    intro L hL
    rw [hψ, map_add, (pderiv L).map_smul, map_sum, pderiv_jg]
    have hterm : ∀ M ∈ Finset.Icc N Q,
        pderiv L ((a M - ((n' + 2 : ℕ) : ℂ) * c) •
          (MvPolynomial.X M * jg (n' + 1) (Q - M))) =
        if M = L then (a M - ((n' + 2 : ℕ) : ℂ) * c) • jg (n' + 1) (Q - M) else 0 := by
      intro M hM
      rw [(pderiv L).map_smul, Derivation.leibniz, pderiv_jg, pderiv_X, smul_eq_mul, smul_eq_mul]
      by_cases hLM : L ≤ Q - M
      · rw [hcoef M hM L hL hLM, zero_smul]
        split_ifs <;> simp
      · rw [if_neg hLM, mul_zero, zero_add, Pi.single_apply]
        by_cases hML : M = L
        · rw [if_pos hML, if_pos hML, mul_one]
        · rw [if_neg hML, if_neg hML, mul_zero, smul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    by_cases hLQ : L ≤ Q
    · rw [if_pos (Finset.mem_Icc.mpr ⟨hL, hLQ⟩), if_pos hLQ, ha L hL hLQ,
        show ((n' + 1 + 1 : ℕ) : TPoly) * jg (n' + 1) (Q - L) =
          ((n' + 2 : ℕ) : ℂ) • jg (n' + 1) (Q - L) by
          rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul],
        smul_smul, ← add_smul]
      congr 1
      ring
    · rw [if_neg (fun h => hLQ (Finset.mem_Icc.mp h).2), if_neg hLQ, smul_zero, add_zero,
        hzero L hL (by omega)]
  have hψJ : ψ ∈ jetIdealT (n' + 1) := by
    rw [hψ]
    refine add_mem ?_ (Ideal.sum_mem _ fun M _ => ?_)
    · rw [smul_eq_C_mul]; exact Ideal.mul_mem_left _ _ (jg_succ_mem (n' + 1) Q)
    · rw [smul_eq_C_mul]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (jg_mem _ _))
  have hψh : ψ ∈ homogeneousSubmodule ℕ ℂ (n' + 1 + 1) := by
    rw [hψ]
    refine add_mem (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).mpr
      (jg_isHomogeneous _ _))) (Submodule.sum_mem _ fun M _ => Submodule.smul_mem _ _ ?_)
    rw [mem_homogeneousSubmodule]
    have := (isHomogeneous_X ℂ M).mul (jg_isHomogeneous (n' + 1) (Q - M))
    rwa [add_comm 1 (n' + 1)] at this
  have hψw : ψ ∈ weightedHomogeneousSubmodule ℂ wT E := by
    rw [hψ]
    refine add_mem (Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun M hM => Submodule.smul_mem _ _ ?_)
    · rw [mem_weightedHomogeneousSubmodule]
      have := coeff_tSer_pow_isWH (n' + 2) Q
      rwa [show Q + (n' + 2) = E by omega] at this
    · rw [mem_weightedHomogeneousSubmodule]
      have hM' := Finset.mem_Icc.mp hM
      have := (isWeightedHomogeneous_X ℂ wT M).mul (coeff_tSer_pow_isWH (n' + 1) (Q - M))
      rwa [show wT M + (Q - M + (n' + 1)) = E by simp only [wT]; omega] at this
  have hψT : ψ ∈ tMonW TPoly MvPolynomial.X (n' + 1 + 1) (E : ℤ) :=
    mem_tMonW_of_isWH ((mem_homogeneousSubmodule _ _).mp hψh)
      ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hψw)
  have hdiffT : F - ψ ∈ tMonW TPoly MvPolynomial.X (n' + 1 + 1) (E : ℤ) := sub_mem hF hψT
  have hvars : ∀ m ∈ (F - ψ).vars, m < N := by
    intro m hm
    by_contra hmN
    have h0 : pderiv m (F - ψ) = 0 := by
      rw [map_sub, hψd m (by omega), sub_self]
    exact InclLead.not_mem_vars_of_pderiv_eq_zero h0 hm
  have hmk : Ideal.Quotient.mk (jetIdealT (n' + 1)) F =
      Ideal.Quotient.mk (jetIdealT (n' + 1)) (F - ψ) := by
    rw [Ideal.Quotient.eq, sub_sub_cancel]; exact hψJ
  rw [hmk]
  exact mk_mem_boxW_of_vars hdiffT hvars

/-! ### At most one high index -/

/-- **The jet-ideal Poincaré lemma when no monomial has two indices `≥ N`** (`E < 2N + k`):
then `F = F_0 + Σ_{M ≥ N} T_M ∂_M F` with `F_0` free of high indices. -/
theorem jetPoincare_of_wt_lt {n N k E : ℕ} (hE : E < 2 * N + k) : JetPoincare n N k E := by
  classical
  intro F hF hder
  set w : ℕ → ℕ := fun m => if N ≤ m then 1 else 0 with hw
  have hFw : IsWeightedHomogeneous wT F E := by
    rw [← pw_tMonW hF]; exact weightedHomogeneousComponent_isWeightedHomogeneous E F
  have hFh : F.IsHomogeneous k := homogeneous_of_tMonW hF
  -- every monomial has at most one high index
  have hone : ∀ s ∈ F.support, Finsupp.weight w s ≤ 1 := by
    intro s hs
    have h1 : Finsupp.weight 1 s = k := hFh (mem_support_iff.mp hs)
    have h2 : Finsupp.weight wT s = E := hFw (mem_support_iff.mp hs)
    by_contra hgt
    have key : Finsupp.weight 1 s + N * Finsupp.weight w s ≤ Finsupp.weight wT s := by
      rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum,
        Finsupp.sum, Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [hw, Pi.one_apply, smul_eq_mul, wT]
      split_ifs with hi
      · nlinarith
      · nlinarith
    have : 2 * N ≤ N * Finsupp.weight w s := by
      have : 2 ≤ Finsupp.weight w s := by omega
      nlinarith
    omega
  set H := ∑ m ∈ F.vars, ((w m : ℕ) : TPoly) * (MvPolynomial.X m * pderiv m F) with hH
  have hHJ : H ∈ jetIdealT n := by
    refine Ideal.sum_mem _ fun m _ => ?_
    by_cases hm : N ≤ m
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hder m hm))
    · simp [hw, hm]
  have hHeq : H = ∑ s ∈ F.support, ((Finsupp.weight w s : ℕ) : TPoly) * monomial s (coeff s F) :=
    euler_sum w F F.vars subset_rfl
  -- `F - H` has no high index
  have hlow : F - H = ∑ s ∈ F.support,
      (if Finsupp.weight w s = 0 then monomial s (coeff s F) else 0) := by
    have hF' : F = ∑ s ∈ F.support, monomial s (coeff s F) := as_sum F
    rw [hHeq]
    nth_rewrite 1 [hF']
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := hone s hs
    rcases Nat.lt_or_ge (Finsupp.weight w s) 1 with h0 | h1
    · rw [if_pos (by omega), show Finsupp.weight w s = 0 by omega]; simp
    · rw [if_neg (by omega), show Finsupp.weight w s = 1 by omega]; simp
  have hzero : ∀ s ∈ F.support, Finsupp.weight w s = 0 → ∀ m, N ≤ m → s m = 0 := by
    intro s _ h0 m hm
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at h0
    by_contra hsm
    have := h0 m (Finsupp.mem_support_iff.mpr hsm)
    simp only [hw, if_pos hm, smul_eq_mul, mul_one] at this
    exact hsm this
  have hpd : ∀ m, N ≤ m → pderiv m (F - H) = 0 := by
    intro m hm
    rw [hlow, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    split_ifs with h0
    · rw [pderiv_monomial, hzero s hs h0 m hm]; simp
    · exact map_zero _
  have hvars : ∀ m ∈ (F - H).vars, m < N := by
    intro m hm
    by_contra hmN
    exact InclLead.not_mem_vars_of_pderiv_eq_zero (hpd m (by omega)) hm
  have hT : F - H ∈ tMonW TPoly MvPolynomial.X k (E : ℤ) := by
    rw [hlow]
    refine Submodule.sum_mem _ fun s hs => ?_
    split_ifs
    · exact monomial_mem_tMonW s _ (by
        have := hFh (mem_support_iff.mp hs)
        rwa [Finsupp.degree_eq_weight_one]) (hFw (mem_support_iff.mp hs))
    · exact Submodule.zero_mem _
  have hmk : Ideal.Quotient.mk (jetIdealT n) F = Ideal.Quotient.mk (jetIdealT n) (F - H) := by
    rw [Ideal.Quotient.eq, sub_sub_cancel]; exact hHJ
  rw [hmk]
  exact mk_mem_boxW_of_vars hT hvars

/-! ### The membership bound -/

/-- **`ModelSocleMembership n r` for every `r ≤ n + 3`**, unconditionally. -/
theorem modelSocleMembership_of_le_three {n r : ℕ} (hn : 1 ≤ n) (hr : r ≤ n + 3) :
    ModelSocleMembership n r :=
  modelSocleMembership_of_below hn fun d N hN =>
    rank_vMem_le hn hN (vMem_le_box hn d hN fun h2 hk E => by
      rw [show r - N = n + 1 by omega]
      exact jetPoincare_degSucc hn N E)

/-- **The remaining input**: the jet-ideal Poincaré lemma in the slots with `N ≥ 2` and `T`-degree
`k ≥ n + 2`. -/
def JetPoincareHigh2 (n : ℕ) : Prop :=
  ∀ N k E : ℕ, 2 ≤ N → n + 2 ≤ k → JetPoincare n N k E

/-- **The core of the remaining input**: the slots `N ≥ 2`, `k ≥ n + 2`, weight `E ≥ 2N + k` (where
two indices `≥ N` can occur in one monomial). -/
def JetPoincareCore (n : ℕ) : Prop :=
  ∀ N k E : ℕ, 2 ≤ N → n + 2 ≤ k → 2 * N + k ≤ E → JetPoincare n N k E

theorem jetPoincareHigh2_of_core {n : ℕ} (h : JetPoincareCore n) : JetPoincareHigh2 n := by
  intro N k E hN hk
  rcases Nat.lt_or_ge E (2 * N + k) with hlt | hge
  · exact jetPoincare_of_wt_lt hlt
  · exact h N k E hN hk hge

theorem jetPoincareHigh_of_two {n : ℕ} (hn : 1 ≤ n) (h : JetPoincareHigh2 n) :
    JetPoincareHigh n := by
  intro N k E hN hk
  rcases Nat.lt_or_ge k (n + 2) with hlt | hge
  · rw [show k = n + 1 by omega]; exact jetPoincare_degSucc hn N E
  · exact h N k E hN hge

end HighDegSucc

open HighDegSucc HighEndpoint

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the jet-ideal Poincaré lemma `JetPoincareHigh2 n` in the slots `N ≥ 2`,
`k ≥ n + 2`. -/
theorem twoSeries_gradedUnitary_of_strictModel_jetPoincare2 (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (h : JetPoincareHigh2 n) :
    VirGradedUnitarity.VirGradedUnitary (twoSeriesLevels n).c
      (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_jetPoincare n hn hA det (jetPoincareHigh_of_two hn h)





/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the core `JetPoincareCore n` of the jet-ideal Poincaré lemma (slots `N ≥ 2`,
`k ≥ n + 2`, weight `≥ 2N + k`). -/
theorem twoSeries_gradedUnitary_of_strictModel_jetPoincareCore (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (h : JetPoincareCore n) :
    VirGradedUnitarity.VirGradedUnitary (twoSeriesLevels n).c
      (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_jetPoincare2 n hn hA det (jetPoincareHigh2_of_core h)

end

end VOA.TwoSeries.StrictModel
