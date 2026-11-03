/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHighDegSucc

/-!
# The jet-ideal Poincaré lemma when every doubly-high monomial carries `T_0ⁿ`

`JetPoincare n N k E` for `1 ≤ N` and `E + n + 2 ≤ 2N + 2k`.  In that range every monomial of
`T`-degree `k` and weight `E` with **two or more** indices `≥ N` has `T_0`-exponent `≥ n`
(the index sum is `E - k`, two high indices use up `≥ 2N`, so at most `E - k - 2(N - 1)` of the
indices are nonzero).  Such monomials lie in `T_0ⁿ · ℂ[T] ⊆ J_n` (`T_0ⁿ = (Tⁿ)_0`), and their
derivatives `∂_M`, `M ≥ 1`, stay in `T_0ⁿ · ℂ[T]`.  Removing them leaves a polynomial with at most
one high index per monomial, still satisfying the hypothesis, which is handled by the high Euler
identity exactly as in `jetPoincare_of_wt_lt`.

* `jg_zero_eq` — `(Tⁿ)_0 = T_0ⁿ`;
* `mk_mem_boxW_of_atMostOne` — the Poincaré conclusion for any `F` all of whose monomials have at
  most one index `≥ N` (the core of `jetPoincare_of_wt_lt`, with the weight bound replaced by the
  monomial condition);
* `jetPoincare_of_T0` — **`JetPoincare n N k E` for `1 ≤ N`, `E + n + 2 ≤ 2N + 2k`**;
* `JetPoincareCoreT0 n` — the remaining slots (`N ≥ 2`, `k ≥ n + 2`, `2N + k ≤ E`,
  `2N + 2k < E + n + 2`); `jetPoincareCore_of_T0` and
  `twoSeries_gradedUnitary_of_strictModel_jetPoincareCoreT0` — the endpoint with the
  smaller input.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

namespace PoincareZero

open HighJet HighReduce HighEndpoint HighDegSucc SingTailDiag LiftDegN

/-- `(Tⁿ)_0 = T_0ⁿ`. -/
theorem jg_zero_eq (n : ℕ) : jg n 0 = (X 0 : TPoly) ^ n := by
  rw [jg, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, tSer, PowerSeries.coeff_mk]

theorem X0_pow_mem (n : ℕ) : (X 0 : TPoly) ^ n ∈ jetIdealT n := by
  rw [← jg_zero_eq]; exact jg_mem n 0

/-- Elements of `T_0ⁿ · ℂ[T]` have all derivatives `∂_M`, `M ≥ 1`, in `J_n`. -/
theorem pderiv_mem_of_mem_span {n M : ℕ} (hM : 1 ≤ M) {G : TPoly}
    (hG : G ∈ Ideal.span {(X 0 : TPoly) ^ n}) : pderiv M G ∈ jetIdealT n := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hG
  rw [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X, Pi.single_apply, if_neg (by omega)]
  simp only [mul_zero, smul_zero, zero_add, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (X0_pow_mem n)

/-! ### At most one high index per monomial -/

/-- **The Poincaré conclusion when every monomial has at most one index `≥ N`.** -/
theorem mk_mem_boxW_of_atMostOne {n N k E : ℕ} {F : TPoly}
    (hF : F ∈ tMonW TPoly MvPolynomial.X k (E : ℤ))
    (hder : ∀ M, N ≤ M → pderiv M F ∈ jetIdealT n)
    (hone : ∀ s ∈ F.support,
      Finsupp.weight (fun m : ℕ => if N ≤ m then 1 else 0) s ≤ 1) :
    Ideal.Quotient.mk (jetIdealT n) F ∈ boxW (tn n) N k (E : ℤ) := by
  classical
  set w : ℕ → ℕ := fun m => if N ≤ m then 1 else 0 with hw
  have hFw : IsWeightedHomogeneous wT F E := by
    rw [← pw_tMonW hF]; exact weightedHomogeneousComponent_isWeightedHomogeneous E F
  have hFh : F.IsHomogeneous k := homogeneous_of_tMonW hF
  set H := ∑ m ∈ F.vars, ((w m : ℕ) : TPoly) * (MvPolynomial.X m * pderiv m F) with hH
  have hHJ : H ∈ jetIdealT n := by
    refine Ideal.sum_mem _ fun m _ => ?_
    by_cases hm : N ≤ m
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hder m hm))
    · simp [hw, hm]
  have hHeq : H = ∑ s ∈ F.support, ((Finsupp.weight w s : ℕ) : TPoly) * monomial s (coeff s F) :=
    euler_sum w F F.vars subset_rfl
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

/-! ### Splitting off the doubly-high monomials -/

/-- The part of `F` supported on monomials satisfying `p`. -/
def filt (p : (ℕ →₀ ℕ) → Prop) [DecidablePred p] (F : TPoly) : TPoly :=
  Finsupp.filter p F

theorem coeff_filt (p : (ℕ →₀ ℕ) → Prop) [DecidablePred p] (F : TPoly) (s : ℕ →₀ ℕ) :
    coeff s (filt p F) = if p s then coeff s F else 0 := by
  simp only [filt, coeff]
  exact Finsupp.filter_apply p F s

theorem filt_add_filt_not (p : (ℕ →₀ ℕ) → Prop) [DecidablePred p] (F : TPoly) :
    filt p F + filt (fun s => ¬ p s) F = F := by
  ext s
  rw [coeff_add, coeff_filt, coeff_filt]
  split_ifs <;> simp

theorem mem_support_filt {p : (ℕ →₀ ℕ) → Prop} [DecidablePred p] {F : TPoly} {s : ℕ →₀ ℕ}
    (hs : s ∈ (filt p F).support) : p s ∧ s ∈ F.support := by
  rw [mem_support_iff, coeff_filt] at hs
  split_ifs at hs with h
  · exact ⟨h, mem_support_iff.mpr hs⟩
  · exact absurd rfl hs

theorem filt_isWH {p : (ℕ →₀ ℕ) → Prop} [DecidablePred p] {w : ℕ → ℕ} {F : TPoly} {d : ℕ}
    (hF : IsWeightedHomogeneous w F d) : IsWeightedHomogeneous w (filt p F) d := by
  intro s hs
  rw [coeff_filt] at hs
  split_ifs at hs
  · exact hF hs
  · exact absurd rfl hs

theorem filt_isHomogeneous {p : (ℕ →₀ ℕ) → Prop} [DecidablePred p] {F : TPoly} {d : ℕ}
    (hF : F.IsHomogeneous d) : (filt p F).IsHomogeneous d := by
  intro s hs
  rw [coeff_filt] at hs
  split_ifs at hs
  · exact hF hs
  · exact absurd rfl hs

/-- The counting estimate: a monomial of degree `k`, weight `E` with at least two indices `≥ N`
(`1 ≤ N`) has `T_0`-exponent `≥ 2k + 2N - 2 - E`. -/
theorem s0_ge {N k E : ℕ} (hN : 1 ≤ N) (s : ℕ →₀ ℕ) (hk : Finsupp.weight 1 s = k)
    (hE : Finsupp.weight wT s = E)
    (h2 : 2 ≤ Finsupp.weight (fun m : ℕ => if N ≤ m then 1 else 0) s) :
    2 * k + 2 * N ≤ E + 2 + s 0 := by
  classical
  set w : ℕ → ℕ := fun m => if N ≤ m then 1 else 0 with hw
  -- pointwise: (i + 1) ≥ 2 - [i = 0] + (N - 1) [N ≤ i], weighted by `s i`
  have key : 2 * Finsupp.weight 1 s + (N - 1) * Finsupp.weight w s ≤
      Finsupp.weight wT s + s 0 := by
    have h0 : s 0 = ∑ i ∈ s.support, if i = 0 then s i else 0 := by
      rw [Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · exact Finsupp.notMem_support_iff.mp h
    rw [h0, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum,
      Finsupp.sum, Finsupp.sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [hw, Pi.one_apply, smul_eq_mul, wT]
    by_cases hi0 : i = 0
    · subst hi0
      have : ¬ N ≤ 0 := by omega
      simp only [this, if_false, if_true, mul_zero]
      nlinarith
    · simp only [hi0, if_false, add_zero]
      split_ifs with hNi
      · have : N - 1 ≤ i - 1 := by omega
        have h3 : (N - 1) * (s i * 1) ≤ s i * (i - 1) := by nlinarith
        have h4 : s i * (i + 1) = 2 * (s i * 1) + s i * (i - 1) := by
          rcases Nat.exists_eq_add_of_le (show 1 ≤ i by omega) with ⟨j, rfl⟩
          simp; ring
        omega
      · have h4 : s i * (i + 1) ≥ 2 * (s i * 1) := by
          have : 2 ≤ i + 1 := by omega
          nlinarith
        omega
  rw [hk, hE] at key
  have : 2 * (N - 1) ≤ (N - 1) * Finsupp.weight w s := by nlinarith
  omega

/-! ### The new slots -/

/-- **The jet-ideal Poincaré lemma for `1 ≤ N`, `E + n + 2 ≤ 2N + 2k`.** -/
theorem jetPoincare_of_T0 {n N k E : ℕ} (hN : 1 ≤ N) (hE : E + n + 2 ≤ 2 * N + 2 * k) :
    JetPoincare n N k E := by
  classical
  intro F hF hder
  set w : ℕ → ℕ := fun m => if N ≤ m then 1 else 0 with hw
  set p : (ℕ →₀ ℕ) → Prop := fun s => 2 ≤ Finsupp.weight w s with hp
  have hFw : IsWeightedHomogeneous wT F E := by
    rw [← pw_tMonW hF]; exact weightedHomogeneousComponent_isWeightedHomogeneous E F
  have hFh : F.IsHomogeneous k := homogeneous_of_tMonW hF
  set G := filt p F with hG
  set H := filt (fun s => ¬ p s) F with hH
  -- the doubly-high part lies in `T_0ⁿ · ℂ[T]`
  have hGspan : G ∈ Ideal.span {(X 0 : TPoly) ^ n} := by
    rw [X_pow_eq_monomial, ← Set.image_singleton (f := fun s => monomial s (1 : ℂ)),
      mem_ideal_span_monomial_image]
    intro s hs
    obtain ⟨hps, hsF⟩ := mem_support_filt hs
    refine ⟨Finsupp.single 0 n, Set.mem_singleton _, ?_⟩
    have hk : Finsupp.weight 1 s = k := by
      have := hFh (mem_support_iff.mp hsF); simpa [Finsupp.degree_eq_weight_one] using this
    have hE' : Finsupp.weight wT s = E := hFw (mem_support_iff.mp hsF)
    have := s0_ge hN s hk hE' hps
    intro i
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · exact Nat.zero_le _
  have hGJ : G ∈ jetIdealT n :=
    (Ideal.span_singleton_le_iff_mem _).mpr (X0_pow_mem n) hGspan
  have hsplit : G + H = F := filt_add_filt_not p F
  have hHT : H ∈ tMonW TPoly MvPolynomial.X k (E : ℤ) :=
    mem_tMonW_of_isWH (filt_isHomogeneous hFh) (filt_isWH hFw)
  have hHder : ∀ M, N ≤ M → pderiv M H ∈ jetIdealT n := by
    intro M hM
    have : H = F - G := by rw [← hsplit]; ring
    rw [this, map_sub]
    exact sub_mem (hder M hM) (pderiv_mem_of_mem_span (by omega) hGspan)
  have hHone : ∀ s ∈ H.support, Finsupp.weight w s ≤ 1 := by
    intro s hs
    have := (mem_support_filt hs).1
    simp only [hp] at this
    omega
  have hmk : Ideal.Quotient.mk (jetIdealT n) F = Ideal.Quotient.mk (jetIdealT n) H := by
    rw [Ideal.Quotient.eq, ← hsplit, add_sub_cancel_right]; exact hGJ
  rw [hmk]
  exact mk_mem_boxW_of_atMostOne hHT hHder hHone

/-- **The remaining input**: the slots `N ≥ 2`, `k ≥ n + 2`, `2N + k ≤ E` that are not covered by
`jetPoincare_of_T0`, i.e. with `2N + 2k < E + n + 2`. -/
def JetPoincareCoreT0 (n : ℕ) : Prop :=
  ∀ N k E : ℕ, 2 ≤ N → n + 2 ≤ k → 2 * N + k ≤ E → 2 * N + 2 * k < E + n + 2 →
    JetPoincare n N k E

/-- The core input follows from the smaller one. -/
theorem jetPoincareCore_of_T0 {n : ℕ} (h : JetPoincareCoreT0 n) : JetPoincareCore n := by
  intro N k E hN hk hE
  rcases Nat.lt_or_ge (2 * N + 2 * k) (E + n + 2) with hlt | hge
  · exact h N k E hN hk hE hlt
  · exact jetPoincare_of_T0 (by omega) hge

end PoincareZero

open PoincareZero HighEndpoint

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional only on `hA`,
detection `det` and the jet-ideal Poincaré lemma in the slots `N ≥ 2`, `k ≥ n + 2`,
`2N + k ≤ E`, `2N + 2k < E + n + 2` (`JetPoincareCoreT0 n`). -/
theorem twoSeries_gradedUnitary_of_strictModel_jetPoincareCoreT0 (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (h : JetPoincareCoreT0 n) :
    VirGradedUnitarity.VirGradedUnitary (twoSeriesLevels n).c
      (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_jetPoincareCore n hn hA det (jetPoincareCore_of_T0 h)

end

end VOA.TwoSeries.StrictModel
