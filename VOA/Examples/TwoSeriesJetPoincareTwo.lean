/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesJetPoincareDual
import VOA.Examples.TwoSeriesPoincareZero

/-!
# The jet-ideal Poincaré lemma for `n = 2`

`jetPoincare_two` — **`JetPoincare 2 N k E` for all `N`, `k`, `E`**, and hence
`jetPoincareCoreT0_two` — `JetPoincareCoreT0 2`.

Proof (duality).  Let `U = J_2 + span{T-monomials of degree k, weight E in T_0, …, T_{N-1}}`.  If
`F ∉ U`, a linear functional `ψ` vanishes on `U` but not on `F`.  Put
`f = Σ_e ψ(T^{e}) x^e / k!` (sum over exponent vectors `e` of `k` points with `Σ e_i = E - k`,
`T^e = ∏_i T_{e_i}`).  Then

* `ψ(G) = ⟨pol(G), f⟩` for every `G` of degree `k` and weight `E` (`pol` the polarization);
* `f ∈ L = (x_i^N)` because `ψ` kills the monomials in `T_0, …, T_{N-1}`;
* `f` is divisible by every `x_b - x_a` because `ψ` kills `J_2`: the coefficients of
  `f|_{x_b = x_a}` are values of `ψ` on `(T²)_j T^μ`;
* hence `f ∈ W` (`JetPoincareVdm.mem_Wid_of_mem_Lid`), and `⟨pol(F), W⟩ = 0` when
  `∂F/∂T_M ∈ J_2` for `M ≥ N` (`JetPoincareDual.dot_pol_W`) — contradicting `ψ(F) ≠ 0`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.JetPoincareTwo

open MvPolynomial Finset JetPoincareVdm JetPoincareDual StrictModel HighJet LiftDegN

noncomputable section

/-! ### Exponent vectors and multisets -/

theorem weight_toMS {k : ℕ} (w : ℕ → ℕ) (B : Finset (Fin k)) (e : Fin k →₀ ℕ) :
    Finsupp.weight w (toMS B e) = ∑ i ∈ B, w (e i) := by
  rw [toMS, map_sum]
  exact sum_congr rfl fun i _ => by rw [Finsupp.weight_single, one_smul]

theorem degree_toMS {k : ℕ} (B : Finset (Fin k)) (e : Fin k →₀ ℕ) :
    (toMS B e).degree = #B := by
  rw [toMS, map_sum]
  simp [Finsupp.degree_single]

theorem mem_support_toMS {k : ℕ} {B : Finset (Fin k)} {e : Fin k →₀ ℕ} {m : ℕ}
    (hm : m ∈ (toMS B e).support) : ∃ i ∈ B, e i = m := by
  classical
  obtain ⟨i, hi, hm'⟩ := mem_biUnion.mp (Finsupp.support_finsetSum hm)
  refine ⟨i, hi, ?_⟩
  have := Finsupp.support_single_subset hm'
  rw [mem_singleton] at this
  exact this.symm

/-- The exponent vectors of `k` points with exponent sum `d`. -/
def Ek (k d : ℕ) : Finset (Fin k →₀ ℕ) :=
  (Finset.Nat.antidiagonalTuple k d).map
    ⟨Finsupp.equivFunOnFinite.symm, Finsupp.equivFunOnFinite.symm.injective⟩

theorem mem_Ek {k d : ℕ} {e : Fin k →₀ ℕ} : e ∈ Ek k d ↔ ∑ i, e i = d := by
  rw [Ek, mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.Nat.mem_antidiagonalTuple] at hx
    simpa using hx
  · intro h
    refine ⟨Finsupp.equivFunOnFinite e, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa using h

theorem mem_Lid_of {k N : ℕ} {f : XP k} (h : ∀ e ∈ f.support, ∃ i, N ≤ e i) : f ∈ Lid k N := by
  have hL : Lid k N = Ideal.span ((fun s => monomial s (1 : ℂ)) ''
      Set.range fun i : Fin k => Finsupp.single i N) := by
    rw [Lid, ← Set.range_comp]
    congr 1
    ext x
    simp [X_pow_eq_monomial]
  rw [hL, mem_ideal_span_monomial_image]
  intro e he
  obtain ⟨i, hi⟩ := h e he
  refine ⟨Finsupp.single i N, ⟨i, rfl⟩, fun j => ?_⟩
  rw [Finsupp.single_apply]
  split_ifs with hij
  · subst hij; exact hi
  · exact Nat.zero_le _

theorem weight_wT_toMS {k : ℕ} (e : Fin k →₀ ℕ) :
    Finsupp.weight wT (toMS univ e) = e.degree + k := by
  rw [weight_toMS, Finsupp.degree_eq_sum, sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-! ### The box span -/

/-- The span of the `T`-monomials of degree `k`, weight `E` in `T_0, …, T_{N-1}`. -/
def boxSpan (N k E : ℕ) : Submodule ℂ TPoly :=
  Submodule.span ℂ {P | ∃ s : ℕ →₀ ℕ, P = monomial s 1 ∧ s.degree = k ∧
    Finsupp.weight wT s = E ∧ ∀ m ∈ s.support, m < N}

theorem mk_mem_boxW_of_mem_boxSpan {n N k E : ℕ} {P : TPoly} (hP : P ∈ boxSpan N k E) :
    Ideal.Quotient.mk (jetIdealT n) P ∈ boxW (tn n) N k (E : ℤ) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨s, rfl, hk, hE, hN⟩ := hP
    exact mk_mem_boxW_of_vars (monomial_mem_tMonW s 1 hk hE)
      (by rw [vars_monomial one_ne_zero]; exact hN)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ => rw [map_add]; exact add_mem hP hQ
  | smul c P _ hP =>
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul, Ideal.Quotient.mkₐ_eq_mk]
    exact Submodule.smul_mem _ c hP

/-! ### The main theorem -/

/-- **The jet-ideal Poincaré lemma for `n = 2`**, in every slot `(N, k, E)`. -/
theorem jetPoincare_two (N k E : ℕ) : JetPoincare 2 N k E := by
  classical
  intro F hF hder
  have hFh : F.IsHomogeneous k := homogeneous_of_tMonW hF
  have hFw : IsWeightedHomogeneous wT F E := by
    rw [← pw_tMonW hF]; exact weightedHomogeneousComponent_isWeightedHomogeneous E F
  set U : Submodule ℂ TPoly := (jetIdealT 2).restrictScalars ℂ ⊔ boxSpan N k E with hUdef
  suffices hU : F ∈ U by
    obtain ⟨j, hj, P, hP, rfl⟩ := Submodule.mem_sup.mp hU
    have hjm : Ideal.Quotient.mk (jetIdealT 2) (j + P) = Ideal.Quotient.mk (jetIdealT 2) P := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add]
    rw [hjm]
    exact mk_mem_boxW_of_mem_boxSpan hP
  by_contra hFU
  obtain ⟨ψ, hψF, hUψ⟩ := Submodule.exists_le_ker_of_notMem hFU
  have hψJ : ∀ G ∈ jetIdealT 2, ψ G = 0 := fun G hG =>
    hUψ (Submodule.mem_sup_left (by simpa using hG))
  have hψB : ∀ G ∈ boxSpan N k E, ψ G = 0 := fun G hG => hUψ (Submodule.mem_sup_right hG)
  rcases Nat.lt_or_ge E k with hEk | hEk
  · exact hψF (by rw [HighDegSucc.eq_zero_of_wt_lt hFh hFw hEk, map_zero])
  set d := E - k with hd
  set f : XP k := ∑ e ∈ Ek k d,
    monomial e (ψ (monomial (toMS univ e) 1) / (k.factorial : ℂ)) with hfdef
  have hcoeff : ∀ e, coeff e f =
      if e ∈ Ek k d then ψ (monomial (toMS univ e) 1) / (k.factorial : ℂ) else 0 := by
    intro e
    rw [hfdef, coeff_sum]
    simp only [coeff_monomial]
    rw [sum_ite_eq']
  have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  -- `ψ = ⟨pol(·), f⟩` on the monomials of `F`
  have hC1 : ∀ s ∈ F.support, dot (pol univ (monomial s 1)) f = ψ (monomial s 1) := by
    intro s hs
    have hsk : s.degree = k := by
      have := hFh (mem_support_iff.mp hs)
      rwa [Finsupp.degree_eq_weight_one]
    have hsE : Finsupp.weight wT s = E := hFw (mem_support_iff.mp hs)
    rw [hfdef, dot_sum_right]
    simp only [dot_monomial_right]
    have h1 : ∀ e ∈ Ek k d, coeff e (pol univ (monomial s 1)) *
        (ψ (monomial (toMS univ e) 1) / (k.factorial : ℂ)) =
        coeff e (pol univ (monomial s 1)) * (ψ (monomial s 1) / (k.factorial : ℂ)) := by
      intro e _
      by_cases he : e ∈ (pol univ (monomial s 1)).support
      · rw [pol_monomial_support s univ e he]
      · rw [notMem_support_iff.mp he, zero_mul, zero_mul]
    rw [sum_congr rfl h1, ← sum_mul]
    have hsub : (pol univ (monomial s 1)).support ⊆ Ek k d := by
      intro e he
      have h2 := pol_monomial_support s univ e he
      have h3 := weight_wT_toMS e
      rw [h2, hsE] at h3
      rw [mem_Ek, ← Finsupp.degree_eq_sum, hd]
      omega
    have hsum : ∑ e ∈ Ek k d, coeff e (pol univ (monomial s 1)) = (k.factorial : ℂ) := by
      rw [← sum_subset hsub (fun e _ he => notMem_support_iff.mp he)]
      have := pol_monomial_eval (k := k) s univ
      rw [card_univ, Fintype.card_fin, if_pos hsk, eval_eq] at this
      rw [← this]
      exact sum_congr rfl fun e _ => by simp
    rw [hsum, mul_div_cancel₀ _ hk0]
  have hC2 : dot (pol univ F) f = ψ F := by
    conv_rhs => rw [as_sum F]
    conv_lhs => rw [as_sum F]
    rw [pol_sum, dot_sum_left, map_sum]
    refine sum_congr rfl fun s hs => ?_
    have hmon : (monomial s (coeff s F) : TPoly) = coeff s F • monomial s 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, pol_smul, dot_smul_left, hC1 s hs, map_smul, smul_eq_mul]
  -- `f ∈ L`
  have hC3 : f ∈ Lid k N := by
    refine mem_Lid_of fun e he => ?_
    rw [mem_support_iff, hcoeff] at he
    split_ifs at he with hE
    · by_contra hlow
      push Not at hlow
      refine he ?_
      rw [hψB _ (Submodule.subset_span ⟨toMS univ e, rfl, ?_, ?_, ?_⟩), zero_div]
      · rw [degree_toMS, card_univ, Fintype.card_fin]
      · rw [weight_wT_toMS, Finsupp.degree_eq_sum, mem_Ek.mp hE]; omega
      · intro m hm
        obtain ⟨i, _, rfl⟩ := mem_support_toMS hm
        exact hlow i
    · exact absurd rfl he
  -- `f` is divisible by every `x_b - x_a`
  have hC4 : ∀ a b : Fin k, a < b → (X b - X a : XP k) ∣ f := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    apply dvd_of_rename_subst_eq_zero
    set σf := rename (JetPoincareVdm.subst a b) f with hσ
    obtain ⟨u, hu⟩ := dvd_sub_rename a b f
    have hfree : b ∉ σf.vars := by
      intro hb
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (vars_rename _ _ hb)
      unfold JetPoincareVdm.subst at hi
      split_ifs at hi with h
      · exact hne hi
      · exact h hi
    ext c
    rw [coeff_zero]
    by_cases hcb : c b = 0
    swap
    · by_contra hc
      exact hcb (coeff_eq_zero_of_not_mem_vars hfree (mem_support_iff.mpr hc))
    set j := c a with hj
    set cb := c - Finsupp.single a j with hcbdef
    have hca : cb a = 0 := by simp [hcbdef, hj]
    have hcbb : cb b = 0 := by simp [hcbdef, hne, hcb]
    have hcoth : ∀ i, i ≠ a → cb i = c i := fun i hi => by
      simp [hcbdef, Ne.symm hi]
    have hex : ∀ p q : ℕ, ∀ i, (Finsupp.single a p + Finsupp.single b q + cb) i =
        if i = a then p else if i = b then q else c i := by
      intro p q i
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      by_cases hia : i = a
      · have hib : i ≠ b := hia ▸ hne
        rw [if_pos hia.symm, if_neg (fun h => hib h.symm), if_pos hia, hia, hca]; simp
      · by_cases hib : i = b
        · rw [if_neg (fun h => hia h.symm), if_pos hib.symm, if_neg hia, if_pos hib, hib, hcbb]
          simp
        · rw [if_neg (fun h => hia h.symm), if_neg (fun h => hib h.symm), if_neg hia, if_neg hib,
            hcoth i hia]
          simp
    have hc : Finsupp.single a j + Finsupp.single b 0 + cb = c := by
      ext i
      rw [hex]
      split_ifs with h1 h2
      · subst h1; rfl
      · subst h2; exact hcb.symm
      · rfl
    set Z : XP k := hsum a b j * monomial cb 1 with hZdef
    have hZ : Z = ∑ x ∈ antidiagonal j,
        monomial (Finsupp.single a x.1 + Finsupp.single b x.2 + cb) (1 : ℂ) := by
      rw [hZdef, hsum, sum_mul]
      exact sum_congr rfl fun x _ => by rw [monomial_mul, one_mul]
    have hPa : a ∉ (monomial cb (1 : ℂ)).vars := by
      rw [vars_monomial one_ne_zero, Finsupp.mem_support_iff, not_not]; exact hca
    have hPb : b ∉ (monomial cb (1 : ℂ)).vars := by
      rw [vars_monomial one_ne_zero, Finsupp.mem_support_iff, not_not]; exact hcbb
    have h1 : dot σf Z = coeff c σf := by
      rw [hZ, dot_sum_right]
      simp only [dot_monomial_right, mul_one]
      rw [sum_eq_single (j, 0)]
      · rw [hc]
      · intro x hx hxne
        rw [mem_antidiagonal] at hx
        have hx2 : x.2 ≠ 0 := by
          intro h0
          exact hxne (Prod.ext (by simp only at hx ⊢; omega) h0)
        by_contra hc0
        have := coeff_eq_zero_of_not_mem_vars hfree (mem_support_iff.mpr hc0)
        rw [hex, if_neg (Ne.symm hne), if_pos rfl] at this
        exact hx2 this
      · intro h; exact absurd (mem_antidiagonal.mpr (by simp)) h
    have h2 : dot ((X b - X a) * u) Z = 0 := by
      rw [dot_comm, hZdef]; exact dot_key hne j hPa hPb u
    have hdegx : ∀ x ∈ antidiagonal j,
        (Finsupp.single a x.1 + Finsupp.single b x.2 + cb).degree = c.degree := by
      intro x hx
      rw [mem_antidiagonal] at hx
      rw [← hc, map_add, map_add, map_add, map_add, Finsupp.degree_single, Finsupp.degree_single,
        Finsupp.degree_single, Finsupp.degree_single]
      omega
    -- the multiset of an arrangement
    set μ : ℕ →₀ ℕ := ∑ i ∈ (univ.erase a).erase b, Finsupp.single (cb i) 1 with hμ
    have htoMS : ∀ p q : ℕ, toMS univ (Finsupp.single a p + Finsupp.single b q + cb) =
        Finsupp.single p 1 + (Finsupp.single q 1 + μ) := by
      intro p q
      rw [toMS, ← add_sum_erase _ _ (mem_univ a),
        ← add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hne, mem_univ b⟩), hex, if_pos rfl, hex,
        if_neg (Ne.symm hne), if_pos rfl, hμ]
      congr 2
      refine sum_congr rfl fun i hi => ?_
      have hib : i ≠ b := ne_of_mem_erase hi
      have hia : i ≠ a := ne_of_mem_erase (mem_of_mem_erase hi)
      rw [hex, if_neg hia, if_neg hib, hcoth i hia]
    have h3 : dot f Z = 0 := by
      rw [hZ, dot_sum_right]
      simp only [dot_monomial_right, mul_one, hcoeff]
      by_cases hcd : c.degree = d
      · have hin : ∀ x ∈ antidiagonal j,
            Finsupp.single a x.1 + Finsupp.single b x.2 + cb ∈ Ek k d := by
          intro x hx
          rw [mem_Ek, ← Finsupp.degree_eq_sum, hdegx x hx, hcd]
        rw [sum_congr rfl fun x hx => if_pos (hin x hx), ← sum_div, ← map_sum]
        have hmon : ∑ x ∈ antidiagonal j, (monomial (toMS univ
            (Finsupp.single a x.1 + Finsupp.single b x.2 + cb)) (1 : ℂ) : TPoly) =
            jg 2 j * monomial μ 1 := by
          rw [JetPoincareDual.jg_two, sum_mul]
          refine sum_congr rfl fun x _ => ?_
          rw [htoMS, mul_assoc, X, X, monomial_mul, monomial_mul, one_mul, one_mul]
        rw [hmon, hψJ _ (Ideal.mul_mem_right _ _ (jg_mem 2 j)), zero_div]
      · refine sum_eq_zero fun x hx => ?_
        rw [if_neg]
        rw [mem_Ek, ← Finsupp.degree_eq_sum, hdegx x hx]
        exact hcd
    have hf : f = (X b - X a) * u + σf := by rw [← hu]; ring
    have h4 := h3
    rw [hf, dot_add_left, h2, zero_add, h1] at h4
    exact h4
  exact hψF (hC2 ▸ dot_pol_W hder (mem_Wid_of_mem_Lid hC3 hC4))

/-- **`JetPoincareCoreT0 2`**, unconditionally. -/
theorem jetPoincareCoreT0_two : PoincareZero.JetPoincareCoreT0 2 :=
  fun N k E _ _ _ _ => jetPoincare_two N k E

/-- `JetPoincareCoreT0 1`: `J_1` contains every `T_m`. -/
theorem jetPoincareCoreT0_one : PoincareZero.JetPoincareCoreT0 1 :=
  fun N k E _ hk _ _ => by
    rw [show k = (k - 1) + 1 by omega]
    exact fun F hF _ => by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (HighDegSucc.mem_jetIdealT_one (by omega) hF)]
      exact Submodule.zero_mem _

end

end VOA.TwoSeries.JetPoincareTwo
