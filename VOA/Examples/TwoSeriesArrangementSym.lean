/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesJetPoincareTwoEndpoint

/-!
# The arrangement input, narrowed to what the endpoint actually uses

`JetPoincareArr.jetPoincare_of_arrangement` consumes `ArrangementInclusion n` only through the
dual polynomial `f` it builds from a functional `ψ`, and that `f` is

* **symmetric** (it is built from `ψ` on multisets),
* **homogeneous** of degree `d = E - k` (a sum over exponent vectors of total degree `d`),

and the endpoint `twoSeries_gradedUnitary_of_affine` only needs the slots of
`PoincareZero.JetPoincareCoreT0 n`: `2 ≤ N`, `n + 2 ≤ k`, `2N + k ≤ E`, `2N + 2k < E + n + 2`,
i.e. `2N ≤ d` and `2N + k < d + n + 2`.  This file isolates exactly that much:

* `SymArrangementInclusion n` — the arrangement inclusion for **symmetric, homogeneous** `f` of
  degree `d` in the window `2 ≤ N`, `n + 2 ≤ k`, `2N ≤ d`, `2N + k < d + n + 2`;
* `symArrangementInclusion_of_arrangementInclusion` — it is implied by `ArrangementInclusion n`
  (so it is a strictly weaker named input);
* `symArrangementInclusion_two` — it holds for `n = 2`;
* `jetPoincare_of_symArrangement` — **`SymArrangementInclusion n → JetPoincare n N k E`** in
  every slot of the window (the duality argument of `jetPoincare_of_arrangement`, re-run with the
  narrowed hypothesis);
* `jetPoincareCoreT0_of_symArrangement` — hence `JetPoincareCoreT0 n`;
* `twoSeries_gradedUnitary_of_affine_symArrangement` — **affine GU ⇒ GU of `M(2, 2m+5)`**,
  conditional only on `hA` and `SymArrangementInclusion (m + 1)`.

Everything is proved outright.  `SymArrangementInclusion n` is the named input; it
is proved for every `n ≥ 1`: `GenIncl.symArrangementInclusion` (`TwoSeriesGenIncl.lean`).
-/

namespace VOA.TwoSeries.ArrangementSym

open MvPolynomial Finset JetPoincareVdm JetPoincareDual JetPoincareTwo JetPoincareArr StrictModel
  HighJet LiftDegN

noncomputable section

/-- **The narrowed arrangement inclusion**: `ArrangementInclusion n` restricted to symmetric,
homogeneous `f` of degree `d`, in the window used by `JetPoincareCoreT0 n`. -/
def SymArrangementInclusion (n : ℕ) : Prop :=
  ∀ (N k d : ℕ), 2 ≤ N → n + 2 ≤ k → 2 * N ≤ d → 2 * N + k < d + n + 2 →
    ∀ f : XP k, f.IsHomogeneous d → (∀ σ : Equiv.Perm (Fin k), rename σ f = f) →
      f ∈ Lid k N → (∀ S : Finset (Fin k), #S = n → VanishOn S f) → f ∈ Wn k N n

/-- The narrowed input is implied by the full one. -/
theorem symArrangementInclusion_of_arrangementInclusion {n : ℕ} (h : ArrangementInclusion n) :
    SymArrangementInclusion n :=
  fun _ k _ _ _ _ _ f _ hσ hL hV => h k _ f hσ hL hV

/-- The narrowed input holds for `n = 2`. -/
theorem symArrangementInclusion_two : SymArrangementInclusion 2 :=
  symArrangementInclusion_of_arrangementInclusion arrangementInclusion_two

/-- **The jet-ideal Poincaré lemma from the narrowed arrangement inclusion**, in every slot of
the window of `JetPoincareCoreT0 n`. -/
theorem jetPoincare_of_symArrangement {n : ℕ} (hn : 1 ≤ n) (hA : SymArrangementInclusion n)
    {N k E : ℕ} (hN : 2 ≤ N) (hk : n + 2 ≤ k) (hE : 2 * N + k ≤ E)
    (hE' : 2 * N + 2 * k < E + n + 2) : JetPoincare n N k E := by
  classical
  intro F hF hder
  have hFh : F.IsHomogeneous k := homogeneous_of_tMonW hF
  have hFw : IsWeightedHomogeneous wT F E := by
    rw [← pw_tMonW hF]; exact weightedHomogeneousComponent_isWeightedHomogeneous E F
  set U : Submodule ℂ TPoly := (jetIdealT n).restrictScalars ℂ ⊔ boxSpan N k E with hUdef
  suffices hU : F ∈ U by
    obtain ⟨j, hj, P, hP, rfl⟩ := Submodule.mem_sup.mp hU
    have hjm : Ideal.Quotient.mk (jetIdealT n) (j + P) = Ideal.Quotient.mk (jetIdealT n) P := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add]
    rw [hjm]
    exact mk_mem_boxW_of_mem_boxSpan hP
  by_contra hFU
  obtain ⟨ψ, hψF, hUψ⟩ := Submodule.exists_le_ker_of_notMem hFU
  have hψJ : ∀ G ∈ jetIdealT n, ψ G = 0 := fun G hG =>
    hUψ (Submodule.mem_sup_left (by simpa using hG))
  have hψB : ∀ G ∈ boxSpan N k E, ψ G = 0 := fun G hG => hUψ (Submodule.mem_sup_right hG)
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
  -- `f` is homogeneous of degree `d`
  have hC0 : f.IsHomogeneous d := by
    rw [hfdef]
    refine IsHomogeneous.sum _ _ _ fun e he => isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_sum]
    exact mem_Ek.mp he
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
  -- `f` vanishes on the `n`-fold diagonals
  have hC4 : ∀ S : Finset (Fin k), #S = n → VanishOn S f := by
    intro S hS s₀ hs₀
    set τ := S.orderEmbOfFin hS with hτdef
    have hτ : Function.Injective τ := τ.injective
    have himS : univ.image τ = S := Finset.image_orderEmbOfFin_univ S hS
    ext c
    rw [coeff_zero]
    by_cases hc : ∃ i ∈ S, i ≠ s₀ ∧ c i ≠ 0
    · obtain ⟨i, hiS, his, hci⟩ := hc
      by_contra hc0
      have hfree : i ∉ (rename (collapseTo s₀ S) f).vars := fun h => by
        obtain ⟨i', -, hi'⟩ := mem_image.mp (vars_rename _ _ h)
        unfold collapseTo at hi'
        split_ifs at hi' with h'
        · exact his hi'.symm
        · exact h' (hi' ▸ hiS)
      exact hci (coeff_eq_zero_of_not_mem_vars hfree (mem_support_iff.mpr hc0))
    push Not at hc
    set j := c s₀ with hj
    set e' := c - Finsupp.single s₀ j with he'def
    have he' : ∀ i ∈ univ.image τ, e' i = 0 := by
      intro i hi
      rw [himS] at hi
      by_cases his : i = s₀
      · subst his; simp [he'def, hj]
      · simp [he'def, Ne.symm his, hc i hi his]
    have hce : c = e' + Finsupp.single s₀ j := by
      ext i
      by_cases his : i = s₀
      · subst his; simp [he'def, hj]
      · simp [he'def, Ne.symm his]
    have hfib := coeff_rename_collapse hτ (himS ▸ hs₀) he' j f
    rw [himS] at hfib
    rw [hce, hfib]
    simp only [hcoeff]
    by_cases hdeg : e'.degree + j = d
    · have hin : ∀ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j, e' + l.mapDomain τ ∈ Ek k d := by
        intro l hl
        rw [mem_finsuppAntidiag] at hl
        have hdl : l.degree = j := by rw [Finsupp.degree_eq_sum]; exact hl.1
        rw [mem_Ek, ← Finsupp.degree_eq_sum, map_add, degree_mapDomain, hdl, hdeg]
      rw [sum_congr rfl fun l hl => if_pos (hin l hl), ← sum_div, ← map_sum]
      have hmon : ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) j,
          (monomial (toMS univ (e' + l.mapDomain τ)) (1 : ℂ) : TPoly) =
          monomial (toMS (univ \ univ.image τ) e') 1 * jg n j := by
        rw [jg_eq_sum, mul_sum]
        exact sum_congr rfl fun l _ => by rw [toMS_split hτ he', monomial_add_sum_single]
      rw [hmon, hψJ _ (Ideal.mul_mem_left _ _ (jg_mem n j)), zero_div]
    · refine sum_eq_zero fun l hl => ?_
      rw [if_neg]
      rw [mem_finsuppAntidiag] at hl
      have hdl : l.degree = j := by rw [Finsupp.degree_eq_sum]; exact hl.1
      rw [mem_Ek, ← Finsupp.degree_eq_sum, map_add, degree_mapDomain, hdl]
      exact hdeg
  -- `f` is symmetric
  have hC5 : ∀ σ : Equiv.Perm (Fin k), rename σ f = f := by
    intro σ
    ext e
    obtain ⟨e₁, rfl⟩ : ∃ e₁ : Fin k →₀ ℕ, e = e₁.mapDomain σ :=
      ⟨e.mapDomain σ.symm, by rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm,
        Finsupp.mapDomain_id]⟩
    have hEk' : e₁.mapDomain σ ∈ Ek k d ↔ e₁ ∈ Ek k d := by
      rw [mem_Ek, mem_Ek, ← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, degree_mapDomain]
    have htoMS : toMS univ (e₁.mapDomain σ) = toMS univ e₁ := by
      rw [toMS, toMS, ← Equiv.sum_comp σ]
      exact sum_congr rfl fun i _ => by rw [Finsupp.mapDomain_apply σ.injective]
    rw [coeff_rename_mapDomain _ σ.injective, hcoeff, hcoeff, htoMS]
    simp only [hEk']
  exact hψF (hC2 ▸ dot_pol_Wn hn hder
    (hA N k d hN hk (by omega) (by omega) f hC0 hC5 hC3 hC4))

/-- The core input of the endpoint from the narrowed arrangement inclusion. -/
theorem jetPoincareCoreT0_of_symArrangement {n : ℕ} (hn : 1 ≤ n)
    (hA : SymArrangementInclusion n) : PoincareZero.JetPoincareCoreT0 n :=
  fun _ _ _ hN hk hE hE' => jetPoincare_of_symArrangement hn hA hN hk hE hE'

end

end VOA.TwoSeries.ArrangementSym

namespace VOA.TwoSeries.JetPoincareTwo

open VOA.GradedUnitaryCohomology VirGradedUnitarity VOA.TwoSeries.StrictModel
open VOA.AffineVOA VOA.AffineVOA.SugawaraCov VOA.AffineVOA.Strong
open VOA.VirModule VOA.TwoSeries.DSSlice VOA.VirSimple VOA.LeeYangCharacter
open VOA.SymbolModel VOA.AffineVOA.Inst Sl2CosetConcrete VOA.AffineSl2BoundaryMaximalIdeal

/-- **Affine GU ⇒ GU of `M(2, 2m+5)`**, conditional only on `hA` and the narrowed arrangement
inclusion `SymArrangementInclusion (m + 1)` (symmetric homogeneous `f`, window of
`JetPoincareCoreT0`). -/
theorem twoSeries_gradedUnitary_of_affine_symArrangement (m : ℕ)
    (hA : GradedUnitary (affineForm (twoSeriesLevels (m + 1)))
      (affineRealStructure (twoSeriesLevels (m + 1))) (affineFlag (twoSeriesLevels (m + 1))))
    (hSym : ArrangementSym.SymArrangementInclusion (m + 1)) :
    VirGradedUnitary (twoSeriesLevels (m + 1)).c (targetRealStructure (twoSeriesLevels (m + 1))) :=
  SliceMap.twoSeries_gradedUnitary_of_affine m hA
    (ArrangementSym.jetPoincareCoreT0_of_symArrangement (by omega) hSym)

end VOA.TwoSeries.JetPoincareTwo
