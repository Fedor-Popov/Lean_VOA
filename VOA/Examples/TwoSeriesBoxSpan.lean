/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesBoxGrassmann

/-!
# The box image is spanned by the reversed monomials in a smaller box

Combining the truncated-product relations of `R_n` (`Psi_hh_mul_eq_zero`) with the Grassmannian
spanning lemma (`grassmann_span`):

* `boxW_le_span_psiMono` — the box image `boxW (tn n) N k e` is spanned by the reversed
  monomials `psiMono n N β = Π_i T_{N-1-β_i}` with `β_i < N` and `|β| + e = k N`;
* `psiMono_mem_span_box` — every `psiMono n N β` lies in the span of the `psiMono n N γ`
  with **all `γ_i < (n-1) N + 1 - k`** and `|γ| = |β|` (symmetrize, apply the Grassmannian
  lemma with `t = (n-1) N + 1 - k`, take the homogeneous component of degree `|β|`, and kill the
  `h_q`-part with `Psi_hh_mul_eq_zero`);
* `boxW_le_span_small` — hence `boxW (tn n) N k e` is spanned by the `psiMono n N γ` with
  `γ_i < (n-1) N + 1 - k` and `|γ| + e = k N`.

For `n = 2` the bound `γ_i ≤ N - k` is exactly the shape of the Grassmannian basis, and
`TwoSeriesBoxTwo` turns it into `BoxCount 2 r`.  For `n ≥ 3` the bound is weaker than `γ_i < N`
(automatic), so this file gives nothing new there.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

/-! ### The box monomials are reversed monomials -/

theorem list_prod_map_tn (n : ℕ) (l : List ℕ) :
    (l.map (tn n)).prod = ∏ i : Fin l.length, tn n (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

theorem list_sum_map_succ (l : List ℕ) :
    (l.map fun m => m + 1).sum = ∑ i : Fin l.length, (l.get i + 1) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

theorem degree_eq_sum {k : ℕ} (β : Fin k →₀ ℕ) : Finsupp.degree β = ∑ i, β i := by
  rw [Finsupp.degree_apply]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
    simpa using hi

/-- **The box image is spanned by reversed monomials.** -/
theorem boxW_le_span_psiMono (n N k : ℕ) (e : ℤ) :
    boxW (tn n) N k e ≤ Submodule.span ℂ (psiMono n N ''
      {β : Fin k →₀ ℕ | (∀ i, β i < N) ∧ ((Finsupp.degree β : ℕ) : ℤ) + e = k * N}) := by
  rw [boxW, Submodule.span_le]
  rintro _ ⟨l, hl, he, hlN, rfl⟩
  subst hl
  have hlt : ∀ i : Fin l.length, l.get i < N := fun i => hlN _ (List.get_mem l i)
  refine Submodule.subset_span ⟨Finsupp.equivFunOnFinite.symm fun i => N - 1 - l.get i,
    ⟨fun i => ?_, ?_⟩, ?_⟩
  · simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    have := hlt i; omega
  · rw [degree_eq_sum, ← he, list_sum_map_succ]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    have h : ∑ i : Fin l.length, (N - 1 - l.get i) + ∑ i : Fin l.length, (l.get i + 1) =
        l.length * N := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl fun i _ => (show N - 1 - l.get i + (l.get i + 1) = N by
        have := hlt i; omega)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact_mod_cast h
  · rw [psiMono, list_prod_map_tn]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    have := hlt i
    rw [if_pos (by omega)]
    congr 1
    omega

/-! ### Homogeneous components of the ideal part -/

theorem hh_isHomogeneous (m q : ℕ) : (hh m q).IsHomogeneous q := by
  rw [hh_eq]
  refine IsHomogeneous.sum _ _ _ fun α hα => isHomogeneous_monomial _ ?_
  rw [Finset.mem_finsuppAntidiag] at hα
  rw [degree_eq_sum]
  exact hα.1

theorem Psi_homogeneousComponent_hh_mul {n N m : ℕ} (q : ℕ) (hq : (n - 1) * N < q + m)
    (g : MvPolynomial (Fin m) ℂ) (D : ℕ) :
    Psi n N m (homogeneousComponent D (hh m q * g)) = 0 := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
    ((hh_isHomogeneous m q).mul (homogeneousComponent_isHomogeneous i g)))]
  split_ifs
  · exact Psi_hh_mul_eq_zero q hq _
  · exact map_zero _

theorem Psi_homogeneousComponent_jSym {n N m t : ℕ} (ht : (n - 1) * N < t + m)
    {x : MvPolynomial (Fin m) ℂ} (hx : x ∈ jSym m t) (D : ℕ) :
    Psi n N m (homogeneousComponent D x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, g, hq, -, rfl⟩ := hy
    exact Psi_homogeneousComponent_hh_mul q (by omega) g D
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, map_smul, hy, smul_zero]

/-! ### Reduction to the small box -/

theorem OS_isHomogeneous (k : ℕ) (β : Fin k →₀ ℕ) :
    (OS k β).IsHomogeneous (Finsupp.degree β) := by
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [rename_monomial]
  refine isHomogeneous_monomial _ ?_
  rw [degree_eq_sum, degree_eq_sum]
  simp_rw [Finsupp.mapDomain_equiv_apply]
  exact Fintype.sum_equiv σ.symm _ _ fun _ => rfl

theorem Psi_OS (n N k : ℕ) (β : Fin k →₀ ℕ) :
    Psi n N k (OS k β) = ((k.factorial : ℕ) : ℂ) • psiMono n N β := by
  rw [OS, map_sum]
  simp_rw [Psi_rename, Psi_monomial, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul]

/-- **Every reversed monomial lies in the span of reversed monomials in the box
`γ_i < (n-1) N + 1 - k`, of the same degree.** -/
theorem psiMono_mem_span_box (n N k : ℕ) (β : Fin k →₀ ℕ) :
    psiMono n N β ∈ Submodule.span ℂ (psiMono n N ''
      {γ : Fin k →₀ ℕ | (∀ i, γ i < (n - 1) * N + 1 - k) ∧
        Finsupp.degree γ = Finsupp.degree β}) := by
  set t := (n - 1) * N + 1 - k with ht
  obtain ⟨P, -, hPbox, hj⟩ := grassmann_span k t (OS k β) (OS_isSymmetric k β)
  have hD : homogeneousComponent (Finsupp.degree β) (OS k β) = OS k β := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
      (OS_isHomogeneous k β)), if_pos rfl]
  have hsplit : Psi n N k (OS k β) =
      Psi n N k (homogeneousComponent (Finsupp.degree β) P) := by
    conv_lhs => rw [← hD, show OS k β = P + (OS k β - P) by ring]
    rw [map_add, map_add, Psi_homogeneousComponent_jSym (by omega) hj, add_zero]
  have hmem : Psi n N k (homogeneousComponent (Finsupp.degree β) P) ∈
      Submodule.span ℂ (psiMono n N '' {γ : Fin k →₀ ℕ | (∀ i, γ i < t) ∧
        Finsupp.degree γ = Finsupp.degree β}) := by
    rw [homogeneousComponent_apply, map_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    rw [Finset.mem_filter] at hd
    rw [Psi_monomial]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, ⟨?_, hd.2⟩, rfl⟩)
    rw [mem_restrictSupport_iff] at hPbox
    exact hPbox (Finset.mem_coe.mpr hd.1)
  rw [← hsplit, Psi_OS] at hmem
  have hk : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have := Submodule.smul_mem _ (((k.factorial : ℕ) : ℂ)⁻¹) hmem
  rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at this

/-- **The box image is spanned by reversed monomials in the box
`γ_i < (n-1) N + 1 - k`.** -/
theorem boxW_le_span_small (n N k : ℕ) (e : ℤ) :
    boxW (tn n) N k e ≤ Submodule.span ℂ (psiMono n N ''
      {γ : Fin k →₀ ℕ | (∀ i, γ i < (n - 1) * N + 1 - k) ∧
        ((Finsupp.degree γ : ℕ) : ℤ) + e = k * N}) := by
  refine (boxW_le_span_psiMono n N k e).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨β, ⟨-, hβ⟩, rfl⟩
  refine Submodule.span_mono ?_ (psiMono_mem_span_box n N k β)
  rintro _ ⟨γ, ⟨hγ, hdeg⟩, rfl⟩
  exact ⟨γ, ⟨hγ, by rw [hdeg]; exact hβ⟩, rfl⟩

end

end VOA.TwoSeries.StrictModel
