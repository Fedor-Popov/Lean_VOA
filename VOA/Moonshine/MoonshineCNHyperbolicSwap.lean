import VOA.Moonshine.MoonshineCNHyperbolicLightCone

/-! # Exchanging the two light-cone coordinates -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

def hypSwapPolynomial : hypFock ≃ₐ[ℂ] hypFock := renameEquiv ℂ hypSwapVariable

@[simp] theorem hypSwapPolynomial_X (v : ℕ × Fin 2) :
    hypSwapPolynomial (X v) = X (v.1, v.2.rev) := by
  simp [hypSwapPolynomial, hypSwapVariable]
  rfl

theorem hypSwapPolynomial_involutive (p : hypFock) :
    hypSwapPolynomial (hypSwapPolynomial p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [hypSwapPolynomial]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

theorem hypSwapPolynomial_raising (n : ℕ) (p : hypFock) :
    hypSwapPolynomial (hypRaisingDerivation n p) =
      hypRaisingDerivation n (hypSwapPolynomial p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [hypSwapPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add,
      hypRaisingDerivation_X, map_smul, hypSwapPolynomial_X, hp]

theorem hypSwapPolynomial_negativePotential (κ ell : ℂ) (j : ℕ) :
    hypSwapPolynomial (hypNegativePotential κ ell j) = hypNegativePotential ell κ j := by
  have hs : (∑ k ∈ Finset.range j, X (j - 1 - k, 1) * X (k, 0) : hypFock) =
      ∑ k ∈ Finset.range j, X (j - 1 - k, 0) * X (k, 1) := by
    calc
      _ = ∑ k ∈ Finset.range j, X (k, 0) * X (j - 1 - k, 1) := by
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
      _ = ∑ k ∈ Finset.range j,
          X (j - 1 - k, 0) * X (j - 1 - (j - 1 - k), 1) :=
        (Finset.sum_range_reflect (fun k => (X (k, 0) * X (j - 1 - k, 1) : hypFock)) j).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show j - 1 - (j - 1 - k) = k by have := Finset.mem_range.mp hk; omega]
  simp only [hypNegativePotential, map_add, map_smul, map_sum, map_mul,
    hypSwapPolynomial_X, show (0 : Fin 2).rev = 1 by rfl,
    show (1 : Fin 2).rev = 0 by rfl, hs]
  abel

theorem hypSwapPolynomial_negativeMode (κ ell : ℂ) (j : ℕ) (p : hypFock) :
    hypSwapPolynomial (hypSugawara κ ell (-(j + 1 : ℤ)) p) =
      hypSugawara ell κ (-(j + 1 : ℤ)) (hypSwapPolynomial p) := by
  rw [hypSugawara_negative, hypSugawara_negative, map_add, map_mul,
    hypSwapPolynomial_negativePotential, hypSwapPolynomial_raising]

theorem hypSwapPolynomial_oneFamily (a : Fin 2) (p : hypFock)
    (hp : p ∈ hypOneFamily a) : hypSwapPolynomial p ∈ hypOneFamily a.rev := by
  rw [hypOneFamily_eq_range, LinearMap.mem_range] at hp ⊢
  obtain ⟨f, rfl⟩ := hp
  refine ⟨f, ?_⟩
  have he : hypSwapPolynomial.toAlgHom.comp (rename (fun j : ℕ => (j, a))) =
      rename (fun j : ℕ => (j, a.rev)) := by
    ext j
    simp
  exact (AlgHom.congr_fun he f).symm

theorem hypSwapPolynomial_spurious (κ ell : ℂ) (p : hypFock)
    (hp : p ∈ hypNegativeSpurious κ ell) :
    hypSwapPolynomial p ∈ hypNegativeSpurious ell κ := by
  have h : hypNegativeSpurious κ ell ≤
      (hypNegativeSpurious ell κ).comap hypSwapPolynomial.toLinearMap := by
    apply iSup_le
    rintro j _ ⟨q, rfl⟩
    change hypSwapPolynomial (hypSugawara κ ell (-(j + 1 : ℤ)) q) ∈
      hypNegativeSpurious ell κ
    rw [hypSwapPolynomial_negativeMode]
    exact (le_iSup (fun j : ℕ => LinearMap.range (hypSugawara ell κ (-(j + 1 : ℤ)))) j)
      (LinearMap.mem_range_self _ _)
  exact h hp

/-- The complementary light-cone choice when the other momentum is nonzero. -/
theorem hypFock_lightConeSplit_swapped (κ ell : ℂ) (hell : ell ≠ 0) :
    IsCompl (hypNegativeSpurious κ ell) (hypOneFamily 1) := by
  have hbase := hypFock_lightConeSplit ell κ hell
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro p hp
    have hS := hypSwapPolynomial_spurious κ ell p hp.1
    have hK : hypSwapPolynomial p ∈ hypOneFamily 0 := hypSwapPolynomial_oneFamily 1 p hp.2
    have hz : hypSwapPolynomial p = 0 := hbase.disjoint.le_bot ⟨hS, hK⟩
    have he := congrArg hypSwapPolynomial hz
    simpa only [hypSwapPolynomial_involutive, map_zero] using he
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    have hp : hypSwapPolynomial p ∈ hypNegativeSpurious ell κ ⊔ hypOneFamily 0 := by
      rw [hbase.sup_eq_top]
      trivial
    obtain ⟨s, hs, k, hk, he⟩ := Submodule.mem_sup.mp hp
    have he' := congrArg hypSwapPolynomial he
    rw [map_add, hypSwapPolynomial_involutive] at he'
    exact Submodule.mem_sup.mpr ⟨_, hypSwapPolynomial_spurious ell κ s hs,
      _, hypSwapPolynomial_oneFamily 0 k hk, he'⟩

/-- Every nonzero momentum has a concrete choice of longitudinal common kernel. -/
theorem hypFock_lightConeSplit_nonzero (κ ell : ℂ) (h : κ ≠ 0 ∨ ell ≠ 0) :
    ∃ a : Fin 2, IsCompl (hypNegativeSpurious κ ell)
      (⨅ j : ℕ, LinearMap.ker (hypOscillator a (if a = 0 then κ else ell) (j + 1 : ℤ))) := by
  rcases h with hκ | hell
  · refine ⟨0, ?_⟩
    rw [← hypOneFamily_eq_commonKernel]
    exact hypFock_lightConeSplit κ ell hκ
  · refine ⟨1, ?_⟩
    rw [← hypOneFamily_eq_commonKernel]
    exact hypFock_lightConeSplit_swapped κ ell hell

end VOA.Moonshine.ConwayNorton
