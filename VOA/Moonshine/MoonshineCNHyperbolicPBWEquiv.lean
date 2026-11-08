import VOA.Moonshine.MoonshineCNHyperbolicPBWMap
import Mathlib.Data.Prod.Lex

/-! # Invertibility of the concrete sorted-word map

Injectivity detects a maximal monomial filtration degree. Surjectivity is
double well-founded induction on count and level, using finite support.
Thus no finite-dimensionality or positive-mode Virasoro theorem is needed.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

theorem hypPBWMap_coefficient_at_max (κ ell : ℂ) (p : hypFock)
    (e : (ℕ × Fin 2) →₀ ℕ) (he : e ∈ p.support)
    (hmax : ∀ t ∈ p.support,
      Finsupp.weight hypBCountWeight t < Finsupp.weight hypBCountWeight e ∨
        (Finsupp.weight hypBCountWeight t = Finsupp.weight hypBCountWeight e ∧
          Finsupp.weight hypBLevelWeight t ≤ Finsupp.weight hypBLevelWeight e)) :
    coeff e (hypPBWMap κ ell p) = κ ^ (Finsupp.weight hypBCountWeight e) * coeff e p := by
  classical
  have hterm (t : (ℕ × Fin 2) →₀ ℕ) (ht : t ∈ p.support) :
      coeff e (hypPBWMap κ ell (monomial t (coeff t p))) =
        if t = e then κ ^ (Finsupp.weight hypBCountWeight e) * coeff e p else 0 := by
    have hz : coeff e (hypPBWMap κ ell (monomial t 1) -
        κ ^ (Finsupp.weight hypBCountWeight t) • monomial t 1) = 0 := by
      by_contra hc
      have hlt := (hypBFiltered_mem _ _ _).mp (hypPBWMap_leading κ ell t) e hc
      have hle := hmax t ht
      omega
    rw [coeff_sub, coeff_smul] at hz
    have hm : (monomial t (coeff t p) : hypFock) = coeff t p • monomial t 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, coeff_smul, sub_eq_zero.mp hz]
    by_cases hte : t = e
    · subst t
      simp [mul_comm]
    · simp [hte]
  conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
  rw [Finset.sum_congr rfl hterm]
  simp [he]

/-- The actual sorted-word map is injective at nonzero light-cone momentum. -/
theorem hypPBWMap_injective (κ ell : ℂ) (hκ : κ ≠ 0) :
    Function.Injective (hypPBWMap κ ell) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  by_contra hne
  have hsupport : p.support.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    apply MvPolynomial.ext
    intro e
    have hn : e ∉ p.support := by rw [h]; simp
    simpa using notMem_support_iff.mp hn
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image p.support
    (fun t => toLex (Finsupp.weight hypBCountWeight t, Finsupp.weight hypBLevelWeight t))
    hsupport
  have hm : ∀ t ∈ p.support,
      Finsupp.weight hypBCountWeight t < Finsupp.weight hypBCountWeight e ∨
        (Finsupp.weight hypBCountWeight t = Finsupp.weight hypBCountWeight e ∧
          Finsupp.weight hypBLevelWeight t ≤ Finsupp.weight hypBLevelWeight e) := by
    intro t ht
    exact Prod.Lex.toLex_le_toLex.mp (hmax t ht)
  have hc := hypPBWMap_coefficient_at_max κ ell p e he hm
  rw [hp, coeff_zero] at hc
  exact (mul_ne_zero (pow_ne_zero _ hκ) (mem_support_iff.mp he)) hc.symm

theorem hypPBWMap_monomial_mem_range (κ ell : ℂ) (hκ : κ ≠ 0)
    (e : (ℕ × Fin 2) →₀ ℕ) : monomial e 1 ∈ LinearMap.range (hypPBWMap κ ell) := by
  classical
  suffices h : ∀ d w, ∀ e : (ℕ × Fin 2) →₀ ℕ,
      Finsupp.weight hypBCountWeight e = d → Finsupp.weight hypBLevelWeight e = w →
      monomial e 1 ∈ LinearMap.range (hypPBWMap κ ell) from h _ _ e rfl rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ihd =>
    intro w
    induction w using Nat.strong_induction_on with
    | h w ihw =>
      intro e hed hew
      let r := hypPBWMap κ ell (monomial e 1) - κ ^ d • monomial e 1
      have hr : r ∈ hypBFiltered d w := by
        simpa only [hed, hew] using hypPBWMap_leading κ ell e
      have hrange : r ∈ LinearMap.range (hypPBWMap κ ell) := by
        rw [r.as_sum]
        apply Submodule.sum_mem
        intro t ht
        have hs := (hypBFiltered_mem d w r).mp hr t (mem_support_iff.mp ht)
        have hm : monomial t 1 ∈ LinearMap.range (hypPBWMap κ ell) := by
          rcases hs with hd | ⟨hd, hw⟩
          · exact ihd _ hd _ t rfl rfl
          · exact ihw _ hw t hd rfl
        simpa only [smul_monomial, smul_eq_mul, mul_one] using
          (LinearMap.range (hypPBWMap κ ell)).smul_mem (coeff t r) hm
      have hs := (LinearMap.range (hypPBWMap κ ell)).sub_mem
        (LinearMap.mem_range_self _ (monomial e 1)) hrange
      have hs' : κ ^ d • monomial e 1 ∈ LinearMap.range (hypPBWMap κ ell) := by
        simpa only [r, sub_sub_cancel] using hs
      have hi := (LinearMap.range (hypPBWMap κ ell)).smul_mem (κ ^ d)⁻¹ hs'
      simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero d hκ), one_smul] using hi

/-- Surjectivity follows by strict descent in the two filtration indices. -/
theorem hypPBWMap_surjective (κ ell : ℂ) (hκ : κ ≠ 0) :
    Function.Surjective (hypPBWMap κ ell) := by
  intro p
  change p ∈ LinearMap.range (hypPBWMap κ ell)
  rw [p.as_sum]
  apply Submodule.sum_mem
  intro e _
  simpa only [smul_monomial, smul_eq_mul, mul_one] using
    (LinearMap.range (hypPBWMap κ ell)).smul_mem (coeff e p)
    (hypPBWMap_monomial_mem_range κ ell hκ e)

/-- A linear automorphism of the polynomial space supplied by negative Sugawara words. -/
def hypPBWEquiv (κ ell : ℂ) (hκ : κ ≠ 0) : hypFock ≃ₗ[ℂ] hypFock :=
  LinearEquiv.ofBijective (hypPBWMap κ ell)
    ⟨hypPBWMap_injective κ ell hκ, hypPBWMap_surjective κ ell hκ⟩

end VOA.Moonshine.ConwayNorton
