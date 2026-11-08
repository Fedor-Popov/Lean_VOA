import VOA.Moonshine.MoonshineCNTensorPBWMap

/-! # Bijectivity of the tensor-sector PBW map

Finite polynomial support, with coefficients in the matter module, supplies
both maximal-degree injectivity and well-founded surjectivity.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped TensorProduct BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem hypTensorPBWMap_coefficient_at_max (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (x : V ⊗[ℂ] hypFock) (e : (ℕ × Fin 2) →₀ ℕ)
    (he : e ∈ (hypTensorCoordinates x).support)
    (hmax : ∀ t ∈ (hypTensorCoordinates x).support,
      Finsupp.weight hypBCountWeight t < Finsupp.weight hypBCountWeight e ∨
        (Finsupp.weight hypBCountWeight t = Finsupp.weight hypBCountWeight e ∧
          Finsupp.weight hypBLevelWeight t ≤ Finsupp.weight hypBLevelWeight e)) :
    hypTensorCoordinates (hypTensorPBWMap D κ ell x) e =
      κ ^ (Finsupp.weight hypBCountWeight e) • hypTensorCoordinates x e := by
  classical
  have hterm (t : (ℕ × Fin 2) →₀ ℕ) (ht : t ∈ (hypTensorCoordinates x).support) :
      hypTensorCoordinates
        (hypTensorPBWMap D κ ell (hypTensorCoordinates x t ⊗ₜ[ℂ] monomial t 1)) e =
        if t = e then κ ^ (Finsupp.weight hypBCountWeight e) • hypTensorCoordinates x e
          else 0 := by
    have hz : hypTensorCoordinates
        (hypTensorPBWMap D κ ell (hypTensorCoordinates x t ⊗ₜ[ℂ] monomial t 1) -
          κ ^ (Finsupp.weight hypBCountWeight t) •
            (hypTensorCoordinates x t ⊗ₜ[ℂ] monomial t 1)) e = 0 := by
      by_contra hc
      have hlt := (hypTensorSupported_mem _ _).mp
        (hypTensorPBWMap_leading D κ ell (hypTensorCoordinates x t) t) e hc
      have hle := hmax t ht
      change _ < _ ∨ (_ = _ ∧ _ < _) at hlt
      omega
    simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      hypTensorCoordinates_monomial] at hz
    rw [sub_eq_zero.mp hz]
    by_cases hte : t = e
    · subst t; simp
    · simp [hte, Ne.symm hte]
  conv_lhs => rw [hypTensor_expansion x, map_sum, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl hterm]
  simp [he]

/-- No negative Virasoro relation is needed for injectivity. -/
theorem hypTensorPBWMap_injective (D : ℕ → Module.End ℂ V) (κ ell : ℂ) (hκ : κ ≠ 0) :
    Function.Injective (hypTensorPBWMap D κ ell) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  by_contra hne
  have hsupport : (hypTensorCoordinates x).support.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    apply hne
    apply hypTensorCoordinates.injective
    simpa only [map_zero] using Finsupp.support_eq_empty.mp h
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image (hypTensorCoordinates x).support
    (fun t => toLex (Finsupp.weight hypBCountWeight t, Finsupp.weight hypBLevelWeight t))
    hsupport
  have hm : ∀ t ∈ (hypTensorCoordinates x).support,
      Finsupp.weight hypBCountWeight t < Finsupp.weight hypBCountWeight e ∨
        (Finsupp.weight hypBCountWeight t = Finsupp.weight hypBCountWeight e ∧
          Finsupp.weight hypBLevelWeight t ≤ Finsupp.weight hypBLevelWeight e) := by
    intro t ht
    exact Prod.Lex.toLex_le_toLex.mp (hmax t ht)
  have hc := hypTensorPBWMap_coefficient_at_max D κ ell x e he hm
  rw [hx, map_zero, Finsupp.zero_apply] at hc
  exact (smul_ne_zero (pow_ne_zero _ hκ) (Finsupp.mem_support_iff.mp he)) hc.symm

theorem hypTensorPBWMap_monomial_mem_range (D : ℕ → Module.End ℂ V)
    (κ ell : ℂ) (hκ : κ ≠ 0) (e : (ℕ × Fin 2) →₀ ℕ) (v : V) :
    v ⊗ₜ[ℂ] monomial e 1 ∈ LinearMap.range (hypTensorPBWMap D κ ell) := by
  classical
  suffices h : ∀ d w, ∀ e : (ℕ × Fin 2) →₀ ℕ,
      Finsupp.weight hypBCountWeight e = d → Finsupp.weight hypBLevelWeight e = w →
      ∀ v : V, v ⊗ₜ[ℂ] monomial e 1 ∈ LinearMap.range (hypTensorPBWMap D κ ell)
    from h _ _ e rfl rfl v
  intro d
  induction d using Nat.strong_induction_on with
  | h d ihd =>
    intro w
    induction w using Nat.strong_induction_on with
    | h w ihw =>
      intro e hed hew v
      let r := hypTensorPBWMap D κ ell (v ⊗ₜ[ℂ] monomial e 1) -
        κ ^ d • (v ⊗ₜ[ℂ] monomial e 1)
      have hr : r ∈ hypTensorFiltered d w := by
        simpa only [hed, hew] using hypTensorPBWMap_leading D κ ell v e
      have hrange : r ∈ LinearMap.range (hypTensorPBWMap D κ ell) := by
        rw [hypTensor_expansion r]
        apply Submodule.sum_mem
        intro t ht
        have hs := (hypTensorSupported_mem _ _).mp hr t (Finsupp.mem_support_iff.mp ht)
        rcases hs with hd | ⟨hd, hw⟩
        · exact ihd _ hd _ t rfl rfl _
        · exact ihw _ hw t hd rfl _
      have hs := (LinearMap.range (hypTensorPBWMap D κ ell)).sub_mem
        (LinearMap.mem_range_self _ (v ⊗ₜ[ℂ] monomial e 1)) hrange
      have hs' : κ ^ d • (v ⊗ₜ[ℂ] monomial e 1) ∈
          LinearMap.range (hypTensorPBWMap D κ ell) := by
        simpa only [r, sub_sub_cancel] using hs
      have hi := (LinearMap.range (hypTensorPBWMap D κ ell)).smul_mem (κ ^ d)⁻¹ hs'
      simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero d hκ), one_smul] using hi

/-- Surjectivity holds for arbitrary matter operators. -/
theorem hypTensorPBWMap_surjective (D : ℕ → Module.End ℂ V) (κ ell : ℂ) (hκ : κ ≠ 0) :
    Function.Surjective (hypTensorPBWMap D κ ell) := by
  intro x
  change x ∈ LinearMap.range (hypTensorPBWMap D κ ell)
  rw [hypTensor_expansion x]
  apply Submodule.sum_mem
  intro e _
  exact hypTensorPBWMap_monomial_mem_range D κ ell hκ e _

def hypTensorPBWEquiv (D : ℕ → Module.End ℂ V) (κ ell : ℂ) (hκ : κ ≠ 0) :
    (V ⊗[ℂ] hypFock) ≃ₗ[ℂ] (V ⊗[ℂ] hypFock) :=
  LinearEquiv.ofBijective (hypTensorPBWMap D κ ell)
    ⟨hypTensorPBWMap_injective D κ ell hκ, hypTensorPBWMap_surjective D κ ell hκ⟩

end VOA.Moonshine.ConwayNorton
