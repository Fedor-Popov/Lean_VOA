import VOA.Moonshine.MoonshineCNTensorPBWEquiv

/-! # Light-cone splitting for the actual tensor negative modes -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped TensorProduct BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

def hypTensorOneFamily (a : Fin 2) : Submodule ℂ (V ⊗[ℂ] hypFock) :=
  hypTensorSupported {e | monomial e 1 ∈ hypOneFamily a}

theorem hypTensorOneFamily_tmul (a : Fin 2) (v : V) (p : hypFock)
    (hp : p ∈ hypOneFamily a) : v ⊗ₜ[ℂ] p ∈ hypTensorOneFamily a := by
  apply hypTensorSupported_tmul
  intro e he
  exact hypOneFamily_monomial_of_support a p hp e (mem_support_iff.mpr he)

theorem hypTensorOneFamily_zero : hypTensorOneFamily (V := V) 0 =
    hypTensorSupported {e | Finsupp.weight hypBCountWeight e = 0} := by
  unfold hypTensorOneFamily
  congr 1
  ext e
  change monomial e (1 : ℂ) ∈ hypOneFamily 0 ↔ _
  rw [hypOneFamily_eq_countZero]
  change (∀ t ∈ (monomial e (1 : ℂ)).support, Finsupp.weight hypBCountWeight t = 0) ↔ _
  simp

theorem hypTensorPBWMap_sorted_monomial (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (l : List ℕ) (hl : stringSortedWord l) (v : V) (e : (ℕ × Fin 2) →₀ ℕ)
    (he : monomial e (1 : ℂ) ∈ hypOneFamily 0) :
    hypTensorPBWMap D κ ell (v ⊗ₜ[ℂ] (hypBWordMonomial l * monomial e 1)) =
      hypTensorWordOperator D κ ell l (v ⊗ₜ[ℂ] monomial e 1) := by
  let b := (l : Multiset ℕ).toFinsupp
  have hA : hypAExponent (b.mapDomain (fun j => (j, 1)) + e) = e := by
    rw [hypAExponent_add, hypAExponent_bEmbedding, zero_add, hypAExponent_of_oneFamily e he]
  have hB : hypBExponent (b.mapDomain (fun j => (j, 1)) + e) = b := by
    rw [hypBExponent_add, hypBExponent_bEmbedding, hypBExponent_of_oneFamily e he, add_zero]
  have hw : hypCanonicalBWord (b.mapDomain (fun j => (j, 1)) + e) = l := by
    rw [hypCanonicalBWord, hB]
    simp only [b, Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ hl
  rw [hypBWordMonomial_exponent, monomial_mul, one_mul, hypTensorPBWMap_monomial,
    hA, hw, hypTensorWordOperator_apply]

theorem hypTensorPBWMap_sorted_word (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (l : List ℕ) (hl : stringSortedWord l) (v : V) (p : hypFock)
    (hp : p ∈ hypOneFamily 0) :
    hypTensorPBWMap D κ ell (v ⊗ₜ[ℂ] (hypBWordMonomial l * p)) =
      hypTensorWordOperator D κ ell l (v ⊗ₜ[ℂ] p) := by
  classical
  rw [p.as_sum, Finset.mul_sum, TensorProduct.tmul_sum, TensorProduct.tmul_sum,
    map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hm : (monomial e (coeff e p) : hypFock) = coeff e p • monomial e 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, mul_smul_comm, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    map_smul, map_smul, hypTensorPBWMap_sorted_monomial D κ ell l hl v e
      (hypOneFamily_monomial_of_support 0 p hp e he)]

theorem hypTensorPBWMap_oneFamily (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (x : V ⊗[ℂ] hypFock) (hx : x ∈ hypTensorOneFamily 0) :
    hypTensorPBWMap D κ ell x = x := by
  have h : hypTensorOneFamily 0 ≤ LinearMap.ker (hypTensorPBWMap D κ ell - 1) := by
    apply hypTensorSupported_induction
    intro e he v
    change hypTensorPBWMap D κ ell (v ⊗ₜ[ℂ] monomial e 1) - (v ⊗ₜ[ℂ] monomial e 1) = 0
    apply sub_eq_zero.mpr
    simpa only [hypBWordMonomial, List.map_nil, List.prod_nil, one_mul,
      hypTensorWordOperator, Module.End.one_apply] using
      hypTensorPBWMap_sorted_monomial D κ ell [] (by simp) v e he
  exact sub_eq_zero.mp (h hx)

def hypTensorBPositive : Submodule ℂ (V ⊗[ℂ] hypFock) :=
  hypTensorSupported {e | Finsupp.weight hypBCountWeight e ≠ 0}

theorem hypTensorBPositive_isCompl :
    IsCompl (hypTensorBPositive (V := V)) (hypTensorOneFamily 0) := by
  rw [hypTensorOneFamily_zero]
  have h : IsCompl
      (Finsupp.supported V ℂ {e : (ℕ × Fin 2) →₀ ℕ | Finsupp.weight hypBCountWeight e ≠ 0})
      (Finsupp.supported V ℂ {e : (ℕ × Fin 2) →₀ ℕ | Finsupp.weight hypBCountWeight e = 0}) :=
    ⟨Finsupp.disjoint_supported_supported (Set.disjoint_left.mpr fun _ hne he => hne he),
      Finsupp.codisjoint_supported_supported (by
        rw [codisjoint_iff, eq_top_iff]
        intro e _
        exact em (Finsupp.weight hypBCountWeight e ≠ 0) |>.elim Or.inl
          (fun hn => Or.inr (not_ne_iff.mp hn)))⟩
  exact h.map (Submodule.orderIsoMapComap (hypTensorCoordinates (V := V))).symm

theorem hypTensorBPositive_word (l : List ℕ) (hl : l ≠ []) (v : V)
    (p : hypFock) (hp : p ∈ hypOneFamily 0) :
    v ⊗ₜ[ℂ] (hypBWordMonomial l * p) ∈ hypTensorBPositive := by
  apply hypTensorSupported_tmul
  intro e he
  have h := hypBPositive_of_homogeneous
    (hypBHomogeneous_mul (hypBWordMonomial_homogeneous l)
      (hypOneFamily_bHomogeneous_zero p hp)) (by simpa using hl)
  exact h (mem_support_iff.mpr he)

def hypTensorNegativeSpurious (D : ℕ → Module.End ℂ V) (κ ell : ℂ) :
    Submodule ℂ (V ⊗[ℂ] hypFock) := ⨆ j : ℕ, LinearMap.range (hypTensorNegative D κ ell j)

theorem hypTensorPBWMap_positive_le_spurious (D : ℕ → Module.End ℂ V) (κ ell : ℂ) :
    hypTensorBPositive.map (hypTensorPBWMap D κ ell) ≤ hypTensorNegativeSpurious D κ ell := by
  rintro _ ⟨x, hx, rfl⟩
  rw [hypTensor_expansion x, map_sum]
  apply Submodule.sum_mem
  intro e he
  rw [hypTensorPBWMap_monomial]
  have hn : hypCanonicalBWord e ≠ [] := by
    intro h
    have hlen := (hypCanonicalBWord_degrees e).1
    rw [h, List.length_nil] at hlen
    exact (hypTensorSupported_mem _ _).mp hx e (Finsupp.mem_support_iff.mp he) hlen.symm
  cases hw : hypCanonicalBWord e with
  | nil => exact (hn hw).elim
  | cons j l =>
    exact (le_iSup (fun j => LinearMap.range (hypTensorNegative D κ ell j)) j)
      (LinearMap.mem_range_self _ _)

theorem hypTensorNegativeSpurious_le_PBWMap_positive (D : ℕ → Module.End ℂ V)
    (hD : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (κ ell : ℂ) (hκ : κ ≠ 0) :
    hypTensorNegativeSpurious D κ ell ≤ hypTensorBPositive.map (hypTensorPBWMap D κ ell) := by
  apply iSup_le
  intro j x hx
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hypTensorPBWMap_surjective D κ ell hκ x
  rw [hypTensor_expansion y, map_sum, map_sum]
  apply Submodule.sum_mem
  intro e _
  rw [hypTensorPBWMap_monomial]
  change stringNegativeWord (hypTensorNegative D κ ell)
    (hypTensorCoordinates y e ⊗ₜ[ℂ] monomial (hypAExponent e) 1)
      (j :: hypCanonicalBWord e) ∈ _
  apply (show Submodule.span ℂ {z | ∃ l : List ℕ,
      l ≠ [] ∧ stringSortedWord l ∧
        stringWordEnergy l = stringWordEnergy (j :: hypCanonicalBWord e) ∧
        stringNegativeWord (hypTensorNegative D κ ell)
          (hypTensorCoordinates y e ⊗ₜ[ℂ] monomial (hypAExponent e) 1) l = z} ≤
      hypTensorBPositive.map (hypTensorPBWMap D κ ell) from ?_)
    (stringNegativeWord_mem_nonempty_sortedSpan _ (hypTensorNegative_comm D hD κ ell)
      _ _ (by simp))
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, hs, _, rfl⟩
  rw [← hypTensorWordOperator_apply, ← hypTensorPBWMap_sorted_monomial D κ ell l hs _ _
    (hypAExponent_oneFamily e 1)]
  exact ⟨_, hypTensorBPositive_word l hl _ _ (hypAExponent_oneFamily e 1), rfl⟩

theorem hypTensorNegativeSpurious_eq_PBWMap_positive (D : ℕ → Module.End ℂ V)
    (hD : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (κ ell : ℂ) (hκ : κ ≠ 0) :
    hypTensorNegativeSpurious D κ ell = hypTensorBPositive.map (hypTensorPBWMap D κ ell) :=
  le_antisymm (hypTensorNegativeSpurious_le_PBWMap_positive D hD κ ell hκ)
    (hypTensorPBWMap_positive_le_spurious D κ ell)

/-- Concrete tensor-sector splitting, assuming only the matter negative relation. -/
theorem hypTensor_lightConeSplit (D : ℕ → Module.End ℂ V)
    (hD : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (κ ell : ℂ) (hκ : κ ≠ 0) :
    IsCompl (hypTensorNegativeSpurious D κ ell) (hypTensorOneFamily 0) := by
  rw [hypTensorNegativeSpurious_eq_PBWMap_positive D hD κ ell hκ]
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, hy, he⟩ := hx.1
    have he' : y = x := hypTensorPBWMap_injective D κ ell hκ
      (he.trans (hypTensorPBWMap_oneFamily D κ ell x hx.2).symm)
    subst y
    exact hypTensorBPositive_isCompl.disjoint.le_bot ⟨hy, hx.2⟩
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hypTensorPBWMap_surjective D κ ell hκ x
    have hy : y ∈ hypTensorBPositive ⊔ hypTensorOneFamily 0 := by
      rw [hypTensorBPositive_isCompl.sup_eq_top]
      trivial
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hy
    rw [← he, map_add, hypTensorPBWMap_oneFamily D κ ell b hb]
    exact Submodule.mem_sup.mpr ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩

end VOA.Moonshine.ConwayNorton
