import VOA.Moonshine.MoonshineCNHyperbolicPBWCoordinates
import VOA.Moonshine.MoonshineCNHyperbolicNegativeVirasoro

/-! # Concrete light-cone splitting of the polynomial hyperbolic Fock space

This is a splitting of the actual negative Sugawara ranges and positive
longitudinal kernels. It does not construct the tensor-sector StringModule.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial

/-- Polynomials all of whose monomials contain at least one b variable. -/
def hypBPositive : Submodule ℂ hypFock :=
  Finsupp.supported ℂ ℂ {e : (ℕ × Fin 2) →₀ ℕ | Finsupp.weight hypBCountWeight e ≠ 0}

theorem hypOneFamily_eq_countZero : hypOneFamily 0 =
    (Finsupp.supported ℂ ℂ {e : (ℕ × Fin 2) →₀ ℕ |
      Finsupp.weight hypBCountWeight e = 0} : Submodule ℂ hypFock) := by
  apply Submodule.ext
  intro p
  change p ∈ hypOneFamily 0 ↔ ∀ e ∈ p.support, Finsupp.weight hypBCountWeight e = 0
  constructor
  · intro hp e he
    exact (hypOneFamily_bHomogeneous_zero p hp).1 (mem_support_iff.mp he)
  · intro hp
    rw [hypOneFamily_mem_iff]
    intro v hv
    obtain ⟨e, he, hv⟩ := (mem_vars_iff_mem_support v).mp hv
    have hl := Finsupp.le_weight_of_ne_zero' hypBCountWeight (Finsupp.mem_support_iff.mp hv)
    rw [hp e he] at hl
    have hn : v.2 ≠ 1 := by
      intro h
      simp [hypBCountWeight, h] at hl
    have hval := v.2.isLt
    have hne : v.2.val ≠ 1 := by simpa [Fin.ext_iff] using hn
    apply Fin.ext
    simp only [Fin.val_zero]
    omega

theorem hypBPositive_isCompl : IsCompl hypBPositive (hypOneFamily 0) := by
  rw [hypOneFamily_eq_countZero]
  change IsCompl (Finsupp.supported ℂ ℂ {e | Finsupp.weight hypBCountWeight e ≠ 0})
    (Finsupp.supported ℂ ℂ {e | Finsupp.weight hypBCountWeight e = 0})
  exact ⟨Finsupp.disjoint_supported_supported (Set.disjoint_left.mpr fun _ hne he => hne he),
    Finsupp.codisjoint_supported_supported (by
      rw [codisjoint_iff, eq_top_iff]
      intro e _
      exact em (Finsupp.weight hypBCountWeight e ≠ 0) |>.elim Or.inl
        (fun h => Or.inr (not_ne_iff.mp h)))⟩

theorem hypBPositive_of_homogeneous {d w : ℕ} {p : hypFock}
    (hp : p ∈ hypBHomogeneous d w) (hd : d ≠ 0) : p ∈ hypBPositive := by
  intro e he
  change Finsupp.weight hypBCountWeight e ≠ 0
  rwa [hp.1 (mem_support_iff.mp he)]

/-- The actual sum of negative Sugawara ranges. -/
def hypNegativeSpurious (κ ell : ℂ) : Submodule ℂ hypFock :=
  ⨆ j : ℕ, LinearMap.range (hypSugawara κ ell (-(j + 1 : ℤ)))

theorem hypPBWMap_positive_le_spurious (κ ell : ℂ) :
    hypBPositive.map (hypPBWMap κ ell) ≤ hypNegativeSpurious κ ell := by
  rintro _ ⟨p, hp, rfl⟩
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro e he
  rw [hypPBWMap_monomial]
  apply Submodule.smul_mem
  have hn : hypCanonicalBWord e ≠ [] := by
    intro h
    have hlen := (hypCanonicalBWord_degrees e).1
    rw [h, List.length_nil] at hlen
    exact hp he hlen.symm
  cases hw : hypCanonicalBWord e with
  | nil => exact (hn hw).elim
  | cons j v =>
    change hypSugawara κ ell (-(j + 1 : ℤ)) _ ∈ hypNegativeSpurious κ ell
    exact (le_iSup (fun j : ℕ => LinearMap.range (hypSugawara κ ell (-(j + 1 : ℤ)))) j)
      (LinearMap.mem_range_self _ _)

theorem hypNegativeSpurious_le_PBWMap_positive (κ ell : ℂ) (hκ : κ ≠ 0) :
    hypNegativeSpurious κ ell ≤ hypBPositive.map (hypPBWMap κ ell) := by
  apply iSup_le
  intro j p hp
  obtain ⟨p, rfl⟩ := hp
  obtain ⟨q, rfl⟩ := hypPBWMap_surjective κ ell hκ p
  rw [q.as_sum, map_sum, map_sum]
  apply Submodule.sum_mem
  intro e _
  rw [hypPBWMap_monomial, map_smul]
  apply Submodule.smul_mem
  change stringNegativeWord (fun j => hypSugawara κ ell (-(j + 1 : ℤ)))
    (monomial (hypAExponent e) 1) (j :: hypCanonicalBWord e) ∈ _
  apply (show Submodule.span ℂ {y | ∃ v : List ℕ,
    v ≠ [] ∧ stringSortedWord v ∧
      stringWordEnergy v = stringWordEnergy (j :: hypCanonicalBWord e) ∧
      stringNegativeWord (fun j => hypSugawara κ ell (-(j + 1 : ℤ)))
        (monomial (hypAExponent e) 1) v = y} ≤ hypBPositive.map (hypPBWMap κ ell) from ?_)
    (hypSugawara_negative_nonempty_straightening κ ell _ _ (by simp))
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, hs, _, rfl⟩
  rw [← hypNegativeWordOperator_apply, ← hypPBWMap_sorted_word κ ell v hs _
    (hypAExponent_oneFamily e 1)]
  exact ⟨_, hypBPositive_of_homogeneous
    (hypBHomogeneous_mul (hypBWordMonomial_homogeneous v)
      (hypOneFamily_bHomogeneous_zero _ (hypAExponent_oneFamily e 1)))
    (by simpa using hv), rfl⟩

theorem hypNegativeSpurious_eq_PBWMap_positive (κ ell : ℂ) (hκ : κ ≠ 0) :
    hypNegativeSpurious κ ell = hypBPositive.map (hypPBWMap κ ell) :=
  le_antisymm (hypNegativeSpurious_le_PBWMap_positive κ ell hκ)
    (hypPBWMap_positive_le_spurious κ ell)

/-- Concrete Fock-space light-cone splitting with only the nonzero-momentum hypothesis. -/
theorem hypFock_lightConeSplit (κ ell : ℂ) (hκ : κ ≠ 0) :
    IsCompl (hypNegativeSpurious κ ell) (hypOneFamily 0) := by
  rw [hypNegativeSpurious_eq_PBWMap_positive κ ell hκ]
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, hy, he⟩ := hx.1
    have he' : y = x := hypPBWMap_injective κ ell hκ
      (he.trans (hypPBWMap_oneFamily κ ell x hx.2).symm)
    subst y
    exact hypBPositive_isCompl.disjoint.le_bot ⟨hy, hx.2⟩
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨p, rfl⟩ := hypPBWMap_surjective κ ell hκ x
    have hp : p ∈ hypBPositive ⊔ hypOneFamily 0 := by rw [hypBPositive_isCompl.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hp
    rw [← he, map_add, hypPBWMap_oneFamily κ ell b hb]
    exact Submodule.mem_sup.mpr ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩

theorem hypOneFamily_eq_commonKernel (a : Fin 2) (charge : ℂ) :
    hypOneFamily a = ⨅ j : ℕ, LinearMap.ker (hypOscillator a charge (j + 1 : ℤ)) := by
  apply Submodule.ext
  intro p
  simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hypOneFamily_iff_oscillator a charge p

theorem hypFock_lightConeSplit_oscillator (κ ell : ℂ) (hκ : κ ≠ 0) :
    IsCompl (⨆ j : ℕ, LinearMap.range (hypSugawara κ ell (-(j + 1 : ℤ))))
      (⨅ j : ℕ, LinearMap.ker (hypOscA κ (j + 1 : ℤ))) := by
  rw [← hypOneFamily_eq_commonKernel]
  exact hypFock_lightConeSplit κ ell hκ

end VOA.Moonshine.ConwayNorton
