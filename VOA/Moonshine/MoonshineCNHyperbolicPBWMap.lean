import VOA.Moonshine.MoonshineCNHyperbolicFilteredWords
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort

/-! # The concrete sorted-word map on hyperbolic monomials -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial

def hypAExponent (e : (ℕ × Fin 2) →₀ ℕ) : (ℕ × Fin 2) →₀ ℕ :=
  e.filter fun v => v.2 = 0

def hypBExponent (e : (ℕ × Fin 2) →₀ ℕ) : ℕ →₀ ℕ :=
  e.comapDomain (fun j => (j, 1)) (fun _ _ _ _ h => (Prod.mk.inj h).1)

def hypCanonicalBWord (e : (ℕ × Fin 2) →₀ ℕ) : List ℕ :=
  (hypBExponent e).toMultiset.sort (· ≥ ·)

theorem hypCanonicalBWord_sorted (e : (ℕ × Fin 2) →₀ ℕ) :
    stringSortedWord (hypCanonicalBWord e) := Multiset.pairwise_sort _ _

theorem hypBWordMonomial_exponent (v : List ℕ) :
    hypBWordMonomial v =
      monomial ((v : Multiset ℕ).toFinsupp.mapDomain (fun j => (j, 1))) (1 : ℂ) := by
  induction v with
  | nil => simp [hypBWordMonomial]
  | cons j v ih =>
    change X (j, 1) * hypBWordMonomial v = _
    rw [ih, show (j :: v : List ℕ) = [j] ++ v from rfl,
      ← Multiset.coe_add, map_add, Finsupp.mapDomain_add]
    simp only [Multiset.coe_singleton, Multiset.toFinsupp_singleton, Finsupp.mapDomain_single,
      X, monomial_mul, one_mul]

theorem hypExponent_split (e : (ℕ × Fin 2) →₀ ℕ) :
    (hypBExponent e).mapDomain (fun j => (j, 1)) + hypAExponent e = e := by
  ext ⟨j, a⟩
  fin_cases a
  · rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by simp)]
    simp [hypAExponent]
  · change (hypBExponent e).mapDomain (fun j => (j, (1 : Fin 2))) (j, 1) +
      hypAExponent e (j, 1) = e (j, 1)
    rw [Finsupp.mapDomain_apply
      (f := fun j : ℕ => (j, (1 : Fin 2)))
      (fun _ _ h => (Prod.mk.inj h).1)]
    simp [hypAExponent, hypBExponent, Finsupp.comapDomain_apply]

theorem hypAExponent_oneFamily (e : (ℕ × Fin 2) →₀ ℕ) (c : ℂ) :
    monomial (hypAExponent e) c ∈ hypOneFamily 0 := by
  rw [hypOneFamily_mem_iff]
  intro v hv
  by_cases hc : c = 0
  · simp [hc] at hv
  · rw [vars_monomial hc] at hv
    by_contra h
    exact Finsupp.mem_support_iff.mp hv (by simp [hypAExponent, h])

theorem hypCanonicalBWord_factorization (e : (ℕ × Fin 2) →₀ ℕ) :
    hypBWordMonomial (hypCanonicalBWord e) * monomial (hypAExponent e) (1 : ℂ) =
      monomial e 1 := by
  rw [hypBWordMonomial_exponent]
  simp only [hypCanonicalBWord, Multiset.sort_eq, Finsupp.toMultiset_toFinsupp,
    monomial_mul, one_mul, hypExponent_split]

theorem hypCanonicalBWord_degrees (e : (ℕ × Fin 2) →₀ ℕ) :
    (hypCanonicalBWord e).length = Finsupp.weight hypBCountWeight e ∧
      stringWordEnergy (hypCanonicalBWord e) = Finsupp.weight hypBLevelWeight e := by
  have h := hypBHomogeneous_mul (hypBWordMonomial_homogeneous (hypCanonicalBWord e))
    (hypOneFamily_bHomogeneous_zero _ (hypAExponent_oneFamily e 1))
  rw [hypCanonicalBWord_factorization] at h
  have hc : coeff e (monomial e (1 : ℂ)) ≠ 0 := by simp
  exact ⟨by simpa using (h.1 hc).symm, by simpa using (h.2 hc).symm⟩

/-- Replace each b-monomial by its decreasing negative Sugawara word. -/
def hypPBWMap (κ ell : ℂ) : Module.End ℂ hypFock :=
  Finsupp.lsum ℂ fun e => LinearMap.smulRight LinearMap.id
    (stringNegativeWord (fun j => hypSugawara κ ell (-(j + 1 : ℤ)))
      (monomial (hypAExponent e) 1) (hypCanonicalBWord e))

theorem hypPBWMap_monomial (κ ell : ℂ) (e : (ℕ × Fin 2) →₀ ℕ) (c : ℂ) :
    hypPBWMap κ ell (monomial e c) = c •
      stringNegativeWord (fun j => hypSugawara κ ell (-(j + 1 : ℤ)))
        (monomial (hypAExponent e) 1) (hypCanonicalBWord e) := by
  rw [hypPBWMap]
  erw [Finsupp.lsum_single]
  rfl

/-- The sorted-word map is triangular with diagonal `κ` to the b-count. -/
theorem hypPBWMap_leading (κ ell : ℂ) (e : (ℕ × Fin 2) →₀ ℕ) :
    hypPBWMap κ ell (monomial e 1) -
      κ ^ (Finsupp.weight hypBCountWeight e) • monomial e 1 ∈
      hypBFiltered (Finsupp.weight hypBCountWeight e) (Finsupp.weight hypBLevelWeight e) := by
  have h := hypSugawara_negative_word_leading_oneFamily κ ell _
    (hypAExponent_oneFamily e 1) (hypCanonicalBWord e)
  rw [hypCanonicalBWord_factorization, (hypCanonicalBWord_degrees e).1,
    (hypCanonicalBWord_degrees e).2] at h
  simpa only [hypPBWMap_monomial, one_smul] using h

end VOA.Moonshine.ConwayNorton
