import VOA.Moonshine.MoonshineCNHyperbolicPBWEquiv

/-! # Coordinate identities for the sorted-word equivalence -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial

def hypNegativeWordOperator (κ ell : ℂ) (v : List ℕ) : Module.End ℂ hypFock :=
  (v.map fun j => hypSugawara κ ell (-(j + 1 : ℤ))).prod

theorem hypNegativeWordOperator_apply (κ ell : ℂ) (v : List ℕ) (p : hypFock) :
    hypNegativeWordOperator κ ell v p =
      stringNegativeWord (fun j => hypSugawara κ ell (-(j + 1 : ℤ))) p v := by
  induction v with
  | nil => rfl
  | cons j v ih =>
    simpa only [hypNegativeWordOperator, List.map_cons, List.prod_cons,
      Module.End.mul_apply, stringNegativeWord] using congrArg (hypSugawara κ ell _) ih

theorem hypOneFamily_monomial_of_support (a : Fin 2) (p : hypFock)
    (hp : p ∈ hypOneFamily a) (e : (ℕ × Fin 2) →₀ ℕ) (he : e ∈ p.support) :
    monomial e (1 : ℂ) ∈ hypOneFamily a := by
  rw [hypOneFamily_mem_iff]
  intro v hv
  rw [vars_monomial one_ne_zero] at hv
  by_contra h
  exact Finsupp.mem_support_iff.mp hv
    (hypOneFamily_coeff a p hp e (mem_support_iff.mp he) v h)

theorem hypAExponent_add (e f : (ℕ × Fin 2) →₀ ℕ) :
    hypAExponent (e + f) = hypAExponent e + hypAExponent f :=
  Finsupp.filter_add

theorem hypBExponent_add (e f : (ℕ × Fin 2) →₀ ℕ) :
    hypBExponent (e + f) = hypBExponent e + hypBExponent f := by
  ext j
  rfl

theorem hypAExponent_bEmbedding (b : ℕ →₀ ℕ) :
    hypAExponent (b.mapDomain (fun j => (j, 1))) = 0 := by
  ext ⟨j, a⟩
  fin_cases a
  · simp only [hypAExponent, Finsupp.filter_apply, Finsupp.zero_apply]
    exact Finsupp.mapDomain_notin_range b (j, 0) (by simp)
  · simp [hypAExponent]

theorem hypBExponent_bEmbedding (b : ℕ →₀ ℕ) :
    hypBExponent (b.mapDomain (fun j => (j, 1))) = b :=
  Finsupp.comapDomain_mapDomain _ (fun _ _ h => (Prod.mk.inj h).1) b

theorem hypAExponent_of_oneFamily (e : (ℕ × Fin 2) →₀ ℕ)
    (he : monomial e (1 : ℂ) ∈ hypOneFamily 0) : hypAExponent e = e := by
  ext v
  by_cases hv : v.2 = 0
  · simp [hypAExponent, hv]
  · have hz := hypOneFamily_coeff 0 _ he e (by simp) v hv
    simp [hypAExponent, hv, hz]

theorem hypBExponent_of_oneFamily (e : (ℕ × Fin 2) →₀ ℕ)
    (he : monomial e (1 : ℂ) ∈ hypOneFamily 0) : hypBExponent e = 0 := by
  ext j
  exact hypOneFamily_coeff 0 _ he e (by simp) (j, 1) (by change (1 : Fin 2) ≠ 0; decide)

theorem hypPBWMap_sorted_monomial (κ ell : ℂ) (v : List ℕ) (hv : stringSortedWord v)
    (e : (ℕ × Fin 2) →₀ ℕ) (he : monomial e (1 : ℂ) ∈ hypOneFamily 0) :
    hypPBWMap κ ell (hypBWordMonomial v * monomial e 1) =
      hypNegativeWordOperator κ ell v (monomial e 1) := by
  let b := (v : Multiset ℕ).toFinsupp
  have hA : hypAExponent (b.mapDomain (fun j => (j, 1)) + e) = e := by
    rw [hypAExponent_add, hypAExponent_bEmbedding, zero_add,
      hypAExponent_of_oneFamily e he]
  have hB : hypBExponent (b.mapDomain (fun j => (j, 1)) + e) = b := by
    rw [hypBExponent_add, hypBExponent_bEmbedding, hypBExponent_of_oneFamily e he, add_zero]
  have hw : hypCanonicalBWord (b.mapDomain (fun j => (j, 1)) + e) = v := by
    rw [hypCanonicalBWord, hB]
    simp only [b, Multiset.toFinsupp_toMultiset, Multiset.coe_sort]
    exact List.mergeSort_eq_self _ hv
  rw [hypBWordMonomial_exponent, monomial_mul, one_mul, hypPBWMap_monomial,
    one_smul, hA, hw, hypNegativeWordOperator_apply]

/-- The sorted-word map agrees with every sorted operator word on every
b-free base polynomial, not just the canonical monomial representatives. -/
theorem hypPBWMap_sorted_word (κ ell : ℂ) (v : List ℕ) (hv : stringSortedWord v)
    (p : hypFock) (hp : p ∈ hypOneFamily 0) :
    hypPBWMap κ ell (hypBWordMonomial v * p) = hypNegativeWordOperator κ ell v p := by
  classical
  rw [p.as_sum, Finset.mul_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hm : (monomial e (coeff e p) : hypFock) = coeff e p • monomial e 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, mul_smul_comm, map_smul, map_smul,
    hypPBWMap_sorted_monomial κ ell v hv e (hypOneFamily_monomial_of_support 0 p hp e he)]

theorem hypPBWMap_oneFamily (κ ell : ℂ) (p : hypFock) (hp : p ∈ hypOneFamily 0) :
    hypPBWMap κ ell p = p := by
  simpa only [hypBWordMonomial, List.map_nil, List.prod_nil, one_mul,
    hypNegativeWordOperator, Module.End.one_apply] using
    hypPBWMap_sorted_word κ ell [] (by simp) p hp

end VOA.Moonshine.ConwayNorton
