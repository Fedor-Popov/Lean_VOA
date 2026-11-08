import VOA.Moonshine.MoonshineCNHyperbolicCommutant

/-! # The hyperbolic monomial form

The Gram matrix pairs each occupation vector with the vector obtained by
exchanging its two isotropic families. Its entries are the positive-sign
oscillator factorial norms. This is the sector contravariant form, not the
opposite-momentum FHL form of the lattice vertex algebra.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial HeisenbergN

def hypSwapVariable : Equiv.Perm (ℕ × Fin 2) :=
  Equiv.prodCongr (Equiv.refl ℕ) Fin.revPerm

def hypSwapExponent : ((ℕ × Fin 2) →₀ ℕ) → ((ℕ × Fin 2) →₀ ℕ) :=
  Finsupp.equivMapDomain hypSwapVariable

@[simp] theorem hypSwapExponent_apply (d : (ℕ × Fin 2) →₀ ℕ) (v : ℕ × Fin 2) :
    hypSwapExponent d v = d (v.1, v.2.rev) := rfl

@[simp] theorem hypSwapExponent_involutive (d : (ℕ × Fin 2) →₀ ℕ) :
    hypSwapExponent (hypSwapExponent d) = d := by ext v; simp

@[simp] theorem hypSwapExponent_add (d e : (ℕ × Fin 2) →₀ ℕ) :
    hypSwapExponent (d + e) = hypSwapExponent d + hypSwapExponent e := by ext v; simp

@[simp] theorem hypSwapExponent_single (v : ℕ × Fin 2) (k : ℕ) :
    hypSwapExponent (Finsupp.single v k) = Finsupp.single (v.1, v.2.rev) k :=
  Finsupp.equivMapDomain_single _ _ _

@[simp] theorem hypSwapExponent_zero : hypSwapExponent 0 = 0 := by ext v; simp

def hypMonomialNorm (d : (ℕ × Fin 2) →₀ ℕ) : ℂ :=
  d.prod fun v k => (v.1 + 1 : ℂ) ^ k * (k.factorial : ℂ)

@[simp] theorem hypMonomialNorm_zero : hypMonomialNorm 0 = 1 := by simp [hypMonomialNorm]

theorem hypMonomialNorm_swap (d : (ℕ × Fin 2) →₀ ℕ) :
    hypMonomialNorm (hypSwapExponent d) = hypMonomialNorm d := by
  rw [hypMonomialNorm, hypSwapExponent, Finsupp.prod_equivMapDomain]
  rfl

theorem hypMonomialNorm_ne_zero (d : (ℕ × Fin 2) →₀ ℕ) : hypMonomialNorm d ≠ 0 := by
  rw [hypMonomialNorm, Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  refine mul_ne_zero (pow_ne_zero _ ?_) ?_
  · exact_mod_cast Nat.succ_ne_zero v.1
  · exact_mod_cast Nat.factorial_ne_zero _

theorem hypMonomialNorm_add_single (d : (ℕ × Fin 2) →₀ ℕ) (v : ℕ × Fin 2) :
    hypMonomialNorm (d + Finsupp.single v 1) =
      (v.1 + 1 : ℂ) * ((d v : ℂ) + 1) * hypMonomialNorm d := by
  have hz : ∀ w : ℕ × Fin 2, (w.1 + 1 : ℂ) ^ (0 : ℕ) * (Nat.factorial 0 : ℂ) = 1 :=
    fun _ => by simp
  rw [hypMonomialNorm, hypMonomialNorm,
    ← Finsupp.mul_prod_erase' _ v _ hz, ← Finsupp.mul_prod_erase' d v _ hz]
  rw [Finsupp.erase_add, Finsupp.erase_single, add_zero]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ, Nat.factorial_succ]
  push_cast
  ring

/-- The explicit isotropic monomial pairing. -/
def hypForm : LinearMap.BilinForm ℂ hypFock :=
  Finsupp.lsum ℂ fun d =>
    LinearMap.smulRight LinearMap.id (hypMonomialNorm d • lcoeff ℂ (hypSwapExponent d))

theorem hypForm_monomial (d : (ℕ × Fin 2) →₀ ℕ) (a : ℂ) (q : hypFock) :
    hypForm (monomial d a) q = a * (hypMonomialNorm d * coeff (hypSwapExponent d) q) := by
  rw [hypForm]
  erw [Finsupp.lsum_single]
  simp

theorem hypForm_monomial_monomial (d e : (ℕ × Fin 2) →₀ ℕ) (a b : ℂ) :
    hypForm (monomial d a) (monomial e b) =
      if hypSwapExponent d = e then a * b * hypMonomialNorm d else 0 := by
  rw [hypForm_monomial, coeff_monomial]
  by_cases he : hypSwapExponent d = e
  · simp [he]; ring
  · simp [he, Ne.symm he]

theorem hypForm_symm (p q : hypFock) : hypForm p q = hypForm q p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    induction q using MvPolynomial.induction_on' with
    | monomial e b =>
      rw [hypForm_monomial_monomial, hypForm_monomial_monomial]
      by_cases he : hypSwapExponent d = e
      · subst e
        simp only [hypSwapExponent_involutive, hypMonomialNorm_swap, if_true]
        ring
      · have he' : hypSwapExponent e ≠ d := by
          intro h
          exact he (by rw [← h, hypSwapExponent_involutive])
        rw [if_neg he, if_neg he']
    | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, hp, hq]
  | add p q hp hq => rw [map_add, LinearMap.add_apply, map_add, hp, hq]

theorem hypForm_one (q : hypFock) : hypForm 1 q = coeff 0 q := by
  rw [show (1 : hypFock) = monomial 0 1 from rfl, hypForm_monomial]
  simp

theorem hypForm_nondegenerate (p : hypFock) (hp : p ≠ 0) : ∃ q, hypForm p q ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, coeff d p ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply MvPolynomial.ext
    intro d
    simp [h d]
  refine ⟨monomial (hypSwapExponent d) 1, ?_⟩
  rw [hypForm_symm, hypForm_monomial, hypSwapExponent_involutive,
    hypMonomialNorm_swap, one_mul]
  exact mul_ne_zero (hypMonomialNorm_ne_zero d) hd

theorem hypSwapExponent_weight (d : (ℕ × Fin 2) →₀ ℕ) :
    Finsupp.weight weightFnN (hypSwapExponent d) = Finsupp.weight weightFnN d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, hypSwapExponent,
    Finsupp.sum_equivMapDomain]
  rfl

theorem hypForm_orthogonal (N Q : ℤ) (hNQ : N ≠ Q) (p q : hypFock)
    (hp : p ∈ hypLevel N) (hq : q ∈ hypLevel Q) : hypForm p q = 0 := by
  classical
  by_cases hN : 0 ≤ N
  · by_cases hQ : 0 ≤ Q
    · change p ∈ gradingZN 2 N at hp
      change q ∈ gradingZN 2 Q at hq
      rw [gradingZN_of_nonneg hN] at hp
      rw [gradingZN_of_nonneg hQ] at hq
      rw [p.as_sum, map_sum, LinearMap.coe_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro d hd
      have hdN := hp (mem_support_iff.mp hd)
      have hq0 : coeff (hypSwapExponent d) q = 0 := by
        by_contra hc
        have hdQ := hq hc
        rw [hypSwapExponent_weight, hdN] at hdQ
        omega
      rw [hypForm_monomial, hq0, mul_zero, mul_zero]
    · rw [hypLevel_negative Q (by omega)] at hq
      have he : q = 0 := hq
      rw [he, map_zero]
  · rw [hypLevel_negative N (by omega)] at hp
    have he : p = 0 := hp
    rw [he, map_zero, LinearMap.zero_apply]

theorem hypForm_weight_nondegenerate (N : ℤ) (p : hypFock) (hp : p ∈ hypLevel N)
    (hB : ∀ q ∈ hypLevel N, hypForm p q = 0) : p = 0 := by
  classical
  by_cases hN : 0 ≤ N
  · change p ∈ gradingZN 2 N at hp
    rw [gradingZN_of_nonneg hN] at hp
    apply MvPolynomial.ext
    intro d
    by_cases hd : coeff d p = 0
    · simpa using hd
    · have hw := hp hd
      have hq : monomial (hypSwapExponent d) (1 : ℂ) ∈ hypLevel N := by
        change _ ∈ gradingZN 2 N
        rw [gradingZN_of_nonneg hN]
        exact isWeightedHomogeneous_monomial _ _ _ (by rwa [hypSwapExponent_weight])
      have hz := hB _ hq
      rw [hypForm_symm, hypForm_monomial, hypSwapExponent_involutive,
        hypMonomialNorm_swap, one_mul] at hz
      exact ((mul_ne_zero (hypMonomialNorm_ne_zero d) hd) hz).elim
  · rw [hypLevel_negative N (by omega)] at hp
    exact hp

/-- Multiplication by one isotropic variable is adjoint to the opposite derivative. -/
theorem hypForm_creation_adjoint (v : ℕ × Fin 2) (p q : hypFock) :
    hypForm (X v * p) q = (v.1 + 1 : ℂ) * hypForm p (pderiv (v.1, v.2.rev) q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [X, monomial_mul, one_mul, add_comm (Finsupp.single v 1) d,
      hypForm_monomial, hypForm_monomial, hypMonomialNorm_add_single,
      hypSwapExponent_add, hypSwapExponent_single, coeff_pderiv]
    simp only [hypSwapExponent_apply, Fin.rev_rev, Prod.eta]
    ring
  | add p r hp hr =>
    rw [mul_add, map_add, LinearMap.add_apply, hp, hr,
      map_add, LinearMap.add_apply, mul_add]

/-- Both isotropic oscillator families are adjoint under reversal of the mode. -/
theorem hypForm_oscillator_adjoint (a : Fin 2) (charge : ℂ) (n : ℤ) (p q : hypFock) :
    hypForm (hypOscillator a charge n p) q =
      hypForm p (hypOscillator a charge (-n) q) := by
  have hneg (j : ℕ) (p q : hypFock) :
      hypForm (hypOscillator a charge (-(j + 1 : ℤ)) p) q =
        hypForm p (hypOscillator a charge (j + 1 : ℤ) q) := by
    rw [hypOscillator_negative_apply, hypOscillator_positive_apply,
      hypForm_creation_adjoint, map_smul, smul_eq_mul]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    simpa only [neg_neg] using hneg j p q
  · simp [LinearMap.smul_apply, map_smul, smul_eq_mul]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
    rw [hypForm_symm, hypForm_symm p, hneg]

end VOA.Moonshine.ConwayNorton
