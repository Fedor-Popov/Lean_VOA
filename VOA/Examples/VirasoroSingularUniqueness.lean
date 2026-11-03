/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroLeadingInvariants

/-!
# A singular Verma state is determined by its translation coefficient

Positive modes preserve the longest PBW length and act there by polynomial
vector fields. Their common invariants use only the translation variable.
Thus every nonzero singular state at level n has a nonzero coefficient of
L-minus-one to the n-th power. This proves uniqueness up to normalization,
not existence of singular states at any proposed Kac label.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangFockExponential LeeYangFockVirasoro LeeYangWardClosure

/-- A word's symbol at its own length is the commutative oscillator monomial. -/
theorem vermaSymbol_word (ell p : ℂ) (w : List ℕ) :
    vermaSymbol ell p w.length (negWord _ _ w) = vermaWordSymbol w := by
  change vermaSymbolProjection (vermaPolynomialLift ell p (negWord _ _ w) w.length) = _
  rw [vermaPolynomialLift_word, vermaWordPolynomial_top]
  rfl

/-- A word has no symbol above its number of creation factors. -/
theorem vermaSymbol_word_above (ell p : ℂ) (w : List ℕ) (d : ℕ)
    (hd : w.length < d) : vermaSymbol ell p d (negWord _ _ w) = 0 := by
  change vermaSymbolProjection (vermaPolynomialLift ell p (negWord _ _ w) d) = _
  rw [vermaPolynomialLift_word, vermaWordPolynomial_coeff_above ell p w d hd, map_zero]

/-- On states with PBW length at most d, positive modes induce the stated
polynomial derivation on the length-d symbol. Lower words contribute zero. -/
theorem vermaSymbol_positive (ell p : ℂ) (d m : ℕ) (hm : 0 < m)
    (v : Verma (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p))
    (hv : ∀ w ∈ ((vermaSortedBasis _ _).repr v).support, w.val.length ≤ d) :
    vermaSymbol ell p d (vermaMode _ _ (m:ℤ) v) =
      vermaLeadingDerivation m (vermaSymbol ell p d v) := by
  classical
  let b := vermaSortedBasis (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p)
  have he := b.linearCombination_repr v
  conv_lhs => rw [← he]
  conv_rhs => rw [← he]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    b, vermaSortedBasis_apply]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Derivation.map_smul]
  congr 1
  by_cases hd : w.val.length = d
  · subst d
    rw [vermaPositive_word_symbol ell p w.val m hm, vermaSymbol_word]
  · have hl : w.val.length < d := lt_of_le_of_ne (hv w hw) hd
    rw [vermaSymbol_word_above ell p w.val d hl, map_zero]
    change vermaSymbolProjection (vermaPolynomialLift ell p
      (vermaMode _ _ (m:ℤ) (negWord _ _ w.val)) d) = 0
    rw [vermaPositive_word_above ell p w.val m d hm hl, map_zero]

/-- At maximal PBW length the coefficient of an ordered word is unchanged
by passing to the oscillator symbol: distinct ordered words have distinct monomials. -/
theorem vermaSymbol_max_coordinate (ell p : ℂ)
    (v : Verma (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p))
    (w : {w : List ℕ // SortedWord w})
    (hw : w ∈ ((vermaSortedBasis _ _).repr v).support)
    (hmax : ∀ u ∈ ((vermaSortedBasis _ _).repr v).support,
      u.val.length ≤ w.val.length) :
    MvPolynomial.coeff (vermaWordExponent w.val) (vermaSymbol ell p w.val.length v) =
      (vermaSortedBasis _ _).repr v w := by
  classical
  let b := vermaSortedBasis (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p)
  have he := congrArg (vermaSymbol ell p w.val.length) (b.linearCombination_repr v)
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    b, vermaSortedBasis_apply] at he
  rw [← he]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [Finset.sum_eq_single w]
  · change _ * MvPolynomial.coeff _
      (vermaSymbolProjection (vermaPolynomialLift ell p (negWord _ _ w.val) _)) = _
    rw [vermaPolynomialLift_word, vermaWordPolynomial_top_selector ell p _ w.val
      w.val w.property w.property (le_refl _) rfl]
    simp
  · intro u hu huw
    change _ * MvPolynomial.coeff _
      (vermaSymbolProjection (vermaPolynomialLift ell p (negWord _ _ u.val) _)) = 0
    rw [vermaPolynomialLift_word, vermaWordPolynomial_top_selector ell p _ u.val
      w.val u.property w.property (hmax u hu) rfl,
      if_neg (fun he => huw (Subtype.ext he)), mul_zero]
  · exact fun hn => (hn hw).elim

/-- Every nonzero singular state has a nonzero all-translation PBW coefficient.
Only the actual L1 and L2 equations are needed; their commutators supply
all positive modes. This is a detection theorem, not a singular existence theorem. -/
theorem verma_singular_top_ne_zero (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n) (hne : v ≠ 0)
    (h1 : vermaMode c h 1 v = 0) (h2 : vermaMode c h 2 v = 0) :
    vermaTopCoordinate c h n v ≠ 0 := by
  classical
  obtain ⟨ell,p,rfl,rfl⟩ := exists_vermaFockFamily_parameters c h
  let b := vermaSortedBasis (3 - 24 * ell ^ 2) (p ^ 2 - 2 * ell * p)
  let a := b.repr v
  have ha : a ≠ 0 := fun he => hne (b.repr.injective (he.trans (map_zero _).symm))
  obtain ⟨w,hw,hmax⟩ := a.support.exists_max_image (fun w => w.val.length)
    (Finsupp.support_nonempty_iff.mpr ha)
  have hc := vermaSymbol_max_coordinate ell p v w hw hmax
  have hcn : MvPolynomial.coeff (vermaWordExponent w.val)
      (vermaSymbol ell p w.val.length v) ≠ 0 := by
    rw [hc]
    exact Finsupp.mem_support_iff.mp hw
  have hinv : ∀ m : ℕ, 0 < m → vermaLeadingDerivation m
      (vermaSymbol ell p w.val.length v) = 0 := by
    intro m hm
    rw [← vermaSymbol_positive ell p w.val.length m hm v hmax,
      verma_positive_zero_of_one_two _ _ v h1 h2 m (by exact_mod_cast hm), map_zero]
  have hz : ∀ i ∈ w.val, i = 0 := by
    intro i hi
    apply vermaLeadingInvariants_vars _ hinv (i,0)
    apply (MvPolynomial.mem_vars_iff_mem_support (i,0)).mpr
    refine ⟨vermaWordExponent w.val, MvPolynomial.mem_support_iff.mpr hcn, ?_⟩
    rw [Finsupp.mem_support_iff, vermaWordExponent_count]
    exact Nat.ne_of_gt (List.count_pos_iff.mpr hi)
  have he : energyHW w.val = n := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hw)
      (verma_eigen_coordinate_zero _ _ v n
        ((verma_mem_level_iff_eigen _ _ n v).mp hv) w (by exact_mod_cast hn))
  have hwrep : w.val = List.replicate n 0 := by
    have hr : w.val = List.replicate w.val.length 0 := List.eq_replicate_of_mem hz
    have hl : w.val.length = energyHW w.val := by
      rw [hr]
      simp [energyHW]
    simpa only [hl,he] using hr
  change b.repr v ⟨List.replicate n 0, _⟩ ≠ 0
  have hw' : w = ⟨List.replicate n 0,sortedWord_replicate_zero n⟩ := Subtype.ext hwrep
  rw [← hw']
  exact Finsupp.mem_support_iff.mp hw

/-- Two singular states at the same level with the same translation
coefficient are equal, at every charge and highest weight, including collisions. -/
theorem verma_singular_eq_of_top_eq (c h : ℂ) (n : ℕ) (v w : Verma c h)
    (hv : v ∈ sortedSpan c h n) (hw : w ∈ sortedSpan c h n)
    (hv1 : vermaMode c h 1 v = 0) (hv2 : vermaMode c h 2 v = 0)
    (hw1 : vermaMode c h 1 w = 0) (hw2 : vermaMode c h 2 w = 0)
    (he : vermaTopCoordinate c h n v = vermaTopCoordinate c h n w) : v = w := by
  by_contra hn
  apply verma_singular_top_ne_zero c h n (v-w)
    (Submodule.sub_mem _ hv hw) (sub_ne_zero.mpr hn)
    (by simp [hv1,hw1]) (by simp [hv2,hw2])
  simp [he]

/-- A fixed nonzero singular vector spans every singular vector at its
level. The coefficient ratio is explicit and has a proved nonzero denominator;
this statement remains valid at colliding Kac parameters. -/
theorem verma_singular_eq_smul (c h : ℂ) (n : ℕ) (v w : Verma c h)
    (hv : v ∈ sortedSpan c h n) (hw : w ∈ sortedSpan c h n) (hwne : w ≠ 0)
    (hv1 : vermaMode c h 1 v = 0) (hv2 : vermaMode c h 2 v = 0)
    (hw1 : vermaMode c h 1 w = 0) (hw2 : vermaMode c h 2 w = 0) :
    v = (vermaTopCoordinate c h n v / vermaTopCoordinate c h n w) • w := by
  apply verma_singular_eq_of_top_eq c h n v _ hv
    (Submodule.smul_mem _ _ hw) hv1 hv2
    (by simp [hw1]) (by simp [hw2])
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _
    (verma_singular_top_ne_zero c h n w hw hwne hw1 hw2)]

end VOA.InverseDS.VirasoroVerma
