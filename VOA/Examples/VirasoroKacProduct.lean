/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroKacDegreeCount
import VOA.Examples.VirasoroFusionLabelRoots

/-!
# Degree exhaustion from actual Kac singular states

At a nonreal parameter, distinct positive Kac labels have distinct highest
weights. If the corresponding actual singular states exist, their independent
Verma descendants give relatively prime determinant factors. The proved finite
partition count exhausts the sharp degree, so no other factor can remain.
The singular states are explicit hypotheses here: their general construction
and the vacuum simple-root theorem are not asserted by this module.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule
open scoped Classical

/-- Positive Kac labels have distinct weights at a nonreal parameter. The
possible equality of squares either identifies both labels or would force the
sum of two positive first labels to vanish. -/
theorem fusionKacWeight_injective_positive (t : ℂ) (ht : t.im ≠ 0)
    (r s r' s' : ℕ) (hr : 0 < r) (hr' : 0 < r')
    (he : fusionKacWeight r s t = fusionKacWeight r' s' t) : r = r' ∧ s = s' := by
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht
  have hsquares : ((r:ℂ)*t-s)^2 = ((r':ℂ)*t-s')^2 := by
    unfold fusionKacWeight at he
    have hh := (div_left_inj' (mul_ne_zero (by norm_num) ht0)).mp he
    linear_combination hh
  have hf : (((r:ℂ)-(r':ℂ))*t-((s:ℂ)-(s':ℂ))) *
      (((r:ℂ)+(r':ℂ))*t-((s:ℂ)+(s':ℂ))) = 0 := by
    linear_combination hsquares
  rcases mul_eq_zero.mp hf with hm | hp
  · have hi := congrArg Complex.im hm
    simp only [Complex.sub_im, Complex.mul_im,
      Complex.natCast_im, sub_zero, zero_mul, add_zero, Complex.zero_im] at hi
    have hrr : (r:ℝ) = (r':ℝ) := sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right ht)
    have hrr' : r = r' := by exact_mod_cast hrr
    subst r'
    have hss : (s:ℂ) = (s':ℂ) := by
      simpa only [sub_self, zero_mul, zero_sub, neg_eq_zero, sub_eq_zero] using hm
    exact ⟨rfl, by exact_mod_cast hss⟩
  · have hi := congrArg Complex.im hp
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.add_re,
      Complex.natCast_re, Complex.natCast_im, add_zero, zero_mul,
      sub_zero, Complex.zero_im] at hi
    have hz := (mul_eq_zero.mp hi).resolve_right ht
    have hpos : (0:ℝ) < (r:ℝ)+(r':ℝ) := by positivity
    exact False.elim (ne_of_gt hpos hz)

/-- The finite positive label pairs whose proposed singular level fits into
level n. Fin indices are shifted by one to include no zero labels. -/
noncomputable def kacLabels (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun i => (i.1.val+1)*(i.2.val+1) ≤ n)

/-- The monic product of the expected Kac factors, with full Verma descendant
partition multiplicities. Defining this polynomial does not assert it divides
the actual determinant. -/
noncomputable def kacWeightProduct (t : ℂ) (n : ℕ) : Polynomial ℂ :=
  ∏ i ∈ kacLabels n,
    (Polynomial.X-Polynomial.C (fusionKacWeight (i.1.val+1) (i.2.val+1) t)) ^
      Fintype.card (VermaPartitions (n-(i.1.val+1)*(i.2.val+1)))

/-- Each proposed factor and hence their finite product is monic. -/
theorem kacWeightProduct_monic (t : ℂ) (n : ℕ) : (kacWeightProduct t n).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (Polynomial.monic_X_sub_C _).pow _

/-- The expected product has precisely the already proved actual determinant
degree. This equality is combinatorial, independently of singular existence. -/
theorem kacWeightProduct_natDegree (t : ℂ) (n : ℕ) :
    (kacWeightProduct t n).natDegree = ∑ w : VermaPartitions n, w.val.length := by
  unfold kacWeightProduct
  rw [Polynomial.natDegree_prod_of_monic (s := kacLabels n)
    (f := fun i => (Polynomial.X-Polynomial.C (fusionKacWeight (i.1.val+1) (i.2.val+1) t)) ^
      Fintype.card (VermaPartitions (n-(i.1.val+1)*(i.2.val+1))))
    (fun i _ => (Polynomial.monic_X_sub_C (fusionKacWeight (i.1.val+1) (i.2.val+1) t)).pow
      (Fintype.card (VermaPartitions (n-(i.1.val+1)*(i.2.val+1)))))]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  rw [kacLabels, Finset.sum_filter, Fintype.sum_prod_type]
  have hh := (verma_partition_lengths_eq_kac_count n).symm
  rw [← Fin.sum_univ_eq_sum_range] at hh
  simp_rw [← Fin.sum_univ_eq_sum_range] at hh
  exact hh

/-- Actual positive-level singular states at all relevant Kac labels force
the full expected product to divide the actual highest-weight determinant.
Only the two actual Ward equations and nonzero states are supplied as input. -/
theorem kacWeightProduct_dvd_of_singular (c t : ℂ) (n : ℕ) (ht : t.im ≠ 0)
    (hs : ∀ i ∈ kacLabels n,
      ∃ v : sortedSpan c (fusionKacWeight (i.1.val+1) (i.2.val+1) t)
        ((i.1.val+1)*(i.2.val+1)), v ≠ 0 ∧
        vermaMode c (fusionKacWeight (i.1.val+1) (i.2.val+1) t) 1 v = 0 ∧
        vermaMode c (fusionKacWeight (i.1.val+1) (i.2.val+1) t) 2 v = 0) :
    kacWeightProduct t n ∣ (vermaWeightGramPolynomial c n).det := by
  have hi : Function.Injective (fun i : Fin n × Fin n =>
      fusionKacWeight (i.1.val+1) (i.2.val+1) t) := by
    intro i j hij
    have hh := fusionKacWeight_injective_positive t ht
      (i.1.val+1) (i.2.val+1) (j.1.val+1) (j.2.val+1) (by omega) (by omega) (by simpa only [Nat.cast_add, Nat.cast_one] using hij)
    apply Prod.ext <;> apply Fin.ext <;> omega
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact (Polynomial.pairwise_coprime_X_sub_C hi hij).pow
  · intro i him
    obtain ⟨v, hv, h1, h2⟩ := hs i him
    have hle : (i.1.val+1)*(i.2.val+1) ≤ n := (Finset.mem_filter.mp him).2
    have hd := vermaWeightDeterminant_dvd_of_singular c _
      ((i.1.val+1)*(i.2.val+1)) (n-(i.1.val+1)*(i.2.val+1))
      (by positivity) v hv h1 h2
    have he : (i.1.val+1)*(i.2.val+1) + (n-(i.1.val+1)*(i.2.val+1)) = n := by omega
    rw [he] at hd
    exact hd

/-- Once actual singular states at every positive Kac label are constructed,
the full normalized Verma determinant formula follows from independent
embeddings and exact degree exhaustion. No factorization or multiplicity
formula is assumed. The singular-existence premise is discharged by
`VirasoroScreening.screening_nonreal_kac_singular` (`VirasoroScreeningKacRoots.lean`). -/
theorem vermaWeightDeterminant_eq_kac_of_singular (c t : ℂ) (n : ℕ) (ht : t.im ≠ 0)
    (hs : ∀ i ∈ kacLabels n,
      ∃ v : sortedSpan c (fusionKacWeight (i.1.val+1) (i.2.val+1) t)
        ((i.1.val+1)*(i.2.val+1)), v ≠ 0 ∧
        vermaMode c (fusionKacWeight (i.1.val+1) (i.2.val+1) t) 1 v = 0 ∧
        vermaMode c (fusionKacWeight (i.1.val+1) (i.2.val+1) t) 2 v = 0) :
    (vermaWeightGramPolynomial c n).det =
      Polynomial.C (∏ w : VermaPartitions n, vermaDiagonalContraction w.val) *
        kacWeightProduct t n := by
  have he := Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (kacWeightProduct_monic t n) (kacWeightProduct_dvd_of_singular c t n ht hs)
    (by rw [vermaWeightDeterminant_natDegree, kacWeightProduct_natDegree])
  simpa only [vermaWeightDeterminant_leadingCoeff] using he

end VOA.InverseDS.VirasoroVerma
