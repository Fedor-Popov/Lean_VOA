import VOA.Classification.COne.OrbOctaZPolynomial

/-! # A concrete positive-root candidate and the remaining Zhu identity

The expected distinct S4 lowest weights are zero and `positiveWeightQ` below.
The order-three and order-four sectors contribute r^2/36 (3 does not divide r)
and s^2/64 (s odd), respectively. Splitting the untwisted A4 sectors suggests
9, 25/4, 25/16 and 49/16 in addition to the thirteen already forced weights.
See Wu--Zhang, arXiv:1603.01797, Section 5. The table here is a candidate:
only its arithmetic, and consequences of its Zhu identity, are proved.
In particular, neither the published exhaustion argument nor its Section 3
positivity assumption (V4) is imported as a Lean premise or theorem.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZ
open VOA Polynomial OrbZhu OrbB5

/-- The 24 expected strictly positive distinct weights. -/
def positiveWeightQ : Fin 24 → ℚ :=
  ![4, 9/4, 1/36, 25/36, 49/36, 1/9, 4/9, 16/9, 1, 1/4, 1/16, 9/16,
    9, 25/4, 25/16, 49/16, 1/64, 9/64, 25/64, 49/64, 81/64, 121/64, 169/64, 225/64]

theorem positiveWeightQ_injective : Function.Injective positiveWeightQ := by decide +kernel

theorem positiveWeightQ_gap : ∀ i, (1 : ℚ) / 64 ≤ positiveWeightQ i := by decide +kernel

/-- The positive part of the candidate polynomial. -/
def positivePolynomial : ℂ[X] := ∏ i : Fin 24, (X - Polynomial.C (positiveWeightQ i : ℂ))

/-- A degree-25 polynomial, with one zero root and 24 positive rational roots. -/
def candidatePolynomial : ℂ[X] := X * positivePolynomial

theorem positivePolynomial_monic : positivePolynomial.Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem positivePolynomial_natDegree : positivePolynomial.natDegree = 24 := by
  rw [positivePolynomial, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

theorem candidatePolynomial_monic : candidatePolynomial.Monic :=
  monic_X.mul positivePolynomial_monic

theorem candidatePolynomial_natDegree : candidatePolynomial.natDegree = 25 := by
  rw [candidatePolynomial, natDegree_mul monic_X.ne_zero positivePolynomial_monic.ne_zero,
    natDegree_X, positivePolynomial_natDegree]

theorem candidate_roots {h : ℂ} :
    candidatePolynomial.eval h = 0 ↔ h = 0 ∨ ∃ i, h = (positiveWeightQ i : ℂ) := by
  simp only [candidatePolynomial, positivePolynomial, eval_mul, eval_X, eval_prod,
    eval_sub, eval_C, mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero]

theorem positivePolynomial_eval_zero_ne : positivePolynomial.eval 0 ≠ 0 := by
  classical
  rw [positivePolynomial, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp only [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
  have hp : (0 : ℚ) < positiveWeightQ i :=
    lt_of_lt_of_le (by norm_num) (positiveWeightQ_gap i)
  exact_mod_cast ne_of_gt hp

/-- OPEN: the concrete degree-25 identity in the intrinsic S4 Zhu algebra. -/
def OctahedralConformalZhuRelation : Prop :=
  (aeval (omegaL W) candidatePolynomial) (mk W W.vacuum) = 0

/-- Once the identity is certified, every realized bottom lies in this table. -/
theorem lowestWeight_table (hP : OctahedralConformalZhuRelation)
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ}
    (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    h = 0 ∨ ∃ i, h = (positiveWeightQ i : ℂ) :=
  candidate_roots.mp (lowestWeight_root_of_conformalPolynomial N hl hne _ hP)

theorem lowestWeight_zero_or_gap (hP : OctahedralConformalZhuRelation)
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ}
    (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    h = 0 ∨ (1 : ℝ) / 64 ≤ h.re := by
  rcases lowestWeight_table hP N hl hne with hz | ⟨i, rfl⟩
  · exact Or.inl hz
  · right
    fin_cases i <;> norm_num [positiveWeightQ]

/-- The candidate identity acts on all of Zhu's algebra, if it acts on 1. -/
theorem candidate_annihilates (hP : OctahedralConformalZhuRelation) :
    aeval (omegaL W) candidatePolynomial = 0 := by
  apply LinearMap.ext
  intro z
  change (aeval (omegaL W) candidatePolynomial) z = 0
  rw [aeval_omegaL_eq_Amul, hP, map_zero, LinearMap.zero_apply]

end VOA.Classification.COne.OrbOctaZ
