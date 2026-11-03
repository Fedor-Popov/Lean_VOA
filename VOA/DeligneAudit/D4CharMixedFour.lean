import VOA.DeligneAudit.D4CharDownUnit

/-!
Mixed Cauchy at (m,n,N) = (2,2,4), in every homogeneous bidegree and at arbitrary
unit alphabets. Full branching permits w = 1: both sides have the same separable
Euler unit, so cancellation gives the down-step without extracting a constant term.
The independent constant-term/Gamma proofs remain available in DownRegroup and DownKernelCT.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtMixed_four_of_last_one (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) (hu : u 4 = 1) :
    gtMixedFourSeries q h x y u =
      gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
        (gtMixedRankKernel q h u 4) := by
  apply (gtMixedExtra_isUnit q h x y).mul_left_cancel
  rw [← gtMixedFiveSeries_branch_one q h x y u hu, gtMixedFiveSeries_eq_kernel,
    gtMixedFiveKernel_branch_one q h x y u hu]

/-- GT evaluation depends only on the variables belonging to its rank. -/
theorem gtEval_congr_variables (q : R) (u v : ℕ → Rˣ) (N : ℕ) (lam : Fin N → ℤ)
    (huv : ∀ i < N, u i = v i) : gtEval q u N lam = gtEval q v N lam := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [gtEval, gtEval]
      apply Finset.sum_congr rfl
      intro μ _
      rw [huv N (by omega), ih μ (fun i hi => huv i (by omega))]

/-- The mixed Euler product depends only on its first N ambient variables. -/
theorem gtMixedRankKernel_congr_variables (q : R) (h : PochhammerUnits q)
    (u v : ℕ → Rˣ) (N : ℕ) (huv : ∀ i < N, u i = v i) :
    gtMixedRankKernel q h u N = gtMixedRankKernel q h v N := by
  have hy : gtRankYBase q h u N = gtRankYBase q h v N := by
    unfold gtRankYBase
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [huv i (Finset.mem_range.mp hi)]
  have hx : gtRankXStep q h u N = gtRankXStep q h v N := by
    unfold gtRankXStep gtMixedEulerStep
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    dsimp only
    rw [huv i (Finset.mem_range.mp hi)]
  simp only [gtMixedRankKernel, hy, hx]

/-- MC_(2,2,4), as an equality of complete homogeneous generating series. -/
theorem gtMixed_four (q : R) (h : PochhammerUnits q) (x y u : ℕ → Rˣ) :
    gtMixedFourSeries q h x y u =
      gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
        (gtMixedRankKernel q h u 4) := by
  let v : ℕ → Rˣ := fun i => if i < 4 then u i else 1
  have hv : v 4 = 1 := by simp [v]
  have he : ∀ i < 4, v i = u i := by intro i hi; simp [v, hi]
  have hf : gtMixedFourSeries q h x y v = gtMixedFourSeries q h x y u := by
    apply PowerSeries.ext
    intro n
    apply PowerSeries.ext
    intro m
    simp only [gtMixedFourSeries, coeff_mk]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro z _
    rw [gtEval_congr_variables q v u 4 _ he]
  have hh := gtMixed_four_of_last_one q h x y v hv
  rwa [hf, gtMixedRankKernel_congr_variables q h v u 4 he] at hh

/-- The complete finite partition expansion of every bidegree of the rank-four kernel. -/
theorem gtMixed_four_coeff (q : R) (h : PochhammerUnits q) (x y u : ℕ → Rˣ)
    (n m : ℕ) :
    gtBiCoeff m n
      (gtFourCollapse (fun i => (x i : R)) (fun i => (y i : R))
        (gtMixedRankKernel q h u 4)) =
      ∑ p ∈ gtPartitionsTwo n, ∑ z ∈ gtPartitionsTwo m,
        gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
          gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] *
            gtEval q u 4 (gtMixedFourRow p.1 p.2 z.1 z.2) := by
  rw [← gtMixed_four]
  simp [gtBiCoeff, gtMixedFourSeries]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixed_four_of_last_one
#print axioms VOA.DeligneAudit.D4Char.gtEval_congr_variables
#print axioms VOA.DeligneAudit.D4Char.gtMixedRankKernel_congr_variables
#print axioms VOA.DeligneAudit.D4Char.gtMixed_four
#print axioms VOA.DeligneAudit.D4Char.gtMixed_four_coeff
