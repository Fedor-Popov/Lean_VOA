import VOA.Huang.GenusOneG1bIterateGrowth

/-!
# Genus-one associativity on the real overlap

`genusOne_iterate_eq_product`: for strongly rational `W`, an iterate channel
`(Y₃, Y₄)` and the finite family of product channels `(Y₁ʲ, Y₂ʲ)` supplied by converse
associativity, at every `τ` there is `δ > 0` such that for real `0 < s < δ` the FULL genus-one
double series agree:

  `Σ_{n,k} iterate(n,k; z₀ = s, z₂ = 1) q-factor = Σ_j Σ_{n,k} product_j(n,k; z₁ = 1+s, z₂ = 1) q-factor`,

both sides absolutely convergent (`IterateSewingSummable`, `ProductSewingSummable`). This is
the genus-one product ↔ iterate identification on the overlap of the two sewing regions
(the first half of step 2 of the G1 programme); it is coefficientwise converse associativity
summed over the traced level, legitimate because of the uniform growth proved in
`iterateModeGrowth_holds` and `productModeGrowth_holds`.
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open VOA VOA.Huang
open scoped BigOperators
open VOA.Huang.GenusTwoPoint (IterateSewingSummable ProductSewingSummable productTerm
  iterateTerm productCoeff iterateCoeff qFactor coefficientAssociativityConverse_of_stronglyRational_pbw)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- A joint double sum is the outer sum of the inner `k`-sums. -/
theorem tsum_pair_eq {f : ℕ → ℕ → ℂ} {g : ℕ → ℂ}
    (h : Summable fun p : ℕ × ℕ => f p.1 p.2 * g p.1) :
    ∑' p : ℕ × ℕ, f p.1 p.2 * g p.1 = ∑' n, (∑' k, f n k) * g n := by
  rw [h.tsum_prod]
  exact tsum_congr fun n => by
    change ∑' k, f n k * g n = _
    exact tsum_mul_right

/-- Summing coefficientwise associativity over the traced level. -/
theorem overlap_identity {r : ℕ} {R : Fin r → LWModule W}
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
    (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod)
    (α₁ α₂ : ℂ) (x : P₁.carrier) (y : P₂.carrier) (z₀ z₁ z₂ : ℂ) (τ : UpperHalfPlane)
    (hIt : IterateSewingSummable Y₃ Y₄ x y α₁ α₂ z₀ z₂ τ)
    (hPr : ∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ z₁ z₂ τ)
    (hcoef : ∀ n : ℕ, iterateCoeff Y₃ Y₄ x y α₁ α₂ (N.h + n) z₀ z₂ =
      ∑ j, productCoeff (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n) z₁ z₂) :
    ∑' p : ℕ × ℕ, iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + p.1) z₀ z₂ p.2 * qFactor N τ p.1 =
      ∑ j, ∑' p : ℕ × ℕ, productTerm (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + p.1) z₁ z₂ p.2 *
        qFactor N τ p.1 := by
  rw [tsum_pair_eq (f := fun n k => iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + n) z₀ z₂ k)
    (g := qFactor N τ) hIt]
  have hP : ∀ j, ∑' p : ℕ × ℕ, productTerm (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + p.1) z₁ z₂ p.2 *
      qFactor N τ p.1 = ∑' n : ℕ, productCoeff (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n) z₁ z₂ *
        qFactor N τ n := fun j =>
    tsum_pair_eq (f := fun n k => productTerm (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n) z₁ z₂ k)
      (g := qFactor N τ) (hPr j)
  simp only [hP]
  change ∑' n : ℕ, iterateCoeff Y₃ Y₄ x y α₁ α₂ (N.h + n) z₀ z₂ * qFactor N τ n = _
  simp only [hcoef, Finset.sum_mul]
  rw [Summable.tsum_finsetSum]
  intro j _
  exact GenusTwoPoint.productQSummable_of_sewing _ _ _ _ _ _ _ _ _ (hPr j)

/-- The two sewing summabilities on a small real overlap. -/
theorem overlap_summable (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : Q.IsIrreducibleLW) {r : ℕ} {R : Fin r → LWModule W}
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
    (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ s : ℝ, 0 < s → s < δ →
      IterateSewingSummable Y₃ Y₄ x y α₁ α₂ (s : ℂ) 1 τ ∧
      ∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ ((1 + s : ℝ) : ℂ) 1 τ := by
  obtain ⟨δ₁, hδ₁, -, hit⟩ := exists_iterateSewingRadius_holds hV i₁ i₂ iN iQ Y₃ Y₄ hx hy τ
  have hq1 : ‖qParam τ‖ < 1 := norm_qParam_lt_one τ
  have hq0 : 0 ≤ ‖qParam τ‖ := norm_nonneg _
  set δ₂ : ℝ := (1 - ‖qParam τ‖) / 2 with hδ₂
  have hδ₂0 : 0 < δ₂ := by rw [hδ₂]; linarith
  refine ⟨min (min δ₁ δ₂) (1 / 2), lt_min (lt_min hδ₁ hδ₂0) (by norm_num), min_le_right _ _,
    fun s hs0 hs => ⟨?_, fun j => ?_⟩⟩
  · have hsδ₁ : s < δ₁ := lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_left _ _))
    refine hit (s : ℂ) 1 (by exact_mod_cast hs0.ne') one_ne_zero ?_
    rw [div_one, Complex.norm_real, Real.norm_of_nonneg hs0.le]; exact hsδ₁
  · have hsδ₂ : s < δ₂ := lt_of_lt_of_le hs ((min_le_left _ _).trans (min_le_right _ _))
    have hnorm1 : ‖((1 + s : ℝ) : ℂ)‖ = 1 + s := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    refine GenusOneWard.productSewingSummable_holds (Y₁ j) (Y₂ j) hV i₁ i₂ iN hx hy
      one_ne_zero ?_ τ ?_
    · rw [norm_one, hnorm1]; linarith
    · rw [norm_one, hnorm1]
      have h1 : ‖qParam τ‖ * (1 + s) ≤ ‖qParam τ‖ * (1 + δ₂) :=
        mul_le_mul_of_nonneg_left (by linarith) hq0
      have h2 : ‖qParam τ‖ * (1 + δ₂) < 1 := by rw [hδ₂]; nlinarith
      linarith

/-- **Genus-one associativity on the real overlap.** -/
theorem genusOne_iterate_eq_product (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) :
    ∃ (r : ℕ) (R : Fin r → LWModule W), (∀ j, (R j).IsIrreducibleLW) ∧
      ∃ (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
        (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod),
      ∀ (α₁ α₂ : ℂ) (x : P₁.carrier) (y : P₂.carrier),
        x ∈ P₁.isMod.weight α₁ → y ∈ P₂.isMod.weight α₂ → ∀ τ : UpperHalfPlane,
        ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
          IterateSewingSummable Y₃ Y₄ x y α₁ α₂ (s : ℂ) 1 τ ∧
          (∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ ((1 + s : ℝ) : ℂ) 1 τ) ∧
          ∑' p : ℕ × ℕ, iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + p.1) (s : ℂ) 1 p.2 *
              qFactor N τ p.1 =
            ∑ j, ∑' p : ℕ × ℕ, productTerm (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + p.1)
              ((1 + s : ℝ) : ℂ) 1 p.2 * qFactor N τ p.1 := by
  obtain ⟨r, R, iR, Y₁, Y₂, heq⟩ :=
    coefficientAssociativityConverse_of_stronglyRational_pbw hV P₁ P₂ N Q i₁ i₂ iN iQ Y₃ Y₄
  refine ⟨r, R, iR, Y₁, Y₂, fun α₁ α₂ x y hx hy τ => ?_⟩
  obtain ⟨δ, hδ, hδ2, hsum⟩ := overlap_summable hV i₁ i₂ iN iQ Y₃ Y₄ Y₁ Y₂ hx hy τ
  refine ⟨δ, hδ, fun s hs0 hs => ?_⟩
  obtain ⟨hIt, hPr⟩ := hsum s hs0 hs
  refine ⟨hIt, hPr, overlap_identity Y₃ Y₄ Y₁ Y₂ α₁ α₂ x y _ _ _ τ hIt hPr fun n => ?_⟩
  have h := heq α₁ α₂ x y hx hy (N.h + n) (1 + s) 1 (by linarith) (by linarith)
  have h01 : ((1 + s : ℝ) : ℂ) - ((1 : ℝ) : ℂ) = (s : ℂ) := by push_cast; ring
  rw [h01, Complex.ofReal_one] at h
  exact h

end VOA.Huang.GenusOneG1b
