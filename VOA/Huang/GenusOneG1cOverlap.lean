import VOA.Huang.GenusOneG1bOverlap
import VOA.Huang.GenusOneG1cAnalytic

/-!
# Genus-one associativity on the COMPLEX overlap

Step (a) of the proof of (G1): the real-segment identity
`GenusOneG1b.genusOne_iterate_eq_product` is continued analytically to the complex domain
`{z₀ : Re z₀ > 0, ‖z₀‖ < δ}` (iterate at `(z₀, z₂ = 1)`, product at `(z₁ = 1 + z₀, z₂ = 1)`).

* `iterF`, `prodF`: the full genus-one double series of the two channels (as functions of the
  free point, the other point at `1`).
* `iterF_differentiableOn`, `prodF_differentiableOn`: both are holomorphic, by
  `differentiableOn_tsum_cpow` (every term is `c_p · z^{e_p}` with `Im e_p` independent of `p`,
  convergence at two real points from `iterateModeGrowth_holds` / `productModeGrowth_holds`).
* `complex_overlap_of_coeff`: for ANY iterate channel and ANY finite family of product channels
  whose fixed-level trace coefficients agree on a real segment `0 < s < δc`, the full genus-one
  double series agree on the complex half-disc, both sides absolutely convergent.
* `genusOne_iterate_eq_product_complex`: the instance for the converse-associativity family.

The general form is what the categorical dictionary (`GenusOneG1cDictionary`) consumes, where the
product family is the one built from `TransferChoice`, not the existential one.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang Complex
open scoped BigOperators
open VOA.Huang.GenusTwoPoint (IterateSewingSummable ProductSewingSummable productTerm
  iterateTerm productCoeff iterateCoeff qFactor
  coefficientAssociativityConverse_of_stronglyRational_pbw)

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The genus-one iterate channel `Tr_N Y₃(Y₄(x, z₀) y, 1) q^{L₀ − c/24}` as a double series. -/
def iterF (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (x : P₁.carrier) (y : P₂.carrier)
    (α₁ α₂ : ℂ) (τ : UpperHalfPlane) (z₀ : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + p.1) z₀ 1 p.2 * qFactor N τ p.1

/-- The genus-one product channel `Tr_N Y₁(x, z₁) Y₂(y, 1) q^{L₀ − c/24}` as a double series. -/
def prodF (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) (x : P₁.carrier) (y : P₂.carrier)
    (α₁ α₂ : ℂ) (τ : UpperHalfPlane) (z₁ : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, productTerm Y₁ Y₂ x y α₁ α₂ (N.h + p.1) z₁ 1 p.2 * qFactor N τ p.1

section Terms

variable (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
  (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
  (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
  (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (τ : UpperHalfPlane)

/-- Iterate exponent of `z₀`. -/
def iterE (p : ℕ × ℕ) : ℂ := -((α₁ + α₂ - 1 - Q.h) - p.2) - 1

/-- Product exponent of `z₁`. -/
def prodE (p : ℕ × ℕ) : ℂ := -((α₁ + α₂ - 2) - (α₂ + (N.h + p.1) - 1 - Q.h) + p.2) - 1

theorem iterateTerm_eq_cpow (z₀ : ℂ) (p : ℕ × ℕ) :
    iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + p.1) z₀ 1 p.2 * qFactor N τ p.1 =
      (iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + p.1) 1 1 p.2 * qFactor N τ p.1) *
        z₀ ^ iterE (Q := Q) α₁ α₂ p := by
  unfold iterateTerm iterE
  simp only [Complex.one_cpow]
  ring

theorem productTerm_eq_cpow (z₁ : ℂ) (p : ℕ × ℕ) :
    productTerm Y₁ Y₂ x y α₁ α₂ (N.h + p.1) z₁ 1 p.2 * qFactor N τ p.1 =
      (productTerm Y₁ Y₂ x y α₁ α₂ (N.h + p.1) 1 1 p.2 * qFactor N τ p.1) *
        z₁ ^ prodE (Q := Q) (N := N) α₁ α₂ p := by
  unfold productTerm prodE
  simp only [Complex.one_cpow]
  ring

theorem iterE_im (p : ℕ × ℕ) :
    (iterE (Q := Q) α₁ α₂ p).im = (iterE (Q := Q) α₁ α₂ (0, 0)).im := by
  simp [iterE]

theorem prodE_im (p : ℕ × ℕ) :
    (prodE (Q := Q) (N := N) α₁ α₂ p).im = (prodE (Q := Q) (N := N) α₁ α₂ (0, 0)).im := by
  simp [prodE]

theorem iterF_eq (z₀ : ℂ) : iterF Y₃ Y₄ x y α₁ α₂ τ z₀ =
    ∑' p : ℕ × ℕ, (iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + p.1) 1 1 p.2 * qFactor N τ p.1) *
      z₀ ^ iterE (Q := Q) α₁ α₂ p :=
  tsum_congr fun p => iterateTerm_eq_cpow Y₃ Y₄ x y α₁ α₂ τ z₀ p

theorem prodF_eq (z₁ : ℂ) : prodF Y₁ Y₂ x y α₁ α₂ τ z₁ =
    ∑' p : ℕ × ℕ, (productTerm Y₁ Y₂ x y α₁ α₂ (N.h + p.1) 1 1 p.2 * qFactor N τ p.1) *
      z₁ ^ prodE (Q := Q) (N := N) α₁ α₂ p :=
  tsum_congr fun p => productTerm_eq_cpow Y₁ Y₂ x y α₁ α₂ τ z₁ p

/-- Holomorphy of the iterate channel from sewing convergence at two real points. -/
theorem iterF_differentiableOn {t₁ t₂ : ℝ} (ht₁ : 0 < t₁)
    (h₁ : IterateSewingSummable Y₃ Y₄ x y α₁ α₂ (t₁ : ℂ) 1 τ)
    (h₂ : IterateSewingSummable Y₃ Y₄ x y α₁ α₂ (t₂ : ℂ) 1 τ) :
    DifferentiableOn ℂ (iterF Y₃ Y₄ x y α₁ α₂ τ) (sectorAnnulus t₁ t₂) := by
  have hf : iterF Y₃ Y₄ x y α₁ α₂ τ = fun w => ∑' p : ℕ × ℕ,
      (iterateTerm Y₃ Y₄ x y α₁ α₂ (N.h + p.1) 1 1 p.2 * qFactor N τ p.1) *
        w ^ iterE (Q := Q) α₁ α₂ p := funext (iterF_eq Y₃ Y₄ x y α₁ α₂ τ)
  rw [hf]
  refine differentiableOn_tsum_cpow _ _ _ (iterE_im α₁ α₂) ht₁ ?_ ?_
  · exact h₁.congr fun p => iterateTerm_eq_cpow Y₃ Y₄ x y α₁ α₂ τ _ p
  · exact h₂.congr fun p => iterateTerm_eq_cpow Y₃ Y₄ x y α₁ α₂ τ _ p

/-- Holomorphy of the product channel from sewing convergence at two real points. -/
theorem prodF_differentiableOn {t₁ t₂ : ℝ} (ht₁ : 0 < t₁)
    (h₁ : ProductSewingSummable Y₁ Y₂ x y α₁ α₂ (t₁ : ℂ) 1 τ)
    (h₂ : ProductSewingSummable Y₁ Y₂ x y α₁ α₂ (t₂ : ℂ) 1 τ) :
    DifferentiableOn ℂ (prodF Y₁ Y₂ x y α₁ α₂ τ) (sectorAnnulus t₁ t₂) := by
  have hf : prodF Y₁ Y₂ x y α₁ α₂ τ = fun w => ∑' p : ℕ × ℕ,
      (productTerm Y₁ Y₂ x y α₁ α₂ (N.h + p.1) 1 1 p.2 * qFactor N τ p.1) *
        w ^ prodE (Q := Q) (N := N) α₁ α₂ p := funext (prodF_eq Y₁ Y₂ x y α₁ α₂ τ)
  rw [hf]
  refine differentiableOn_tsum_cpow _ _ _ (prodE_im α₁ α₂) ht₁ ?_ ?_
  · exact h₁.congr fun p => productTerm_eq_cpow Y₁ Y₂ x y α₁ α₂ τ _ p
  · exact h₂.congr fun p => productTerm_eq_cpow Y₁ Y₂ x y α₁ α₂ τ _ p

end Terms

/-- The open convex domain `{ε < Re z, ‖z‖ < δ}`. -/
def halfDisc (ε δ : ℝ) : Set ℂ := {w | ε < w.re} ∩ Metric.ball 0 δ

theorem isOpen_halfDisc (ε δ : ℝ) : IsOpen (halfDisc ε δ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball

theorem convex_halfDisc (ε δ : ℝ) : Convex ℝ (halfDisc ε δ) :=
  (convex_halfSpace_re_gt ε).inter (convex_ball 0 δ)

theorem one_lt_norm_one_add {z : ℂ} (hz : 0 < z.re) : 1 < ‖1 + z‖ := by
  have h := Complex.re_le_norm (1 + z)
  simp only [Complex.add_re, Complex.one_re] at h
  linarith

/-- **Complex overlap from a real coefficient identity.** For any iterate channel `(Y₃, Y₄)` and
any finite family of product channels `(Y₁ʲ, Y₂ʲ)` (all with irreducible external modules), if the
fixed-level trace coefficients agree on a real segment, then the full genus-one double series agree
on the complex half-disc `{Re z₀ > 0, ‖z₀‖ < δ}`, both sides absolutely convergent there. -/
theorem complex_overlap_of_coeff (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : Q.IsIrreducibleLW) {r : ℕ} {R : Fin r → LWModule W}
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
    (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (τ : UpperHalfPlane)
    (hcoef : ∃ δc : ℝ, 0 < δc ∧ ∀ s : ℝ, 0 < s → s < δc → ∀ n : ℕ,
      iterateCoeff Y₃ Y₄ x y α₁ α₂ (N.h + n) (s : ℂ) 1 =
        ∑ j, productCoeff (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n) ((1 + s : ℝ) : ℂ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      IterateSewingSummable Y₃ Y₄ x y α₁ α₂ z₀ 1 τ ∧
      (∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ (1 + z₀) 1 τ) ∧
      iterF Y₃ Y₄ x y α₁ α₂ τ z₀ = ∑ j, prodF (Y₁ j) (Y₂ j) x y α₁ α₂ τ (1 + z₀) := by
  obtain ⟨δc, hδc, hc⟩ := hcoef
  obtain ⟨δi, hδi, -, hit⟩ :=
    GenusOneG1b.exists_iterateSewingRadius_holds hV i₁ i₂ iN iQ Y₃ Y₄ hx hy τ
  obtain ⟨δo, hδo, -, hov⟩ :=
    GenusOneG1b.overlap_summable hV i₁ i₂ iN iQ Y₃ Y₄ Y₁ Y₂ hx hy τ
  have hq1 : ‖qParam τ‖ < 1 := norm_qParam_lt_one τ
  have hq0 : 0 ≤ ‖qParam τ‖ := norm_nonneg _
  set δq : ℝ := (1 - ‖qParam τ‖) / 2 with hδq
  have hδq0 : 0 < δq := by rw [hδq]; linarith
  have hqδ : ‖qParam τ‖ * (1 + δq) < 1 := by rw [hδq]; nlinarith
  set M : ℝ := min (min δi δq) (min δo δc) with hM
  have hM0 : 0 < M := lt_min (lt_min hδi hδq0) (lt_min hδo hδc)
  have hMi : M ≤ δi := (min_le_left _ _).trans (min_le_left _ _)
  have hMq : M ≤ δq := (min_le_left _ _).trans (min_le_right _ _)
  have hMo : M ≤ δo := (min_le_right _ _).trans (min_le_left _ _)
  have hMc : M ≤ δc := (min_le_right _ _).trans (min_le_right _ _)
  set ρ : ℝ := 3 * M / 4 with hρ
  -- iterate summability at any nonzero point of norm `< δi`
  have hIt : ∀ z : ℂ, z ≠ 0 → ‖z‖ < δi → IterateSewingSummable Y₃ Y₄ x y α₁ α₂ z 1 τ :=
    fun z hz hzn => hit z 1 hz one_ne_zero (by rwa [div_one])
  -- product summability at any point with `1 < ‖z₁‖ < 1 + δq`
  have hPr : ∀ j, ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < 1 + δq →
      ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ z 1 τ := by
    intro j z h1 h2
    refine GenusOneWard.productSewingSummable_holds (Y₁ j) (Y₂ j) hV i₁ i₂ iN hx hy
      one_ne_zero (by rwa [norm_one]) τ ?_
    rw [norm_one]
    have : ‖qParam τ‖ * ‖z‖ ≤ ‖qParam τ‖ * (1 + δq) :=
      mul_le_mul_of_nonneg_left h2.le hq0
    linarith
  refine ⟨M / 2, half_pos hM0, fun z₀ hre hn => ?_⟩
  have hz0 : z₀ ≠ 0 := fun h => by simp [h] at hre
  have hnorm1 : ‖1 + z₀‖ ≤ 1 + ‖z₀‖ := by
    have := norm_add_le (1 : ℂ) z₀; rwa [norm_one] at this
  have hsumI : IterateSewingSummable Y₃ Y₄ x y α₁ α₂ z₀ 1 τ := hIt z₀ hz0 (by linarith)
  have hsumP : ∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ (1 + z₀) 1 τ :=
    fun j => hPr j _ (one_lt_norm_one_add hre) (by linarith)
  refine ⟨hsumI, hsumP, ?_⟩
  -- analytic continuation on `halfDisc ε (M/2)`, `ε = Re z₀ / 2`
  set ε : ℝ := z₀.re / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hεre : ε < z₀.re := by rw [hε]; linarith
  have hreN : z₀.re ≤ ‖z₀‖ := Complex.re_le_norm z₀
  have hρM : M / 2 < ρ := by rw [hρ]; linarith
  have hρi : ρ < δi := by rw [hρ]; linarith
  have hρq : ρ ≤ δq := by rw [hρ]; linarith
  have hreal : ∀ t : ℝ, 0 < t → ‖(t : ℂ)‖ = t := fun t ht => by
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
  set f : ℂ → ℂ := iterF Y₃ Y₄ x y α₁ α₂ τ with hf
  set g : ℂ → ℂ := fun z => ∑ j, prodF (Y₁ j) (Y₂ j) x y α₁ α₂ τ (1 + z) with hg
  have hUf : halfDisc ε (M / 2) ⊆ sectorAnnulus ε ρ := by
    intro w ⟨hw1, hw2⟩
    simp only [Set.mem_setOf_eq] at hw1
    rw [Metric.mem_ball, dist_zero_right] at hw2
    have := Complex.re_le_norm w
    exact ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp only [Set.mem_setOf_eq]; linarith⟩,
      by simp only [Set.mem_setOf_eq]; linarith⟩
  have hdf : DifferentiableOn ℂ f (halfDisc ε (M / 2)) := by
    refine (iterF_differentiableOn Y₃ Y₄ x y α₁ α₂ τ hε0 ?_ ?_).mono hUf
    · exact hIt _ (by exact_mod_cast hε0.ne') (by rw [hreal ε hε0]; linarith)
    · have hρ0 : 0 < ρ := by rw [hρ]; linarith
      exact hIt _ (by exact_mod_cast hρ0.ne') (by rw [hreal ρ hρ0]; linarith)
  have hdg : DifferentiableOn ℂ g (halfDisc ε (M / 2)) := by
    apply DifferentiableOn.fun_sum
    intro j _
    have hmaps : Set.MapsTo (fun z : ℂ => 1 + z) (halfDisc ε (M / 2))
        (sectorAnnulus (1 + ε) (1 + ρ)) := by
      intro w ⟨hw1, hw2⟩
      simp only [Set.mem_setOf_eq] at hw1
      rw [Metric.mem_ball, dist_zero_right] at hw2
      have h1 := Complex.re_le_norm (1 + w)
      have h2 : ‖1 + w‖ ≤ 1 + ‖w‖ := by
        have := norm_add_le (1 : ℂ) w; rwa [norm_one] at this
      simp only [Complex.add_re, Complex.one_re] at h1
      exact ⟨⟨by simp only [Set.mem_setOf_eq, Complex.add_re, Complex.one_re]; linarith,
        by simp only [Set.mem_setOf_eq]; linarith⟩, by simp only [Set.mem_setOf_eq]; linarith⟩
    have hd := prodF_differentiableOn (Y₁ j) (Y₂ j) x y α₁ α₂ τ (t₁ := 1 + ε) (t₂ := 1 + ρ)
      (by linarith)
      (hPr j _ (by rw [hreal _ (by linarith)]; linarith) (by rw [hreal _ (by linarith)]; linarith))
      (hPr j _ (by rw [hreal _ (by linarith)]; linarith) (by rw [hreal _ (by linarith)]; linarith))
    exact hd.comp ((differentiableOn_const 1).add differentiableOn_id) hmaps
  have hsub : ∀ s : ℝ, ε < s → s < M / 2 → (s : ℂ) ∈ halfDisc ε (M / 2) := by
    intro s h1 h2
    refine ⟨by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact h1, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, hreal s (by linarith)]
    exact h2
  have heq : ∀ s : ℝ, ε < s → s < M / 2 → f s = g s := by
    intro s h1 h2
    have hs0 : 0 < s := by linarith
    obtain ⟨hI, hP⟩ := hov s hs0 (by linarith)
    have h := GenusOneG1b.overlap_identity Y₃ Y₄ Y₁ Y₂ α₁ α₂ x y _ _ _ τ hI hP
      (hc s hs0 (by linarith))
    have hcast : ((1 + s : ℝ) : ℂ) = 1 + (s : ℂ) := by push_cast; ring
    rw [hcast] at h
    exact h
  have hEq := eqOn_of_real_segment (isOpen_halfDisc ε (M / 2)) (convex_halfDisc ε (M / 2))
    hdf hdg (show ε < M / 2 by linarith) hsub heq
  exact hEq ⟨hεre, by rw [Metric.mem_ball, dist_zero_right]; exact hn⟩

/-- **Genus-one associativity on the complex overlap** (step (a)): the converse-associativity
family of `GenusOneG1b.genusOne_iterate_eq_product`, with the identity continued from the real
segment to `{Re z₀ > 0, ‖z₀‖ < δ}`. -/
theorem genusOne_iterate_eq_product_complex (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) :
    ∃ (r : ℕ) (R : Fin r → LWModule W), (∀ j, (R j).IsIrreducibleLW) ∧
      ∃ (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
        (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod),
      ∀ (α₁ α₂ : ℂ) (x : P₁.carrier) (y : P₂.carrier),
        x ∈ P₁.isMod.weight α₁ → y ∈ P₂.isMod.weight α₂ → ∀ τ : UpperHalfPlane,
        ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
          IterateSewingSummable Y₃ Y₄ x y α₁ α₂ z₀ 1 τ ∧
          (∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ (1 + z₀) 1 τ) ∧
          iterF Y₃ Y₄ x y α₁ α₂ τ z₀ = ∑ j, prodF (Y₁ j) (Y₂ j) x y α₁ α₂ τ (1 + z₀) := by
  obtain ⟨r, R, iR, Y₁, Y₂, heq⟩ :=
    coefficientAssociativityConverse_of_stronglyRational_pbw hV P₁ P₂ N Q i₁ i₂ iN iQ Y₃ Y₄
  refine ⟨r, R, iR, Y₁, Y₂, fun α₁ α₂ x y hx hy τ => ?_⟩
  refine complex_overlap_of_coeff hV i₁ i₂ iN iQ Y₃ Y₄ Y₁ Y₂ hx hy τ ⟨1, one_pos, ?_⟩
  intro s hs0 hs1 n
  have h := heq α₁ α₂ x y hx hy (N.h + n) (1 + s) 1 (by linarith) (by linarith)
  have h01 : ((1 + s : ℝ) : ℂ) - ((1 : ℝ) : ℂ) = (s : ℂ) := by push_cast; ring
  rw [h01, Complex.ofReal_one] at h
  exact h

end VOA.Huang.GenusOneG1c
