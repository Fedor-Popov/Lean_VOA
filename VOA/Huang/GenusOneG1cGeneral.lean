import VOA.Huang.GenusOneG1cBCycleOne

/-!
# From a genus-zero four-point identity to a genus-one identity (general form)

Two reusable bridges for any finite linear relation between product and iterate channels with
common external modules `P₁, P₂` and common traced module `N`:

* `coeff_of_fourPoint`: a four-point identity `Σ_j c_j ⟨f, Y₁ʲ(x, 1+t) Y₂ʲ(y, 1) w⟩ =
  Σ_k d_k ⟨f, Y₃ᵏ(Y₄ᵏ(x, t) y, 1) w⟩` for every test implies the same identity for every
  fixed-weight trace coefficient (real `0 < s < 1`);
* `genusOne_of_coeff`: such a coefficient identity on a real segment implies the identity of the
  full genus-one functions `Σ_j c_j prodF_j (1 + z₀) = Σ_k d_k iterF_k z₀` on the complex
  half-disc `{Re z₀ > 0, ‖z₀‖ < δ}`, all channels absolutely convergent.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang VOA.Huang.AssocTarget Complex
open VOA.Huang.GenusTwoPoint (IterateSewingSummable ProductSewingSummable productTerm
  iterateTerm productCoeff iterateCoeff qFactor weightFunctional
  supportedAt_weightFunctional iterateCoeff_eq_sum_iterValue productCoeff_eq_sum_prodValue
  summable_iterate_q_of_sewing productQSummable_of_sewing)
open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N : LWModule W}

section Families

variable {r₁ r₂ : ℕ} {R : Fin r₁ → LWModule W} {Q : Fin r₂ → LWModule W}
  (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
  (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod)
  (Y₃ : ∀ k, IntertwiningOperator (Q k).isMod N.isMod N.isMod)
  (Y₄ : ∀ k, IntertwiningOperator P₁.isMod P₂.isMod (Q k).isMod)
  (cP : Fin r₁ → ℂ) (cI : Fin r₂ → ℂ)

/-- A four-point identity gives the trace-coefficient identity. -/
theorem coeff_of_fourPoint (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (h4 : ∀ d : AssocConverse.TestData P₁ P₂ N N,
      ∑ j, cP j * AssocConverse.productValue (Y₁ j) (Y₂ j) d =
        ∑ k, cI k * AssocConverse.iterateValue (Y₃ k) (Y₄ k) d)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (β : ℂ) (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ∑ j, cP j * productCoeff (Y₁ j) (Y₂ j) x y α₁ α₂ β ((1 + s : ℝ) : ℂ) 1 =
      ∑ k, cI k * iterateCoeff (Y₃ k) (Y₄ k) x y α₁ α₂ β (s : ℂ) 1 := by
  classical
  letI := N.isMod.finrank β
  let bs := Module.finBasis ℂ (N.isMod.weight β)
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℂ)‖ < ‖(1 : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_one]; exact hs1
  have hpn : ‖(1 : ℂ)‖ < ‖((1 + s : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_one]; linarith
  simp_rw [productCoeff_eq_sum_prodValue hV i₁ i₂ iN _ _ hx hy β bs one_ne_zero hpn,
    iterateCoeff_eq_sum_iterValue hV i₁ i₂ iN _ _ hx hy β bs hs0' hsn, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun k t => cI k * iterValue (Y₃ k).val (Y₄ k).val _ x y _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro t _
  let d : AssocConverse.TestData P₁ P₂ N N :=
    ⟨α₁, α₂, β, β, x, y, bs t, weightFunctional N.isMod β bs t, hx, hy,
      (bs t).property, supportedAt_weightFunctional N.isMod β bs t, s, hs0, hs1⟩
  have h := h4 d
  simp only [iterateValue_eq_iterValue, productValue_eq_prodValue] at h
  have hσ : α₁ + α₂ + β - β - 2 = α₁ + α₂ - 2 := by ring
  have hcast : ((1 + s : ℝ) : ℂ) = 1 + (s : ℂ) := by push_cast; ring
  rw [hcast]
  simpa only [d, hσ] using h

/-- **Genus-one identity on the complex half-disc from a real coefficient identity.** -/
theorem genusOne_of_coeff (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : ∀ k, (Q k).IsIrreducibleLW)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (τ : UpperHalfPlane)
    (hcoef : ∃ δc : ℝ, 0 < δc ∧ ∀ s : ℝ, 0 < s → s < δc → ∀ n : ℕ,
      ∑ j, cP j * productCoeff (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n) ((1 + s : ℝ) : ℂ) 1 =
        ∑ k, cI k * iterateCoeff (Y₃ k) (Y₄ k) x y α₁ α₂ (N.h + n) (s : ℂ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      (∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ (1 + z₀) 1 τ) ∧
      (∀ k, IterateSewingSummable (Y₃ k) (Y₄ k) x y α₁ α₂ z₀ 1 τ) ∧
      ∑ j, cP j * prodF (Y₁ j) (Y₂ j) x y α₁ α₂ τ (1 + z₀) =
        ∑ k, cI k * iterF (Y₃ k) (Y₄ k) x y α₁ α₂ τ z₀ := by
  obtain ⟨δc, hδc, hc⟩ := hcoef
  have hk := fun k => GenusOneG1b.exists_iterateSewingRadius_holds hV i₁ i₂ iN (iQ k)
    (Y₃ k) (Y₄ k) hx hy τ
  choose δk hδk _ hks using hk
  obtain ⟨δK, hδK, hδKle⟩ := exists_pos_le_fin δk hδk
  have hq0 : 0 ≤ ‖qParam τ‖ := norm_nonneg _
  have hq1 : ‖qParam τ‖ < 1 := norm_qParam_lt_one τ
  set δq : ℝ := (1 - ‖qParam τ‖) / 2 with hδq
  have hδq0 : 0 < δq := by rw [hδq]; linarith
  have hqδ : ‖qParam τ‖ * (1 + δq) < 1 := by rw [hδq]; nlinarith
  set M : ℝ := min (min δc δK) δq with hM
  have hM0 : 0 < M := lt_min (lt_min hδc hδK) hδq0
  have hMc : M ≤ δc := (min_le_left _ _).trans (min_le_left _ _)
  have hMK : M ≤ δK := (min_le_left _ _).trans (min_le_right _ _)
  have hMq : M ≤ δq := min_le_right _ _
  set ρ : ℝ := 3 * M / 4 with hρ
  have hreal : ∀ t : ℝ, 0 < t → ‖(t : ℂ)‖ = t := fun t ht => by
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hIt : ∀ k, ∀ z : ℂ, z ≠ 0 → ‖z‖ < δK →
      IterateSewingSummable (Y₃ k) (Y₄ k) x y α₁ α₂ z 1 τ :=
    fun k z hz hzn => hks k z 1 hz one_ne_zero (by rw [div_one]; linarith [hδKle k])
  have hPr : ∀ j, ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < 1 + δq →
      ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ z 1 τ := by
    intro j z h1 h2
    refine GenusOneWard.productSewingSummable_holds (Y₁ j) (Y₂ j) hV i₁ i₂ iN hx hy
      one_ne_zero (by rwa [norm_one]) τ ?_
    rw [norm_one]
    have : ‖qParam τ‖ * ‖z‖ ≤ ‖qParam τ‖ * (1 + δq) := mul_le_mul_of_nonneg_left h2.le hq0
    linarith
  -- the real identity
  have hreal_id : ∀ s : ℝ, 0 < s → s < M →
      ∑ j, cP j * prodF (Y₁ j) (Y₂ j) x y α₁ α₂ τ (1 + (s : ℂ)) =
        ∑ k, cI k * iterF (Y₃ k) (Y₄ k) x y α₁ α₂ τ (s : ℂ) := by
    intro s hs0 hs
    have hcast : 1 + (s : ℂ) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    have hn1 : ‖((1 + s : ℝ) : ℂ)‖ = 1 + s := hreal _ (by linarith)
    have hP : ∀ j, ProductSewingSummable (Y₁ j) (Y₂ j) x y α₁ α₂ ((1 + s : ℝ) : ℂ) 1 τ :=
      fun j => hPr j _ (by rw [hn1]; linarith) (by rw [hn1]; linarith)
    have hI : ∀ k, IterateSewingSummable (Y₃ k) (Y₄ k) x y α₁ α₂ (s : ℂ) 1 τ :=
      fun k => hIt k _ (by exact_mod_cast hs0.ne') (by rw [hreal s hs0]; linarith)
    have hPq : ∀ j, prodF (Y₁ j) (Y₂ j) x y α₁ α₂ τ ((1 + s : ℝ) : ℂ) =
        ∑' n : ℕ, productCoeff (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n) ((1 + s : ℝ) : ℂ) 1 *
          qFactor N τ n := fun j =>
      GenusOneG1b.tsum_pair_eq (f := fun n k => productTerm (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n)
        ((1 + s : ℝ) : ℂ) 1 k) (g := qFactor N τ) (hP j)
    have hIq : ∀ k, iterF (Y₃ k) (Y₄ k) x y α₁ α₂ τ (s : ℂ) =
        ∑' n : ℕ, iterateCoeff (Y₃ k) (Y₄ k) x y α₁ α₂ (N.h + n) (s : ℂ) 1 *
          qFactor N τ n := fun k =>
      GenusOneG1b.tsum_pair_eq (f := fun n m => iterateTerm (Y₃ k) (Y₄ k) x y α₁ α₂ (N.h + n)
        (s : ℂ) 1 m) (g := qFactor N τ) (hI k)
    have hSP := fun j => productQSummable_of_sewing _ _ _ _ _ _ _ _ τ (hP j)
    have hSI := fun k => summable_iterate_q_of_sewing _ _ _ _ _ _ _ _ τ (hI k)
    rw [hcast]
    simp only [hPq, hIq]
    rw [show (∑ j, cP j * ∑' n : ℕ, productCoeff (Y₁ j) (Y₂ j) x y α₁ α₂ (N.h + n)
        ((1 + s : ℝ) : ℂ) 1 * qFactor N τ n) = ∑' n : ℕ, (∑ j, cP j * productCoeff (Y₁ j) (Y₂ j)
          x y α₁ α₂ (N.h + n) ((1 + s : ℝ) : ℂ) 1) * qFactor N τ n by
      simp only [Finset.sum_mul, mul_assoc]
      rw [Summable.tsum_finsetSum fun j _ => (hSP j).mul_left (cP j)]
      exact Finset.sum_congr rfl fun j _ => (tsum_mul_left).symm,
      show (∑ k, cI k * ∑' n : ℕ, iterateCoeff (Y₃ k) (Y₄ k) x y α₁ α₂ (N.h + n)
        (s : ℂ) 1 * qFactor N τ n) = ∑' n : ℕ, (∑ k, cI k * iterateCoeff (Y₃ k) (Y₄ k)
          x y α₁ α₂ (N.h + n) (s : ℂ) 1) * qFactor N τ n by
      simp only [Finset.sum_mul, mul_assoc]
      rw [Summable.tsum_finsetSum fun k _ => (hSI k).mul_left (cI k)]
      exact Finset.sum_congr rfl fun k _ => (tsum_mul_left).symm]
    exact tsum_congr fun n => by rw [hc s hs0 (by linarith) n]
  refine ⟨M / 2, half_pos hM0, fun z₀ hre hn => ?_⟩
  have hz0 : z₀ ≠ 0 := fun h => by simp [h] at hre
  have hnorm1 : ‖1 + z₀‖ ≤ 1 + ‖z₀‖ := by
    have := norm_add_le (1 : ℂ) z₀; rwa [norm_one] at this
  refine ⟨fun j => hPr j _ (one_lt_norm_one_add hre) (by linarith),
    fun k => hIt k _ hz0 (by linarith), ?_⟩
  set ε : ℝ := z₀.re / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hεre : ε < z₀.re := by rw [hε]; linarith
  have hreN : z₀.re ≤ ‖z₀‖ := Complex.re_le_norm z₀
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hεn : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
  have hρn : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  set f : ℂ → ℂ := fun z => ∑ j, cP j * prodF (Y₁ j) (Y₂ j) x y α₁ α₂ τ (1 + z) with hf
  set g : ℂ → ℂ := fun z => ∑ k, cI k * iterF (Y₃ k) (Y₄ k) x y α₁ α₂ τ z with hg
  have hUf : halfDisc ε (M / 2) ⊆ sectorAnnulus ε ρ := by
    intro w ⟨hw1, hw2⟩
    simp only [Set.mem_setOf_eq] at hw1
    rw [Metric.mem_ball, dist_zero_right] at hw2
    have := Complex.re_le_norm w
    exact ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp only [Set.mem_setOf_eq]; linarith⟩,
      by simp only [Set.mem_setOf_eq]; linarith⟩
  have hdg : DifferentiableOn ℂ g (halfDisc ε (M / 2)) := by
    apply DifferentiableOn.fun_sum
    intro k _
    exact ((iterF_differentiableOn _ _ _ _ _ _ τ hε0
      (hIt k _ hεn (by rw [hreal ε hε0]; linarith))
      (hIt k _ hρn (by rw [hreal ρ hρ0]; linarith))).mono hUf).const_mul _
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
  have hdf : DifferentiableOn ℂ f (halfDisc ε (M / 2)) := by
    apply DifferentiableOn.fun_sum
    intro j _
    have hd := prodF_differentiableOn (Y₁ j) (Y₂ j) x y α₁ α₂ τ (t₁ := 1 + ε) (t₂ := 1 + ρ)
      (by linarith)
      (hPr j _ (by rw [hreal _ (by linarith)]; linarith) (by rw [hreal _ (by linarith)]; linarith))
      (hPr j _ (by rw [hreal _ (by linarith)]; linarith) (by rw [hreal _ (by linarith)]; linarith))
    exact (hd.comp ((differentiableOn_const 1).add differentiableOn_id) hmaps).const_mul _
  have hsub : ∀ s : ℝ, ε < s → s < M / 2 → (s : ℂ) ∈ halfDisc ε (M / 2) := by
    intro s h1 h2
    refine ⟨by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact h1, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, hreal s (by linarith)]
    exact h2
  have heq : ∀ s : ℝ, ε < s → s < M / 2 → f s = g s :=
    fun s h1 h2 => hreal_id s (by linarith) (by linarith)
  have hEq := eqOn_of_real_segment (isOpen_halfDisc ε (M / 2)) (convex_halfDisc ε (M / 2))
    hdf hdg (show ε < M / 2 by linarith) hsub heq
  exact hEq ⟨hεre, by rw [Metric.mem_ball, dist_zero_right]; exact hn⟩

end Families

end VOA.Huang.GenusOneG1c
