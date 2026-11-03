import VOA.Huang.GenusOneG1cBCycleOne

/-!
# The B-cycle identity on the complex half-disc

The real-segment identities `reversed_genusOne` and `bcycle_vacuumChannel` continued
analytically (same method as `complex_overlap_of_coeff`: both sides are holomorphic on
`{ε < Re z, ‖z‖ < δ}` by `prodF_differentiableOn` / `iterF_differentiableOn`, and agree on a real
segment) to `{Re z₀ > 0, ‖z₀‖ < δ}`:

* `reversed_genusOne_complex`;
* `bcycle_vacuumChannel_complex`: for `Re z₀ > 0` small,
  `e^{−2πiτα_a} Σ_j prodLift μ_j ν_j (−2πiτ, log(1 + z₀))
     = Σ_z transferMatrix c β x z · Φ_z(z₀) + Σ_{j,k} R_{jk}(z₀)`,
  every `prodLift` absolutely convergent.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion CategoryTheory Complex
open VOA.Huang.GenusTwoPoint (IterateSewingSummable ProductSewingSummable vacuumLW)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]
variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

section Reversed

variable (hV : StronglyRational W) (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
  {β : ∀ x, Fin (c.r x) → ℂ} (hβ : IsTransferScalar F H c β)
  (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject)
  {r : ℕ} (lab' : Fin r → ι)
  (i : ∀ k, famObj D (lab' k) ⟶ tensorObj F (famObj D b) (famObj D a))
  (p : ∀ k, tensorObj F (famObj D b) (famObj D a) ⟶ famObj D (lab' k))
  (htot : ∑ k, p k ≫ i k = 𝟙 _)

include hV hβ htot in
/-- The reversed identity on the complex half-disc. -/
theorem reversed_genusOne_complex (x : ι) (j : Fin (c.r x)) {αb αa : ℂ}
    {wb : (lwOf D b).carrier} {wa : (lwOf D a).carrier}
    (hwb : wb ∈ (lwOf D b).isMod.weight αb) (hwa : wa ∈ (lwOf D a).isMod.weight αa)
    (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      prodF (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j) (muInt F H c x j)
          wb wa αb αa τ (1 + z₀) =
        β x j * iterF (Q := vacuumLW W hv) (N := lwOf D (c.lab x j))
          (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) wb wa αb αa τ z₀ +
        ∑ k, iterF (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
          (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa τ z₀ := by
  obtain ⟨δr, hδr, hrev⟩ := reversed_genusOne F H hV hv c hβ π lab' i p htot x j hwb hwa τ
  have iQ0 : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.simple
  have iL := lwOf_irreducible D (c.lab x j)
  obtain ⟨δ0, hδ0, -, h0⟩ := GenusOneG1b.exists_iterateSewingRadius_holds hV
    (lwOf_irreducible D b) (lwOf_irreducible D a) iL iQ0
    (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) hwb hwa τ
  have hk := fun k => GenusOneG1b.exists_iterateSewingRadius_holds hV
    (lwOf_irreducible D b) (lwOf_irreducible D a) iL (lwOf_irreducible D (lab' k))
    (remOuter F H c x j lab' i k) (remInner F c π lab' p k) hwb hwa τ
  choose δk hδk _ hks using hk
  obtain ⟨δK, hδK, hδKle⟩ := exists_pos_le_fin δk hδk
  have hq0 : 0 ≤ ‖qParam τ‖ := norm_nonneg _
  have hq1 : ‖qParam τ‖ < 1 := norm_qParam_lt_one τ
  set δq : ℝ := (1 - ‖qParam τ‖) / 2 with hδq
  have hδq0 : 0 < δq := by rw [hδq]; linarith
  have hqδ : ‖qParam τ‖ * (1 + δq) < 1 := by rw [hδq]; nlinarith
  set M : ℝ := min (min δr δ0) (min δK δq) with hM
  have hM0 : 0 < M := lt_min (lt_min hδr hδ0) (lt_min hδK hδq0)
  have hMr : M ≤ δr := (min_le_left _ _).trans (min_le_left _ _)
  have hM0' : M ≤ δ0 := (min_le_left _ _).trans (min_le_right _ _)
  have hMK : M ≤ δK := (min_le_right _ _).trans (min_le_left _ _)
  have hMq : M ≤ δq := (min_le_right _ _).trans (min_le_right _ _)
  set ρ : ℝ := 3 * M / 4 with hρ
  have hreal : ∀ t : ℝ, 0 < t → ‖(t : ℂ)‖ = t := fun t ht => by
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hI0 : ∀ z : ℂ, z ≠ 0 → ‖z‖ < δ0 →
      IterateSewingSummable (Q := vacuumLW W hv) (N := lwOf D (c.lab x j))
        (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) wb wa αb αa z 1 τ :=
    fun z hz hzn => h0 z 1 hz one_ne_zero (by rwa [div_one])
  have hIk : ∀ k, ∀ z : ℂ, z ≠ 0 → ‖z‖ < δK →
      IterateSewingSummable (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
        (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa z 1 τ :=
    fun k z hz hzn => hks k z 1 hz one_ne_zero (by rw [div_one]; linarith [hδKle k])
  have hPr : ∀ z : ℂ, 1 < ‖z‖ → ‖z‖ < 1 + δq →
      ProductSewingSummable (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j)
        (muInt F H c x j) wb wa αb αa z 1 τ := by
    intro z h1 h2
    refine GenusOneWard.productSewingSummable_holds _ _ hV (lwOf_irreducible D b)
      (lwOf_irreducible D a) iL hwb hwa one_ne_zero (by rwa [norm_one]) τ ?_
    rw [norm_one]
    have : ‖qParam τ‖ * ‖z‖ ≤ ‖qParam τ‖ * (1 + δq) := mul_le_mul_of_nonneg_left h2.le hq0
    linarith
  refine ⟨M / 2, half_pos hM0, fun z₀ hre hn => ?_⟩
  set ε : ℝ := z₀.re / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hεre : ε < z₀.re := by rw [hε]; linarith
  have hreN : z₀.re ≤ ‖z₀‖ := Complex.re_le_norm z₀
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  set f : ℂ → ℂ := fun z => prodF (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j)
    (muInt F H c x j) wb wa αb αa τ (1 + z) with hf
  set g : ℂ → ℂ := fun z => β x j * iterF (Q := vacuumLW W hv) (N := lwOf D (c.lab x j))
      (moduleIntertwiner (lwOf D (c.lab x j)).isMod) (piInt F π) wb wa αb αa τ z +
    ∑ k, iterF (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
      (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa τ z with hg
  have hUf : halfDisc ε (M / 2) ⊆ sectorAnnulus ε ρ := by
    intro w ⟨hw1, hw2⟩
    simp only [Set.mem_setOf_eq] at hw1
    rw [Metric.mem_ball, dist_zero_right] at hw2
    have := Complex.re_le_norm w
    exact ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp only [Set.mem_setOf_eq]; linarith⟩,
      by simp only [Set.mem_setOf_eq]; linarith⟩
  have hεn : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
  have hρn : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have hdg : DifferentiableOn ℂ g (halfDisc ε (M / 2)) := by
    refine DifferentiableOn.add (DifferentiableOn.const_mul ?_ _) ?_
    · exact (iterF_differentiableOn _ _ _ _ _ _ τ hε0
        (hI0 _ hεn (by rw [hreal ε hε0]; linarith))
        (hI0 _ hρn (by rw [hreal ρ hρ0]; linarith))).mono hUf
    · apply DifferentiableOn.fun_sum
      intro k _
      exact (iterF_differentiableOn _ _ _ _ _ _ τ hε0
        (hIk k _ hεn (by rw [hreal ε hε0]; linarith))
        (hIk k _ hρn (by rw [hreal ρ hρ0]; linarith))).mono hUf
  have hdf : DifferentiableOn ℂ f (halfDisc ε (M / 2)) := by
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
    have hd := prodF_differentiableOn (nuInt F c x j) (muInt F H c x j) wb wa αb αa τ
      (Q := lwOf D x) (N := lwOf D (c.lab x j)) (t₁ := 1 + ε) (t₂ := 1 + ρ) (by linarith)
      (hPr _ (by rw [hreal _ (by linarith)]; linarith) (by rw [hreal _ (by linarith)]; linarith))
      (hPr _ (by rw [hreal _ (by linarith)]; linarith) (by rw [hreal _ (by linarith)]; linarith))
    exact hd.comp ((differentiableOn_const 1).add differentiableOn_id) hmaps
  have hsub : ∀ s : ℝ, ε < s → s < M / 2 → (s : ℂ) ∈ halfDisc ε (M / 2) := by
    intro s h1 h2
    refine ⟨by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact h1, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, hreal s (by linarith)]
    exact h2
  have heq : ∀ s : ℝ, ε < s → s < M / 2 → f s = g s := by
    intro s h1 h2
    have h := hrev s (by linarith) (by linarith)
    have hcast : ((1 + s : ℝ) : ℂ) = 1 + (s : ℂ) := by push_cast; ring
    rw [hcast] at h
    exact h
  have hEq := eqOn_of_real_segment (isOpen_halfDisc ε (M / 2)) (convex_halfDisc ε (M / 2))
    hdf hdg (show ε < M / 2 by linarith) hsub heq
  exact hEq ⟨hεre, by rw [Metric.mem_ball, dist_zero_right]; exact hn⟩

include hV hβ htot in
/-- **The B-cycle of the vacuum channel on the complex half-disc** (Huang Lemma 4.2 (4.11)).
For `Re z₀ > 0` small: the product expansion of `Ψ_x` at the B-translate `ℓ₁ = −2πiτ` of the
near-collision point `(0, log(1 + z₀))`, times `e^{−2πiτα_a}`, equals
`Σ_z transferMatrix c β x z · Φ_z(z₀) + Σ_{j,k} R_{jk}(z₀)`; all product terms converge
absolutely. -/
theorem bcycle_vacuumChannel_complex (x : ι) {αa αb : ℂ} {wa : (lwOf D a).carrier}
    {wb : (lwOf D b).carrier} (hwa : wa ∈ (lwOf D a).isMod.weight αa)
    (hwb : wb ∈ (lwOf D b).isMod.weight αb) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z₀ : ℂ, 0 < z₀.re → ‖z₀‖ < δ →
      (∀ j, Summable (GenusOneWard.liftTerm (Q := lwOf D (c.lab x j)) (N := lwOf D x)
        (muInt F H c x j) (nuInt F c x j) wa wb αa αb (-(2 * (Real.pi : ℂ) * I * τ))
        (log (1 + z₀)) τ)) ∧
      exp (-(2 * (Real.pi : ℂ) * I * τ * αa)) *
          ∑ j, GenusOneWard.prodLift (Q := lwOf D (c.lab x j)) (N := lwOf D x)
            (muInt F H c x j) (nuInt F c x j) wa wb αa αb (-(2 * (Real.pi : ℂ) * I * τ))
            (log (1 + z₀)) τ =
        ∑ z, transferMatrix c β x z * iterF (Q := vacuumLW W hv) (N := lwOf D z)
          (moduleIntertwiner (lwOf D z).isMod) (piInt F π) wb wa αb αa τ z₀ +
        ∑ j, ∑ k, iterF (Q := lwOf D (lab' k)) (N := lwOf D (c.lab x j))
          (remOuter F H c x j lab' i k) (remInner F c π lab' p k) wb wa αb αa τ z₀ := by
  have hj := fun j => reversed_genusOne_complex F H hV hv c hβ π lab' i p htot x j hwb hwa τ
  choose δj hδj hrev using hj
  obtain ⟨δJ, hδJ, hδJle⟩ := exists_pos_le_fin δj hδj
  have him : 0 < (τ : ℂ).im := τ.im_pos
  set E : ℝ := Real.exp (2 * Real.pi * (τ : ℂ).im) - 1 with hE
  have hE0 : 0 < E := by
    rw [hE]; have : 1 < Real.exp (2 * Real.pi * (τ : ℂ).im) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  refine ⟨min δJ E, lt_min hδJ hE0, fun z₀ hre hn => ⟨fun j => ?_, ?_⟩⟩
  · have hnE : ‖z₀‖ < E := lt_of_lt_of_le hn (min_le_right _ _)
    have h1 : 1 < ‖1 + z₀‖ := one_lt_norm_one_add hre
    have h2 : ‖1 + z₀‖ ≤ 1 + ‖z₀‖ := by
      have := norm_add_le (1 : ℂ) z₀; rwa [norm_one] at this
    have hpos : 0 < ‖1 + z₀‖ := by linarith
    have hre1 : (-(2 * (Real.pi : ℂ) * I * τ)).re = 2 * Real.pi * (τ : ℂ).im := by
      simp [Complex.mul_re, Complex.mul_im]
    have hre2 : (log (1 + z₀)).re = Real.log ‖1 + z₀‖ := Complex.log_re _
    refine GenusOneWard.summable_liftTerm _ _ hV (lwOf_irreducible D a) (lwOf_irreducible D b)
      (lwOf_irreducible D x) hwa hwb _ _ τ ?_ ?_
    · rw [hre1, hre2]
      have : ‖1 + z₀‖ < Real.exp (2 * Real.pi * (τ : ℂ).im) := by rw [hE] at hnE; linarith
      have := Real.log_lt_log hpos this
      rwa [Real.log_exp] at this
    · rw [hre1, hre2, Real.exp_log hpos]
      have hq : ‖qParam τ‖ = Real.exp (-(2 * Real.pi * (τ : ℂ).im)) := by
        rw [qParam, Complex.norm_exp]
        congr 1
        simp [Complex.mul_re, Complex.mul_im]
      rw [hq, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
      exact h1
  · have hnJ : ∀ j, ‖z₀‖ < δj j := fun j => lt_of_lt_of_le (lt_of_lt_of_le hn (min_le_left _ _))
      (hδJle j)
    have h1z : (1 + z₀) ≠ 0 := by
      intro h; have := one_lt_norm_one_add hre; rw [h, norm_zero] at this; linarith
    have hB : ∀ j, exp (-(2 * (Real.pi : ℂ) * I * τ * αa)) *
        GenusOneWard.prodLift (Q := lwOf D (c.lab x j)) (N := lwOf D x)
          (muInt F H c x j) (nuInt F c x j) wa wb αa αb (-(2 * (Real.pi : ℂ) * I * τ))
          (log (1 + z₀)) τ =
        prodF (Q := lwOf D x) (N := lwOf D (c.lab x j)) (nuInt F c x j) (muInt F H c x j)
          wb wa αb αa τ (1 + z₀) := by
      intro j
      rw [← GenusOneWard.prodLift_bcycle (muInt F H c x j) (nuInt F c x j) hwa hwb,
        neg_add_cancel, prodLift_log_one _ _ _ _ _ _ τ h1z]
    rw [Finset.mul_sum]
    simp only [hB]
    simp only [fun j => hrev j z₀ hre (hnJ j)]
    rw [Finset.sum_add_distrib]
    congr 1
    exact sum_group_transfer F c β x (fun z => iterF (Q := vacuumLW W hv) (N := lwOf D z)
      (moduleIntertwiner (lwOf D z).isMod) (piInt F π) wb wa αb αa τ z₀)

end Reversed

end VOA.Huang.GenusOneG1c
