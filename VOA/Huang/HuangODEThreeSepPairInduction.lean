import VOA.Huang.HuangODEThreeSepPairMoves
import VOA.Huang.HuangODEThreeSepInduction

/-!
# The five-slot induction and the inner equation for the pair (blow-up) chart

`pairSeries_mem` (Huang's Prop. 1.1/2.1 for the pair shape
`f(𝒴_P(p) (𝒴_{XY}(r) x y) (𝒴_{ZT}(q) z t))`) and
`innerRegular_pairSeries`: the coefficient array of every normalized pair series
satisfies a monic Euler equation in the second chart variable (`y = z₀/z₃`, the collision of
the pair `x, y`) with coefficients in `pairRing`, all of whose elements are bounded on every
admissible polydisc (`MidBound`).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop PowerSeries VOA.Huang.HuangODEThree
open VOA.Huang.HuangODEProduct VOA.Huang.HuangODEModes
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {AU : OrdVModule W MU} {AV : OrdVModule W MV}
variable {P : IntertwiningModes MU MV M₀} {ZT : IntertwiningModes M₂ M₁ MV}
  {XY : IntertwiningModes M₃ M₄ MU}

section Induction

variable {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {B₀ B₁ B₂ B₃ B₄ : ℕ}

/-- **Prop. 1.1 with regularity for the pair chart.** -/
theorem pairSeries_mem
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    (hD₀ : DualC1Graded A₀ h₀ B₀) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hC₄ : C1Graded A₄ h₄ B₄)
    (NN : Submodule pairRing PS2)
    (hbase : ∀ (N₀ N₁ N₂ N₃ N₄ : ℕ), N₀ ≤ B₀ → N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN) :
    ∀ (s N₀ N₁ N₂ N₃ N₄ : ℕ), N₀ + N₁ + N₂ + N₃ + N₄ = s →
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
  intro N₀ N₁ N₂ N₃ N₄ hs f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
  have IH' : ∀ (N₀ N₁ N₂ N₃ N₄ : ℕ), N₀ + N₁ + N₂ + N₃ + N₄ < s →
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN :=
    fun N₀ N₁ N₂ N₃ N₄ hlt f w₁ w₂ w₃ w₄ h1 h2 h3 h4 =>
      IH _ hlt N₀ N₁ N₂ N₃ N₄ rfl f w₁ w₂ w₃ w₄ h1 h2 h3 h4
  subst hs
  -- slot `t`
  by_cases c1 : B₁ < N₁
  · refine Submodule.span_induction
      (p := fun x _ => normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY
        (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f x w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hC₁ N₁ c1 w₁ hw₁)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₀ + N₁ + N₂ + N₃ + N₄ = N₀ + ((N₁ - d) + d) + N₂ + N₃ + N₄ by omega,
        pairSeries_terminal hP hZT hXY hl₀ hl₂ hl₃ hl₄ hB hu f hw' hw₂ hw₃ hw₄]
      refine NN.sub_mem (NN.sub_mem (NN.sub_mem ?_ ?_) ?_) ?_
      · split_ifs with hd
        · exact mul_mem_of_sub NN (pair_monomial_mem _ _)
            (IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw' hw₂ hw₃ hw₄)
        · exact NN.zero_mem
      · refine NN.sum_mem fun k hk => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw' hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hk)
      · refine NN.sum_mem fun l hl => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_ιxy_binom_mem l) ?_)
        simp only [Finset.mem_range] at hl
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw' hw₂ (mode_mem_weight_nat hu hw₃ hl) hw₄
      · refine NN.sum_mem fun k hk => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw' (mode_mem_weight_nat hu hw₂ hk) hw₃ hw₄
    · simp only []; rw [ns_zero_w₁]; exact NN.zero_mem
    · intro x y _ _ hx hy; rw [ns_add_w₁]; exact NN.add_mem hx hy
    · intro a x _ hx; rw [ns_smul_w₁]; exact smul_mem_of_sub NN a hx
  -- slot `z`
  by_cases c2' : B₂ < N₂
  · refine Submodule.span_induction
      (p := fun x _ => normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY
        (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ x w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hC₂ N₂ c2' w₂ hw₂)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₀ + N₁ + N₂ + N₃ + N₄ = N₀ + N₁ + ((N₂ - d) + d) + N₃ + N₄ by omega,
        pairSeries_two hP hZT hXY hl₀ hl₁ hl₃ hl₄ hB hu f hw₁ hw' hw₃ hw₄]
      refine NN.sub_mem (NN.sub_mem (NN.add_mem ?_ ?_) ?_) ?_
      · refine NN.sum_mem fun i hi => mul_mem_of_sub NN (pair_monomial_mem _ _) ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw' hw₃ hw₄
      · refine NN.sum_mem fun i hi => mul_mem_of_sub NN (pair_monomial_mem _ _) ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ (mode_mem_weight_nat hu hw₁ hi) hw' hw₃ hw₄
      · refine NN.sum_mem fun k hk => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_ιx_binom_mem k)
            (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_))
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw' hw₃ (mode_mem_weight_nat hu hw₄ hk)
      · refine NN.sum_mem fun l hl => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_monomial_mem _ _)
            (mul_mem_of_sub NN (pair_ιm'_geom_pow_mem _) ?_))
        simp only [Finset.mem_range] at hl
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw' (mode_mem_weight_nat hu hw₃ hl) hw₄
    · simp only []; rw [ns_zero_w₂]; exact NN.zero_mem
    · intro x y _ _ hx hy; rw [ns_add_w₂]; exact NN.add_mem hx hy
    · intro a x _ hx; rw [ns_smul_w₂]; exact smul_mem_of_sub NN a hx
  -- slot `x`
  by_cases c3 : B₃ < N₃
  · refine Submodule.span_induction
      (p := fun x _ => normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY
        (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ x w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hC₃ N₃ c3 w₃ hw₃)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₀ + N₁ + N₂ + N₃ + N₄ = N₀ + N₁ + N₂ + ((N₃ - d) + d) + N₄ by omega,
        pairSeries_three hP hZT hXY hl₀ hl₁ hl₂ hl₄ hB hu f hw₁ hw₂ hw' hw₄]
      refine NN.add_mem (NN.add_mem (NN.add_mem ?_ ?_) ?_) ?_
      · refine NN.sum_mem fun i hi => NN.sum_mem fun j hj => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_)
        simp only [Finset.mem_range] at hi hj
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw₂ hw' hw₄
      · refine NN.sum_mem fun j hj => mul_mem_of_sub NN (pair_ιxy_binom_mem j) ?_
        simp only [Finset.mem_range] at hj
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ (mode_mem_weight_nat hu hw₁ hj) hw₂ hw' hw₄
      · refine NN.sum_mem fun k hk => mul_mem_of_sub NN (pair_monomial_mem _ _)
          (mul_mem_of_sub NN (pair_ιm'_geom_pow_mem _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ (mode_mem_weight_nat hu hw₂ hk) hw' hw₄
      · refine NN.sum_mem fun i hi => ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw₂ hw' (mode_mem_weight_nat hu hw₄ hi)
    · simp only []; rw [ns_zero_w₃]; exact NN.zero_mem
    · intro x y _ _ hx hy; rw [ns_add_w₃]; exact NN.add_mem hx hy
    · intro a x _ hx; rw [ns_smul_w₃]; exact smul_mem_of_sub NN a hx
  -- slot `y`
  by_cases c4 : B₄ < N₄
  · refine Submodule.span_induction
      (p := fun x _ => normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY
        (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
        f w₁ w₂ w₃ x N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hC₄ N₄ c4 w₄ hw₄)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₀ + N₁ + N₂ + N₃ + N₄ = N₀ + N₁ + N₂ + N₃ + ((N₄ - d) + d) by omega,
        pairSeries_four hP hZT hXY hl₀ hl₁ hl₂ hl₃ hB hu f hw₁ hw₂ hw₃ hw']
      refine NN.sub_mem (NN.add_mem (NN.add_mem ?_ ?_) ?_) ?_
      · refine NN.sum_mem fun i hi => mul_mem_of_sub NN (pair_monomial_mem _ _) ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw₂ hw₃ hw'
      · refine NN.sum_mem fun i hi => mul_mem_of_sub NN (pair_monomial_mem _ _) ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ (mode_mem_weight_nat hu hw₁ hi) hw₂ hw₃ hw'
      · refine NN.sum_mem fun k hk => mul_mem_of_sub NN (pair_ιx_binom_mem k)
          (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ (mode_mem_weight_nat hu hw₂ hk) hw₃ hw'
      · refine NN.sum_mem fun k hk => smul_mem_of_sub NN _ ?_
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw₂ (mode_mem_weight_nat hu hw₃ hk) hw'
    · simp only []; rw [ns_zero_w₄]; exact NN.zero_mem
    · intro x y _ _ hx hy; rw [ns_add_w₄]; exact NN.add_mem hx hy
    · intro a x _ hx; rw [ns_smul_w₄]; exact smul_mem_of_sub NN a hx
  -- output functional
  by_cases c0 : B₀ < N₀
  · refine Submodule.span_induction
      (p := fun φ _ => ∀ f' : M₀ →ₗ[ℂ] ℂ, f'.domRestrict (A₀.weight (h₀ + N₀)) = φ →
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f' w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hD₀ N₀ c0 f) f rfl
    · rintro φ ⟨d, m, u, g, hd1, hm, hmN, hu, rfl⟩ f' hf'
      rw [pairSeries_congr_f hP hZT hXY hw₁ hw₂ hw₃ hw₄ hf']
      obtain ⟨j, rfl⟩ : ∃ j, m = 2 * d - 1 + j := ⟨m - (2 * d - 1), by omega⟩
      obtain ⟨r, rfl⟩ : ∃ r, N₀ = r + d + j := ⟨N₀ - (d + j), by omega⟩
      have hmz : (((2 * d - 1 + j : ℕ) : ℤ)) = 2 * (d : ℤ) - 1 + j := by
        rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
      rw [hmz, pairSeries_dual hP hZT hXY hl₁ hl₂ hl₃ hl₄ hB hd1 hu g j hw₁ hw₂ hw₃ hw₄]
      refine NN.add_mem (NN.add_mem (NN.add_mem ?_ ?_) ?_) ?_
      · split_ifs with h1
        · refine mul_mem_of_sub NN (pair_monomial_mem _ _)
            (IH' _ _ _ _ _ (by omega) _ _ _ _ _ ?_ hw₂ hw₃ hw₄)
          have hm1 := mode_mem_weight A₁ hu hw₁ (2 * (d : ℤ) - 1 + j)
          convert hm1 using 2
          rw [Nat.cast_sub h1]; push_cast; ring
        · exact NN.zero_mem
      · refine NN.sum_mem fun k hk => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ (mode_mem_weight_nat hu hw₂ hk) hw₃ hw₄
      · refine NN.sum_mem fun k hk => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw₂ hw₃ (mode_mem_weight_nat hu hw₄ hk)
      · refine NN.sum_mem fun k hk => NN.sum_mem fun l hl => smul_mem_of_sub NN _
          (mul_mem_of_sub NN (pair_monomial_mem _ _) ?_)
        simp only [Finset.mem_range] at hk hl
        exact IH' _ _ _ _ _ (by omega) _ _ _ _ _ hw₁ hw₂ (mode_mem_weight_nat hu hw₃ hl) hw₄
    · intro f' hf'
      rw [pairSeries_congr_f hP hZT hXY hw₁ hw₂ hw₃ hw₄ (g := 0) (by rw [hf']; ext; simp),
        ns_zero_f]
      exact NN.zero_mem
    · intro φ₁ φ₂ _ _ h1 h2 f' hf'
      obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend φ₁
      have hsplit : f' = g₁ + (f' - g₁) := by abel
      rw [hsplit, ns_add_f]
      refine NN.add_mem (h1 g₁ hg₁) (h2 _ ?_)
      ext x
      have hx := LinearMap.congr_fun hf' x
      have hx1 := LinearMap.congr_fun hg₁ x
      simp only [LinearMap.domRestrict_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, Submodule.subtype_apply] at hx hx1 ⊢
      rw [hx, hx1]; ring
    · intro a φ _ h1 f' hf'
      obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend φ
      rw [pairSeries_congr_f hP hZT hXY hw₁ hw₂ hw₃ hw₄ (g := a • g₁) (by
        rw [hf']; ext x
        have hx1 := LinearMap.congr_fun hg₁ x
        simp only [LinearMap.domRestrict_apply, LinearMap.smul_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx1 ⊢
        rw [hx1]), ns_smul_f]
      exact smul_mem_of_sub NN a (h1 g₁ hg₁)
  exact hbase N₀ N₁ N₂ N₃ N₄ (by omega) (by omega) (by omega) (by omega) (by omega)
    f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄

end Induction

/-- **The inner regular equation for the pair chart.** Every normalized pair series
satisfies, for every `λ`, a monic Euler equation in the second chart variable with
coefficients in `pairRing`, bounded on every admissible polydisc (`InnerRegularMid`). -/
theorem innerRegular_pairSeries
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {B₀ B₁ B₂ B₃ B₄ : ℕ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    (hD₀ : DualC1Graded A₀ h₀ B₀) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hC₄ : C1Graded A₄ h₄ B₄)
    {N₀ N₁ N₂ N₃ N₄ : ℕ} (f : M₀ →ₗ[ℂ] ℂ) {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) (lam : ℂ) :
    InnerRegularMid lam (c2 (normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY
      (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄))) := by
  classical
  obtain ⟨S, hSfin, hS⟩ := exists_finite_span_pair_box hP hZT hXY
    h₀ h₁ h₂ h₃ h₄ ν μ B₀ B₁ B₂ B₃ B₄
  set NN : Submodule pairRing PS2 := Submodule.span pairRing S
  have hFG : NN.FG := Submodule.fg_span hSfin
  have hle : Submodule.span ℂ S ≤ NN.restrictScalars ℂ :=
    Submodule.span_le_restrictScalars ℂ pairRing S
  have hall := pairSeries_mem hP hZT hXY hl₀ hl₁ hl₂ hl₃ hl₄ hB hD₀ hC₁ hC₂ hC₃ hC₄ NN
    (fun N₀ N₁ N₂ N₃ N₄ b₀ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ w₄ h1 h2 h3 h4 =>
      hle (hS N₀ N₁ N₂ N₃ N₄ b₀ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ w₄ h1 h2 h3 h4))
  set Q : ℕ → PS2 := fun j =>
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ ((⇑A₃.Lm1)^[j] w₃) w₄ N₀ (N₀ + N₁ + N₂ + (N₃ + j) + N₄) with hQdef
  have hQmem : ∀ j, Q j ∈ NN := fun j =>
    hall _ N₀ N₁ N₂ (N₃ + j) N₄ rfl f w₁ w₂ _ w₄ hw₁ hw₂ (Lm1_iterate_mem_weight hw₃ j) hw₄
  have hQ : ∀ j, Q (j + 1) =
      thetaY (-(μ + ((N₀ + N₁ + N₂ + (N₃ + j) + N₄ : ℕ) : ℂ) + 1)) (Q j) := by
    intro j
    simp only [hQdef]
    rw [Function.iterate_succ_apply', show N₀ + N₁ + N₂ + (N₃ + (j + 1)) + N₄ =
      N₀ + N₁ + N₂ + (N₃ + j) + N₄ + 1 by ring, normalizedSeries_Lm1_third hXY]
  have hθ := thetaY_iter_mem_sub NN Q _ hQ hQmem 0
  have hQ0 : Q 0 = normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY
      (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) := by
    simp [hQdef]
  rw [← hQ0]
  exact innerRegularAdm_of_fg (fun r hr => midBound_of_mem_pairRing hr) NN hFG (μ := 0)
    (fun j => hθ j 0) lam

end VOA.Huang.FivePointSep
