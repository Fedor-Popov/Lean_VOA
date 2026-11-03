import VOA.Huang.GenusTwoPointSepSpatialWard

/-!
# Finite mode support with the other mode fixed

Weight conservation makes one mode coset finite when the other mode is
fixed. The cutoff is uniform in the varied logarithmic coordinate. This
does not bound the remaining intermediate-mode or q-level sum.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Uniform finite first-mode support follows from algebraic weight support,
even with arbitrary descendants in both insertion slots. -/
theorem productTracePair_weightExp_support_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (b n₂ e : ℂ) :
    ∃ S : Finset ℤ, ∀ j ∉ S, ∀ t : ℂ,
      productTracePair Y₁ Y₂ (b + j) n₂ e (moduleWeightExp P₁.isMod t w₁) w₂ = 0 := by
  classical
  refine FusionTop.induction_weight P₁.isMod w₁ ⟨∅, by simp⟩ ?_ ?_
  · intro x y hx hy
    obtain ⟨S, hS⟩ := hx
    obtain ⟨T, hT⟩ := hy
    refine ⟨S ∪ T, fun j hj t => ?_⟩
    simp only [Finset.mem_union, not_or] at hj
    simp only [map_add, LinearMap.add_apply, hS j hj.1 t, hT j hj.2 t, add_zero]
  · intro α x hx
    refine FusionTop.induction_weight P₂.isMod w₂ ⟨∅, by simp⟩ ?_ ?_
    · intro y z hy hz
      obtain ⟨S, hS⟩ := hy
      obtain ⟨T, hT⟩ := hz
      refine ⟨S ∪ T, fun j hj t => ?_⟩
      simp only [Finset.mem_union, not_or] at hj
      simp only [map_add, hS j hj.1 t, hT j hj.2 t, add_zero]
    · intro β y hy
      have hz (j : ℤ) (h : b + j + n₂ ≠ α + β - 2) (t : ℂ) :
          productTracePair Y₁ Y₂ (b + j) n₂ e (moduleWeightExp P₁.isMod t x) y = 0 := by
        rw [moduleWeightExp_of_weight P₁.isMod t hx, map_smul, LinearMap.smul_apply]
        change Complex.exp (t * α) * productModeTrace Y₁ Y₂ x y (b + j) n₂ e = 0
        rw [productModeTrace_eq_zero Y₁ Y₂ hx hy h e, mul_zero]
      by_cases h : ∃ j : ℤ, b + j + n₂ = α + β - 2
      · obtain ⟨j₀, hj₀⟩ := h
        refine ⟨{j₀}, fun j hj t => hz j (fun he => ?_) t⟩
        apply hj
        apply Finset.mem_singleton.mpr
        apply Int.cast_injective (α := ℂ)
        linear_combination he - hj₀
      · exact ⟨∅, fun j _ t => hz j (fun hj => h ⟨j, hj⟩) t⟩

/-- The same finite support for the actual Huang-modified trace, uniformly
in its first coordinate. No genus-one convergence theorem is assumed. -/
theorem huangModifiedModeTrace_support_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (b n₂ t₂ e : ℂ) :
    ∃ S : Finset ℤ, ∀ j ∉ S, ∀ t : ℂ,
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b + j) n₂ t t₂ e = 0 := by
  obtain ⟨S, hS⟩ := productTracePair_weightExp_support_left Y₁ Y₂
    (huangU P₁ 0 w₁) (huangU P₂ t₂ w₂) b n₂ e
  refine ⟨S, fun j hj t => ?_⟩
  rw [huangModifiedModeTrace_eq]
  have ht : huangU P₁ t w₁ = moduleWeightExp P₁.isMod t (huangU P₁ 0 w₁) := by
    simpa using huangU_add P₁ t 0 w₁
  rw [ht]
  change Complex.exp _ * productTracePair Y₁ Y₂ (b + j) n₂ e _ _ = 0
  rw [hS j hj t, mul_zero]

/-- Huang's spatial derivative law after summing the first mode coset,
with the second mode and traced weight fixed. All sums here are proved
finite. The outer mode and q sums are not covered by this theorem. -/
theorem hasDerivAt_huangModifiedModeTrace_sum_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (b n₂ t₁ t₂ e : ℂ) :
    HasDerivAt
      (fun s => ∑' j : ℤ, huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b + j) n₂ s t₂ e)
      ((Complex.exp logTwoPiI)⁻¹ * ∑' j : ℤ,
        huangModifiedModeTrace Y₁ Y₂ (P₁.isMod.Lm1 w₁) w₂ (b + j) n₂ t₁ t₂ e) t₁ := by
  classical
  let f : ℤ → ℂ → ℂ := fun j s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b + j) n₂ s t₂ e
  obtain ⟨S, hS⟩ := huangModifiedModeTrace_support_left Y₁ Y₂ w₁ w₂ b n₂ t₂ e
  have hz (j : ℤ) (hj : j ∉ S) : f j = 0 := funext (hS j hj)
  have hs (s : ℂ) : (Function.support (fun j => f j s)).Finite :=
    S.finite_toSet.subset fun j hj => by
      by_contra hn
      exact hj (hS j hn s)
  have hd : (Function.support (fun j => _root_.deriv (f j) t₁)).Finite :=
    S.finite_toSet.subset fun j hj => by
      by_contra hn
      exact hj (by dsimp only; rw [hz j hn]; simp)
  have hw : Summable (fun j : ℤ => (b + j + 1) * f j t₁) :=
    summable_of_hasFiniteSupport ((hs t₁).subset fun j hj hzero =>
      hj (by dsimp only at hzero ⊢; rw [hzero, mul_zero]))
  have hsum := (huangModifiedModeTrace_sum_Lm1_left Y₁ Y₂ w₁ w₂ b n₂ t₁ t₂ e
    hw (summable_of_hasFiniteSupport hd)).2
  have he (s : ℂ) : (∑' j, f j s) = ∑ j ∈ S, f j s :=
    tsum_eq_sum fun j hj => hS j hj s
  have hed : (∑' j, _root_.deriv (f j) t₁) = ∑ j ∈ S, _root_.deriv (f j) t₁ :=
    tsum_eq_sum fun j hj => by rw [hz j hj]; simp
  have hf : ∀ j, HasDerivAt (f j) (_root_.deriv (f j) t₁) t₁ := fun j =>
    (hasDerivAt_huangModifiedModeTrace_left Y₁ Y₂ w₁ w₂
      (b + j) n₂ t₁ t₂ e).differentiableAt.hasDerivAt
  have hfinite := HasDerivAt.fun_sum (u := S) (fun j _ => hf j)
  have hvalue : (Complex.exp logTwoPiI)⁻¹ *
      (∑' j : ℤ, huangModifiedModeTrace Y₁ Y₂ (P₁.isMod.Lm1 w₁) w₂
        (b + j) n₂ t₁ t₂ e) = ∑ j ∈ S, _root_.deriv (f j) t₁ := by
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]
    exact hed
  rw [hvalue]
  exact hfinite.congr_of_eventuallyEq (Filter.Eventually.of_forall he)

/-- Uniform finite second-mode support follows from algebraic weight support,
even with arbitrary descendants in both insertion slots. -/
theorem productTracePair_weightExp_support_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ b e : ℂ) :
    ∃ S : Finset ℤ, ∀ j ∉ S, ∀ t : ℂ,
      productTracePair Y₁ Y₂ n₁ (b + j) e w₁ (moduleWeightExp P₂.isMod t w₂) = 0 := by
  classical
  refine FusionTop.induction_weight P₁.isMod w₁ ⟨∅, by simp⟩ ?_ ?_
  · intro x y hx hy
    obtain ⟨S, hS⟩ := hx
    obtain ⟨T, hT⟩ := hy
    refine ⟨S ∪ T, fun j hj t => ?_⟩
    simp only [Finset.mem_union, not_or] at hj
    simp only [map_add, LinearMap.add_apply, hS j hj.1 t, hT j hj.2 t, add_zero]
  · intro α x hx
    refine FusionTop.induction_weight P₂.isMod w₂ ⟨∅, by simp⟩ ?_ ?_
    · intro y z hy hz
      obtain ⟨S, hS⟩ := hy
      obtain ⟨T, hT⟩ := hz
      refine ⟨S ∪ T, fun j hj t => ?_⟩
      simp only [Finset.mem_union, not_or] at hj
      simp only [map_add, hS j hj.1 t, hT j hj.2 t, add_zero]
    · intro β y hy
      have hz (j : ℤ) (h : n₁ + (b + j) ≠ α + β - 2) (t : ℂ) :
          productTracePair Y₁ Y₂ n₁ (b + j) e x (moduleWeightExp P₂.isMod t y) = 0 := by
        rw [moduleWeightExp_of_weight P₂.isMod t hy, map_smul]
        change Complex.exp (t * β) * productModeTrace Y₁ Y₂ x y n₁ (b + j) e = 0
        rw [productModeTrace_eq_zero Y₁ Y₂ hx hy h e, mul_zero]
      by_cases h : ∃ j : ℤ, n₁ + (b + j) = α + β - 2
      · obtain ⟨j₀, hj₀⟩ := h
        refine ⟨{j₀}, fun j hj t => hz j (fun he => ?_) t⟩
        apply hj
        apply Finset.mem_singleton.mpr
        apply Int.cast_injective (α := ℂ)
        linear_combination he - hj₀
      · exact ⟨∅, fun j _ t => hz j (fun hj => h ⟨j, hj⟩) t⟩

/-- The same finite support for the actual Huang-modified trace, uniformly
in its second coordinate. No genus-one convergence theorem is assumed. -/
theorem huangModifiedModeTrace_support_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ b t₁ e : ℂ) :
    ∃ S : Finset ℤ, ∀ j ∉ S, ∀ t : ℂ,
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ (b + j) t₁ t e = 0 := by
  obtain ⟨S, hS⟩ := productTracePair_weightExp_support_right Y₁ Y₂
    (huangU P₁ t₁ w₁) (huangU P₂ 0 w₂) n₁ b e
  refine ⟨S, fun j hj t => ?_⟩
  rw [huangModifiedModeTrace_eq]
  have ht : huangU P₂ t w₂ = moduleWeightExp P₂.isMod t (huangU P₂ 0 w₂) := by
    simpa using huangU_add P₂ t 0 w₂
  rw [ht]
  change Complex.exp _ * productTracePair Y₁ Y₂ n₁ (b + j) e _ _ = 0
  rw [hS j hj t, mul_zero]

/-- Huang's spatial derivative law after summing the second mode coset,
with the first mode and traced weight fixed. All sums here are proved
finite. The outer mode and q sums are not covered by this theorem. -/
theorem hasDerivAt_huangModifiedModeTrace_sum_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ b t₁ t₂ e : ℂ) :
    HasDerivAt
      (fun s => ∑' j : ℤ, huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ (b + j) t₁ s e)
      ((Complex.exp logTwoPiI)⁻¹ * ∑' j : ℤ,
        huangModifiedModeTrace Y₁ Y₂ w₁ (P₂.isMod.Lm1 w₂) n₁ (b + j) t₁ t₂ e) t₂ := by
  classical
  let f : ℤ → ℂ → ℂ := fun j s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ (b + j) t₁ s e
  obtain ⟨S, hS⟩ := huangModifiedModeTrace_support_right Y₁ Y₂ w₁ w₂ n₁ b t₁ e
  have hz (j : ℤ) (hj : j ∉ S) : f j = 0 := funext (hS j hj)
  have hs (s : ℂ) : (Function.support (fun j => f j s)).Finite :=
    S.finite_toSet.subset fun j hj => by
      by_contra hn
      exact hj (hS j hn s)
  have hd : (Function.support (fun j => _root_.deriv (f j) t₂)).Finite :=
    S.finite_toSet.subset fun j hj => by
      by_contra hn
      exact hj (by dsimp only; rw [hz j hn]; simp)
  have hw : Summable (fun j : ℤ => (b + j + 1) * f j t₂) :=
    summable_of_hasFiniteSupport ((hs t₂).subset fun j hj hzero =>
      hj (by dsimp only at hzero ⊢; rw [hzero, mul_zero]))
  have hsum := (huangModifiedModeTrace_sum_Lm1_right Y₁ Y₂ w₁ w₂ n₁ b t₁ t₂ e
    hw (summable_of_hasFiniteSupport hd)).2
  have he (s : ℂ) : (∑' j, f j s) = ∑ j ∈ S, f j s :=
    tsum_eq_sum fun j hj => hS j hj s
  have hed : (∑' j, _root_.deriv (f j) t₂) = ∑ j ∈ S, _root_.deriv (f j) t₂ :=
    tsum_eq_sum fun j hj => by rw [hz j hj]; simp
  have hf : ∀ j, HasDerivAt (f j) (_root_.deriv (f j) t₂) t₂ := fun j =>
    (hasDerivAt_huangModifiedModeTrace_right Y₁ Y₂ w₁ w₂
      n₁ (b + j) t₁ t₂ e).differentiableAt.hasDerivAt
  have hfinite := HasDerivAt.fun_sum (u := S) (fun j _ => hf j)
  have hvalue : (Complex.exp logTwoPiI)⁻¹ *
      (∑' j : ℤ, huangModifiedModeTrace Y₁ Y₂ w₁ (P₂.isMod.Lm1 w₂)
        n₁ (b + j) t₁ t₂ e) = ∑ j ∈ S, _root_.deriv (f j) t₂ := by
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]
    exact hed
  rw [hvalue]
  exact hfinite.congr_of_eventuallyEq (Filter.Eventually.of_forall he)

end VOA.Huang.GenusTwoPoint.Separate
