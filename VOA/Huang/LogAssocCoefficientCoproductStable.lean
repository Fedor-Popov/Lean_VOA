import VOA.Huang.LogAssocCoefficientCoproduct
import VOA.Huang.LogAssocCoefficientBounds

/-! The actual coefficient span is stable under every genuine P(1) mode
and lower truncated, using proved generalized-module support bounds. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCoproduct
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.PzTensorRho
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A true supported functional annihilates every sufficiently negative
outside mode, uniformly in the module input. -/
theorem exists_comp_mode_vanish_below {N : LogVModule W M} {f : M →ₗ[ℂ] ℂ} {β : ℂ}
    (hf : SupportedAt N f β) {d : ℤ} {u : V} (hu : u∈W.grading d) :
    ∃ Q : ℤ,∀ q : ℤ,q ≤ Q → f ∘ₗ mode (N.YM u) q=0 := by
  obtain ⟨B,hB⟩ := N.boundedBelow
  obtain ⟨Q,hQ⟩ := exists_int_lt (B-(β-d+1).re)
  refine ⟨Q,fun q hq => eq_zero_of_supportedAt_bot (supportedAt_comp_mode hf hu q) ?_⟩
  by_contra hne
  have hb := hB (β-d+q+1) hne
  have hq' : (q : ℝ) ≤ Q := by exact_mod_cast hq
  simp only [Complex.add_re,Complex.sub_re,Complex.intCast_re,Complex.one_re] at hQ hb
  linarith

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- The span of literal coefficients with actual homogeneous outside data. -/
noncomputable def coefficientSpan : Submodule ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) :=
  Submodule.span ℂ {b | ∃ (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ),
    SupportedAt N₄ f β ∧ z∈N₃.weight c ∧
    b=coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k}

theorem coefficient_mem_span (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k ∈
      coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ :=
  Submodule.subset_span ⟨f,z,c,β,γ,k,hf,hz,rfl⟩

/-- The genuine coproduct preserves the actual coefficient span. -/
theorem coefficientSpan_rho_stable {d : ℤ} {u : V} (hu : u∈W.grading d) (p : ℤ)
    {b : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hb : b∈coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :
    rhoL N₁.toWeakModule N₂.toWeakModule u p b ∈
      coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ := by
  let S := coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  change rhoL N₁.toWeakModule N₂.toWeakModule u p b∈S
  refine Submodule.span_induction (p := fun b _ => rhoL N₁.toWeakModule N₂.toWeakModule u p b∈S)
    ?_ ?_ ?_ ?_ hb
  · rintro b ⟨f,z,c,β,γ,k,hf,hz,rfl⟩
    obtain ⟨NA,hA⟩ := exists_comp_mode_vanish hf hu p
    obtain ⟨NZ,hZ⟩ := exists_nat_truncation N₃ u z
    rw [coefficient_coproduct hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ hu p f z c β γ k hA hZ]
    refine S.sub_mem (S.sum_mem fun i _ => S.smul_mem _ ?_) (S.smul_mem _ (S.sum_mem fun i _ => S.smul_mem _ ?_))
    · exact coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ _ _ _ _ _ _ (supportedAt_comp_mode hf hu (p-i)) hz
    · exact coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ _ _ _ _ _ _ hf (by simpa only [Int.cast_natCast] using N₃.mode_mem_weight hu hz (i : ℤ))
  · dsimp only
    rw [map_zero]
    exact S.zero_mem
  · intro x y _ _ hx hy
    dsimp only
    rw [map_add]
    exact S.add_mem hx hy
  · intro s x _ hx
    dsimp only
    rw [map_smul]
    exact S.smul_mem s hx

/-- The actual homogeneous contragredient twist also preserves the span. -/
theorem coefficientSpan_tau_stable {d : ℤ} {u : V} (hu : u∈W.grading d) (n : ℤ)
    {b : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hb : b∈coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :
    tauHat N₁.toWeakModule N₂.toWeakModule d u n b ∈
      coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ := by
  unfold tauHat
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact coefficientSpan_rho_stable hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ (VertexOperatorAlgebra.L_one_pow_mem W hu j) _ hb

/-- Actual support and the global collision exponent bound give genuine
lower truncation on each literal coefficient functional. -/
theorem coefficient_truncated (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d) :
    TruncAt N₁.toWeakModule N₂.toWeakModule u
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k) := by
  obtain ⟨Q,hQ⟩ := exists_comp_mode_vanish_below hf hu
  obtain ⟨NZ,hZ⟩ := exists_nat_truncation N₃ u z
  obtain ⟨K,M,hB⟩ := exists_coefficient_bounds hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  obtain ⟨P,hP⟩ := exists_int_lt (M-γ.re-c.re-β.re)
  refine ⟨min Q P,fun p hp => ?_⟩
  have hA : ∀ i : ℕ,0  ≤  i → f ∘ₗ mode (N₄.YM u) (p-i)=0 :=
    fun i _ => hQ _ (by have := min_le_left Q P; omega)
  rw [coefficient_coproduct hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ hu p f z c β γ k hA hZ]
  simp only [Finset.range_zero,Finset.sum_empty,zero_sub,neg_eq_zero]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i hi
  rw [hB _ _ _ f (by simpa only [Int.cast_natCast] using N₃.mode_mem_weight hu hz (i : ℤ))
    hf _ k (Or.inr ?_),smul_zero]
  have hp' : (p : ℝ) ≤ P := by exact_mod_cast le_trans hp (min_le_right Q P)
  have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  simp only [Complex.add_re,Complex.sub_re,Complex.intCast_re,Complex.one_re,Complex.natCast_re]
  linarith

/-- Lower truncation persists under finite linear combinations. -/
theorem coefficientSpan_truncated {d : ℤ} {u : V} (hu : u∈W.grading d)
    {b : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hb : b∈coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :
    TruncAt N₁.toWeakModule N₂.toWeakModule u b := by
  refine Submodule.span_induction (p := fun b _ => TruncAt N₁.toWeakModule N₂.toWeakModule u b)
    ?_ ?_ ?_ ?_ hb
  · rintro b ⟨f,z,c,β,γ,k,hf,hz,rfl⟩
    exact coefficient_truncated hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      f z c β γ k hf hz hu
  · exact ⟨0,fun p hp => map_zero _⟩
  · rintro x y _ _ ⟨P,hP⟩ ⟨Q,hQ⟩
    refine ⟨min P Q,fun p hp => ?_⟩
    rw [map_add,hP _ (le_trans hp (min_le_left P Q)),hQ _ (le_trans hp (min_le_right P Q)),add_zero]
  · rintro s x _ ⟨P,hP⟩
    refine ⟨P,fun p hp => ?_⟩
    rw [map_smul,hP p hp,smul_zero]

end VOA.Huang.LogAssocCoefficientCoproduct
