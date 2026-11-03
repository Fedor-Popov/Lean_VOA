import VOA.Huang.GenusTwoPointTrace

/-!
# Convergence of each fixed-weight two-point trace coefficient

Huang's genus-zero convergence is applied to a finite basis of the traced weight
space. This proves the inner mode sums converge, without asserting convergence
of the subsequent q-series. All powers use the library's principal branch.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Module MatrixCoeff AssocTarget
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Summand at intermediate level k, with the traced weight β held fixed. -/
noncomputable def productTerm (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ β z₁ z₂ : ℂ) (k : ℕ) : ℂ :=
  productModeTrace Y₁ Y₂ w₁ w₂
    ((α₁ + α₂ - 2) - (α₂ + β - 1 - Q.h) + k) ((α₂ + β - 1 - Q.h) - k)
    (β - W.centralCharge / 24) *
      z₁ ^ (-((α₁ + α₂ - 2) - (α₂ + β - 1 - Q.h) + k) - 1) *
      z₂ ^ (-((α₂ + β - 1 - Q.h) - k) - 1)

/-- The corresponding iterate summand. Its inner base is independent of β. -/
noncomputable def iterateTerm (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ β z₀ z₂ : ℂ) (k : ℕ) : ℂ :=
  iterateModeTrace Y₃ Y₄ w₁ w₂ ((α₁ + α₂ - 1 - Q.h) - k)
    ((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k) (β - W.centralCharge / 24) *
      z₂ ^ (-((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k) - 1) *
      z₀ ^ (-((α₁ + α₂ - 1 - Q.h) - k) - 1)

noncomputable def productCoeff (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ β z₁ z₂ : ℂ) : ℂ :=
  ∑' k, productTerm Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂ k

noncomputable def iterateCoeff (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ β z₀ z₂ : ℂ) : ℂ :=
  ∑' k, iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ β z₀ z₂ k

/-- The canonical intermediate-level indexing omits no nonzero mode coefficients. -/
theorem productModeTrace_eq_zero_of_off_coset
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) {α₂ : ℂ} {w₂ : P₂.carrier}
    (h₂ : w₂ ∈ P₂.isMod.weight α₂) (β n₁ n₂ : ℂ)
    (hn : ∀ k : ℕ, n₂ ≠ α₂ + β - 1 - Q.h - k) :
    productModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ (β - W.centralCharge / 24) = 0 := by
  classical
  letI := N.isMod.finrank β
  let b := Module.finBasis ℂ (N.isMod.weight β)
  rw [productModeTrace_eq_sum Y₁ Y₂ w₁ w₂ n₁ n₂ β b]
  apply Finset.sum_eq_zero
  intro i _
  have hv : Y₂.val n₂ w₂ (b i) = 0 := by
    have hm := FusionTop.mem_weight Y₂.property h₂ (b i).property n₂
    by_contra hne
    have hb : Q.isMod.weight (α₂ + β - n₂ - 1) ≠ ⊥ := by
      intro hb
      rw [hb, Submodule.mem_bot] at hm
      exact hne hm
    obtain ⟨k, hk⟩ := Q.isLow _ hb
    apply hn k
    linear_combination -hk
  simp only [prodCoeff, hv, map_zero]

/-- Convergence at one traced weight, with no sewing estimate assumed. -/
theorem summable_productTerm (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (β : ℂ) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    Summable (productTerm Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂) := by
  classical
  letI := N.isMod.finrank β
  let b := Module.finBasis ℂ (N.isMod.weight β)
  have hs := fun i => summable_prodValue hV i₁ i₂ iN iN Y₁.property Y₂.property
    h₁ h₂ (b i).property (supportedAt_weightFunctional N.isMod β b i) hz₂ hz
  simp only [add_sub_cancel_right] at hs
  convert (summable_sum fun i (_ : i ∈ Finset.univ) => hs i) using 1
  funext k
  simp only [productTerm, productModeTrace_eq_sum Y₁ Y₂ w₁ w₂ _ _ β b,
    Finset.sum_mul]

/-- Iterate convergence at one traced weight. -/
theorem summable_iterateTerm (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (β : ℂ) {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz : ‖z₀‖ < ‖z₂‖) :
    Summable (iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ β z₀ z₂) := by
  classical
  letI := N.isMod.finrank β
  let b := Module.finBasis ℂ (N.isMod.weight β)
  have hs := fun i => summable_iterValue hV i₁ i₂ iN iN Y₃.property Y₄.property
    h₁ h₂ (b i).property (supportedAt_weightFunctional N.isMod β b i) hz₀ hz
  simp only [add_sub_cancel_right] at hs
  convert (summable_sum fun i (_ : i ∈ Finset.univ) => hs i) using 1
  funext k
  simp only [iterateTerm, iterateModeTrace_eq_sum Y₃ Y₄ w₁ w₂ _ _ β b,
    Finset.sum_mul]

theorem productCoeff_eq_sum_prodValue {ι : Type*} [Fintype ι]
    (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (β : ℂ) (b : Basis ι ℂ (N.isMod.weight β))
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂ =
      ∑ i, prodValue Y₁.val Y₂.val (weightFunctional N.isMod β b i)
        w₁ w₂ (b i) (α₁ + α₂ - 2) (α₂ + β - 1 - Q.h) z₁ z₂ := by
  have hs := fun i => summable_prodValue hV i₁ i₂ iN iN Y₁.property Y₂.property
    h₁ h₂ (b i).property (supportedAt_weightFunctional N.isMod β b i) hz₂ hz
  simp only [add_sub_cancel_right] at hs
  simp only [productCoeff, productTerm,
    productModeTrace_eq_sum Y₁ Y₂ w₁ w₂ _ _ β b, Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun i _ => hs i)

theorem iterateCoeff_eq_sum_iterValue {ι : Type*} [Fintype ι]
    (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (β : ℂ) (b : Basis ι ℂ (N.isMod.weight β))
    {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz : ‖z₀‖ < ‖z₂‖) :
    iterateCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ β z₀ z₂ =
      ∑ i, iterValue Y₃.val Y₄.val (weightFunctional N.isMod β b i)
        w₁ w₂ (b i) (α₁ + α₂ - 2) (α₁ + α₂ - 1 - Q.h) z₀ z₂ := by
  have hs := fun i => summable_iterValue hV i₁ i₂ iN iN Y₃.property Y₄.property
    h₁ h₂ (b i).property (supportedAt_weightFunctional N.isMod β b i) hz₀ hz
  simp only [add_sub_cancel_right] at hs
  simp only [iterateCoeff, iterateTerm,
    iterateModeTrace_eq_sum Y₃ Y₄ w₁ w₂ _ _ β b, Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun i _ => hs i)

/-- The iterate summand is a one-point coefficient with an actual intermediate vector. -/
theorem iterateTerm_eq_onePoint (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (β z₀ z₂ : ℂ) (k : ℕ) :
    iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ β z₀ z₂ k =
      GenusOne.trace Y₃ (Y₄.val ((α₁ + α₂ - 1 - Q.h) - k) w₁ w₂)
        (β - W.centralCharge / 24) *
      z₂ ^ (-((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k) - 1) *
      z₀ ^ (-((α₁ + α₂ - 1 - Q.h) - k) - 1) := by
  unfold iterateTerm
  rw [show (α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + (k : ℂ) =
    α₁ + α₂ - ((α₁ + α₂ - 1 - Q.h) - k) - 2 by ring,
    iterateModeTrace_eq_onePoint Y₃ Y₄ h₁ h₂]

end VOA.Huang.GenusTwoPoint
