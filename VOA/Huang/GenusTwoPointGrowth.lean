import VOA.Huang.GenusTwoPointMajorant

/-!
# The uniform growth still needed for general sewing

`ProductModeGrowth` and `IterateModeGrowth` are coefficient estimates on actual
traces, not axioms. Their intended hypotheses are strongly rational W,
irreducible modules and homogeneous insertions (Huang 2005, §§3–4).
They are NOT proved here. We prove their analytic consequences and the
pointwise-in-intermediate-level bound supplied by the one-point theorem.
In particular, that pointwise bound is not promoted to a uniform bound.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA
open scoped BigOperators
universe u

/-- A strict geometric margin can be enlarged slightly. -/
theorem exists_geometric_margin {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) :
    ∃ a : ℝ, 1 < a ∧ a * t < 1 := by
  obtain ⟨s, hts, hs⟩ := exists_between ht
  have hs0 : 0 < s := lt_of_le_of_lt ht0 hts
  refine ⟨1 / s, (lt_div_iff₀ hs0).2 (by simpa using hs), ?_⟩
  rw [div_mul_eq_mul_div, one_mul, div_lt_one hs0]
  exact hts

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Residual product estimate: subexponential growth in BOTH independent levels.
It has no coordinate variables and asks for no equality or summation exchange.
Its existence for general strongly rational data remains open. -/
def ProductModeGrowth
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) : Prop :=
  ∀ a : ℝ, 1 < a → ∃ C : ℝ, 0 ≤ C ∧
    TwoLevelBound (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂) C a a

/-- Residual local iterate estimate: after choosing ANY q-radius strictly inside
the unit disc, there is one exponential bound in the intermediate level.
The k-growth constant may depend on the chosen q-margin. -/
def IterateModeGrowth
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) : Prop :=
  ∀ a : ℝ, 1 < a → ∃ C b : ℝ, 0 ≤ C ∧ 0 ≤ b ∧
    TwoLevelBound (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂) C a b

/-- The raw product sewing domain is invariant under simultaneous scaling of
the insertion points. This theorem retains the unproved coefficient estimate. -/
theorem productSewingSummable_of_modeGrowth
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (hg : ProductModeGrowth Y₁ Y₂ w₁ w₂ α₁ α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (τ : UpperHalfPlane)
    (hq : ‖qParam τ‖ * ‖z₁‖ < ‖z₂‖) :
    ProductSewingSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg z₂) hz)
  have hx : ‖qParam τ * z₁ / z₂‖ < 1 := by
    rw [norm_div, norm_mul, div_lt_one (norm_pos_iff.mpr hz₂)]
    exact hq
  have hy : ‖z₂ / z₁‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz₁)]
    exact hz
  obtain ⟨a, ha, hmargin⟩ := exists_geometric_margin
    (le_trans (norm_nonneg _) (le_max_left ‖qParam τ * z₁ / z₂‖ ‖z₂ / z₁‖))
    (max_lt hx hy)
  obtain ⟨C, hC, hbound⟩ := hg a ha
  exact productSewingSummable_of_modeBound Y₁ Y₂ w₁ w₂ α₁ α₂ hC
    (by linarith) (by linarith) hbound hz₁ hz₂ τ
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)) hmargin)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)) hmargin)

/-- In the original product chart both summability obligations follow from the
same coefficient estimate. The estimate is still an explicit hypothesis. -/
theorem productSummable_in_sewingRegion_of_modeGrowth
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (hg : ProductModeGrowth Y₁ Y₂ w₁ w₂ α₁ α₂)
    {z₁ z₂ : ℂ} (hz₁ : ‖z₁‖ < 1) (hz : ‖z₂‖ < ‖z₁‖)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ < ‖z₂‖) :
    ProductSewingSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ ∧
      ProductQSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ := by
  have hs := productSewingSummable_of_modeGrowth Y₁ Y₂ w₁ w₂ α₁ α₂ hg
    (norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hq)) hz τ
    (lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hz₁.le) hq)
  exact ⟨hs, productQSummable_of_sewing Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ hs⟩

/-- The one-point theorem does prove subexponential growth for each fixed k.
There is no bound here on how its constants depend on k. -/
theorem iterateLevelCoeff_subexponential (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂) (k : ℕ) :
    Subexponential (fun n => ‖iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k‖) := by
  have hs := GenusOne.traceSubexponential_of_irreducible hC2 iQ Y₃
    ⟨N.realized, N.isLow⟩ (Y₄.val ((α₁ + α₂ - 1 - Q.h) - k) w₁ w₂)
  convert hs using 1
  funext n
  unfold iterateLevelCoeff
  rw [show (α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + (k : ℂ) =
    α₁ + α₂ - ((α₁ + α₂ - 1 - Q.h) - k) - 2 by ring,
    iterateModeTrace_eq_onePoint Y₃ Y₄ h₁ h₂,
    show N.h + (n : ℂ) - W.centralCharge / 24 = N.h - W.centralCharge / 24 + n by ring]

/-- Pointwise row constants exist. A geometric bound on this family is the
additional requirement in `IterateModeGrowth`, not a consequence of choice. -/
theorem exists_iterate_row_bounds (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    {a : ℝ} (ha : 1 < a) :
    ∃ B : ℕ → ℝ, (∀ k, 0 ≤ B k) ∧
      ∀ n k, ‖iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k‖ ≤ B k * a ^ n := by
  choose B hB using fun k => (iterateLevelCoeff_subexponential hC2 iQ Y₃ Y₄ h₁ h₂ k) a ha
  refine ⟨fun k => max (B k) 0, fun k => le_max_right _ _, fun n k => ?_⟩
  exact le_trans (hB k n)
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _))

/-- The intermediate sewing radius is positive, and may shrink as τ approaches
the boundary. There is no assertion of convergence for every `‖z₀‖ < ‖z₂‖`. -/
theorem exists_iterateSewingRadius_of_modeGrowth
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (hg : IterateModeGrowth Y₃ Y₄ w₁ w₂ α₁ α₂) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (z₀ z₂ : ℂ), z₀ ≠ 0 → z₂ ≠ 0 →
      ‖z₀ / z₂‖ < δ → IterateSewingSummable Y₃ Y₄ w₁ w₂ α₁ α₂ z₀ z₂ τ := by
  obtain ⟨a, ha, hqa⟩ := exists_geometric_margin (norm_nonneg _) (norm_qParam_lt_one τ)
  obtain ⟨C, b, hC, hb, hbound⟩ := hg a ha
  have hb1 : 0 < b + 1 := by linarith
  refine ⟨1 / (b + 1), div_pos zero_lt_one hb1,
    (div_le_one hb1).2 (by linarith), ?_⟩
  intro z₀ z₂ hz₀ hz₂ hz
  apply iterateSewingSummable_of_modeBound Y₃ Y₄ w₁ w₂ α₁ α₂ hC
    (by linarith) hb hbound hz₀ hz₂ τ hqa
  have ht := (lt_div_iff₀ hb1).mp hz
  nlinarith [norm_nonneg (z₀ / z₂)]

end VOA.Huang.GenusTwoPoint
