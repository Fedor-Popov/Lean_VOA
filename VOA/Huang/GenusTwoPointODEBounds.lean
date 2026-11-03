import VOA.Huang.GenusTwoPointUniformFuchsian
import VOA.Huang.GenusTwoPointGrowth

/-!
# Uniform Fuchsian bounds, finite strips, and the two trace indices

The abstract implication from a COMMON scalar equation and finite-strip bounds
to two-level bounds is proved here. Its common-equation hypothesis is not
asserted for general VOA traces. Genus-zero equations fix the external vectors;
tracing over all weights changes those vectors. In particular, finite generation
over a rational-function ring is not finite dimensionality over the scalars.

For actual intertwiner traces we prove subexponential growth in the intermediate
index at each traced weight, and bounds on any finite strip. The iterate also
has finite strips in the traced index by the existing one-point theorem. These
are genuine narrower estimates, not joint sewing.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA PowerSeries FuchsianODE MatrixCoeff AssocTarget Convergence
open scoped BigOperators

/-- A bound on finitely many columns, uniform over every row. It has no
summation or differential-equation assumption. -/
def FiniteInitialStrip (d : ℕ → ℕ → ℂ) (K : ℕ) (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n j, j < K → ‖d n j‖ ≤ C * a ^ n

/-- Pointwise subexponential rows give uniform constants on any FINITE strip.
The constant is allowed to depend on the strip width. -/
theorem finiteInitialStrip_of_subexponential {d : ℕ → ℕ → ℂ}
    (hd : ∀ j, Subexponential (fun n => ‖d n j‖)) (K : ℕ) {a : ℝ} (ha : 1 < a) :
    FiniteInitialStrip d K a := by
  have hs := Subexponential.finsetSum (Finset.range K) (fun j n => ‖d n j‖)
    (fun j _ => hd j)
  obtain ⟨C, hC⟩ := hs a ha
  have hC0 : 0 ≤ C := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (by simpa using hC 0)
  exact ⟨C, hC0, fun n j hj =>
    (Finset.single_le_sum (fun j _ => norm_nonneg (d n j))
      (Finset.mem_range.mpr hj)).trans (hC n)⟩

/-- For a fixed equation the finite strip needed to control a two-index family
is independent of that family and its amplitude. All constants are explicit. -/
theorem twoLevelBound_of_common_fuchsian (lam : ℂ) (s : ℕ)
    (c : ℕ → PowerSeries ℂ) (hc : ∀ i < s, c i ∈ SubexpPS)
    {b : ℝ} (hb : 1 < b) :
    ∃ K : ℕ, ∀ (d : ℕ → ℕ → ℂ) (C a : ℝ), 0 ≤ C → 0 ≤ a →
      (∀ n, FuchsianEq lam s c (PowerSeries.mk (d n))) →
      (∀ n j, j < K → ‖d n j‖ ≤ C * a ^ n) → TwoLevelBound d C a b := by
  obtain ⟨K, hK⟩ := uniform_fuchsian_cutoff lam s c hc hb
  refine ⟨K, fun d C a hC ha heq hinit n k => ?_⟩
  have hB : 0 ≤ C * a ^ n := mul_nonneg hC (pow_nonneg ha n)
  have h := hK (PowerSeries.mk (d n)) (C * a ^ n) (heq n) hB
    (fun j hj => (by simpa using hinit n j hj :
      ‖coeff j (PowerSeries.mk (d n))‖ ≤ C * a ^ n).trans
        (le_mul_of_one_le_right hB (one_le_pow₀ hb.le))) k
  simpa only [coeff_mk] using h

/-- A common equation upgrades separately proved row growth to joint growth.
This is a conditional analytic criterion, NOT a claimed common VOA equation. -/
theorem twoLevelGrowth_of_common_fuchsian {d : ℕ → ℕ → ℂ}
    (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS)
    (heq : ∀ n, FuchsianEq lam s c (PowerSeries.mk (d n)))
    (hd : ∀ j, Subexponential (fun n => ‖d n j‖)) :
    ∀ a : ℝ, 1 < a → ∃ C : ℝ, 0 ≤ C ∧ TwoLevelBound d C a a := by
  intro a ha
  obtain ⟨K, hK⟩ := twoLevelBound_of_common_fuchsian lam s c hc ha
  obtain ⟨C, hC, hinit⟩ := finiteInitialStrip_of_subexponential hd K ha
  exact ⟨C, hC, hK d C a hC (by linarith) heq hinit⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- What the genus-zero product ODE supplies for raw traces: subexponential
intermediate-level coefficients at ONE fixed traced weight. -/
theorem productLevelCoeff_subexponential (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂) (n : ℕ) :
    Subexponential (fun k => ‖productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ n k‖) := by
  classical
  let β : ℂ := N.h + n
  letI := N.isMod.finrank β
  let b := Module.finBasis ℂ (N.isMod.weight β)
  have hs := fun i => subexponential_of_ratFuchsian (by simp : ‖(1 : ℂ)‖ ≤ 1)
    ((ModuleC2.huangODEInput_holds _ W hV).1 P₁ P₂ N N i₁ i₂ iN iN Q.isMod
      Y₁.property Y₂.property h₁ h₂ (b i).property
      (supportedAt_weightFunctional N.isMod β b i)
      (isBase_canonical Q Y₂.property h₂ (b i).property))
  apply Subexponential.of_le _ (Subexponential.finsetSum Finset.univ _ (fun i _ => hs i))
  intro k
  dsimp only at hs ⊢
  simp only [coeff_prodSeries, add_sub_cancel_right]
  unfold productLevelCoeff
  have he : α₂ + N.h + (n : ℂ) - 1 - Q.h = α₂ + β - 1 - Q.h := by dsimp [β]; ring
  rw [he, productModeTrace_eq_sum Y₁ Y₂ w₁ w₂ _ _ β b]
  exact norm_sum_le _ _

/-- The corresponding genus-zero estimate for the iterate at fixed traced weight.
It complements, but does not replace, the one-point estimate in the other index. -/
theorem iterateLevelCoeff_intermediate_subexponential (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂) (n : ℕ) :
    Subexponential (fun k => ‖iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k‖) := by
  classical
  let β : ℂ := N.h + n
  letI := N.isMod.finrank β
  let b := Module.finBasis ℂ (N.isMod.weight β)
  have hs := fun i => subexponential_of_ratFuchsian (by simp : ‖(-1 : ℂ)‖ ≤ 1)
    ((ModuleC2.huangODEInput_holds _ W hV).2 P₁ P₂ N N i₁ i₂ iN iN Q.isMod
      Y₃.property Y₄.property h₁ h₂ (b i).property
      (supportedAt_weightFunctional N.isMod β b i) (isBase_canonical Q Y₄.property h₁ h₂))
  apply Subexponential.of_le _ (Subexponential.finsetSum Finset.univ _ (fun i _ => hs i))
  intro k
  simp only [coeff_iterSeries, add_sub_cancel_right]
  unfold iterateLevelCoeff
  rw [iterateModeTrace_eq_sum Y₃ Y₄ w₁ w₂ _ _ β b]
  exact norm_sum_le _ _

/-- A finite traced-weight strip has a single subexponential intermediate bound.
There is no uniformity in the strip width K. -/
theorem product_finite_traced_strip (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (K : ℕ) {a : ℝ} (ha : 1 < a) :
    FiniteInitialStrip (fun k n => productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ n k) K a :=
  finiteInitialStrip_of_subexponential
    (productLevelCoeff_subexponential hV i₁ i₂ iN Y₁ Y₂ h₁ h₂) K ha

/-- Every finite intermediate strip already has the required traced-level bound
from one-point convergence, without any common-equation assumption. -/
theorem iterate_finite_intermediate_strip (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (K : ℕ) {a : ℝ} (ha : 1 < a) :
    FiniteInitialStrip (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂) K a :=
  finiteInitialStrip_of_subexponential
    (iterateLevelCoeff_subexponential hC2 iQ Y₃ Y₄ h₁ h₂) K ha

/-- Conditional sewing criterion exposing exactly the extra common-equation
hypothesis. Its validity for general traces is NOT asserted by this theorem. -/
theorem iterateModeGrowth_of_common_fuchsian
    (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS)
    (heq : ∀ n, FuchsianEq lam s c
      (PowerSeries.mk (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n))) :
    IterateModeGrowth Y₃ Y₄ w₁ w₂ α₁ α₂ := by
  intro a ha
  obtain ⟨C, hC, hb⟩ := twoLevelGrowth_of_common_fuchsian lam s c hc heq
    (iterateLevelCoeff_subexponential hC2 iQ Y₃ Y₄ h₁ h₂) a ha
  exact ⟨C, a, hC, by linarith, hb⟩

end VOA.Huang.GenusTwoPoint
