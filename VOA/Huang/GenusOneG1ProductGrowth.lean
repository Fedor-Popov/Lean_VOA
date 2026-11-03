import VOA.Huang.GenusOneG1SquareC2
import VOA.Huang.GenusOneWardHeadline
import VOA.Huang.GenusTwoPointGrowth

/-!
# Absolute double convergence of the genus-one two-point product trace

`productModeGrowth_holds`: for strongly rational `W`, irreducible modules and
homogeneous insertions, the level coefficients `τ(n,k)` of
`Tr_N Y₁(x,z₁) Y₂(y,z₂) q^{L₀}` (traced level `n`, intermediate level `k`) are
`O(a^{n+k})` for EVERY `a > 1`. Consequently (`productSewingSummable_holds`) the
full double series is absolutely summable on Huang's region
`|q| |z₁| < |z₂| < |z₁|` (`ProductSewingSummable`), strengthening the outer
`q`-convergence `productQSummable_holds`.

Proof. In `ℂ⟦u⟧⟦t⟧` (`u = q z₁/z₂`, `t = z₂/z₁`) the formal collected Ward
identities and Huang's two-slot C₂ induction (`phi_mem_span_pairs`) put every
`Phi x y` in the `Sub2`-span of finitely many generators; the mixed omega identity
closes the span under `Θ_{h−c/24}` (`thetaR2`). Each fixed-`n` row is genus-zero
convergent on `|t| < 1` (`conv_Phi`), hence `O(b^k)` for every `b > 1`. The
Euler-system majorant `geo2_of_euler_system` concludes.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.FusionC2
open VOA.Huang.GenusOne.SquareModule (shiftedOmega)
open VOA.Huang.GenusTwoPoint (ProductModeGrowth ProductSewingSummable productLevelCoeff
  TwoLevelBound)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section Product
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- Finitely many generators for the bilinear series over `Sub2`. -/
theorem exists_phi_generators (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) :
    ∃ (U : Finset P₁.carrier) (Z : Finset P₂.carrier), ∀ x y,
      Phi Y₁ Y₂ x y ∈ Submodule.span (↥Sub2)
        (Set.range fun k : U × Z => Phi Y₁ Y₂ k.1.val k.2.val) := by
  classical
  obtain ⟨U, hU, htopU⟩ := exists_finset_homog (N := P₁.isMod.toAdmissible)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₁)
  obtain ⟨Z, hZ, htopZ⟩ := exists_finset_homog (N := P₂.isMod.toAdmissible)
    (GenusOne.moduleC2_of_irreducible hV.c2Cofinite i₂)
  refine ⟨U, Z, fun x y => ?_⟩
  have h := phi_mem_span_pairs Y₁ Y₂ hU hZ htopU htopZ x y
  have he : {v | ∃ u ∈ (U : Set P₁.carrier), ∃ z ∈ (Z : Set P₂.carrier), Phi Y₁ Y₂ u z = v} =
      Set.range (fun k : U × Z => Phi Y₁ Y₂ k.1.val k.2.val) := by
    ext v
    constructor
    · rintro ⟨u, hu, z, hz, rfl⟩; exact ⟨(⟨u, hu⟩, ⟨z, hz⟩), rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k.1.val, k.1.property, k.2.val, k.2.property, rfl⟩
  rwa [he] at h

/-- The span is closed under the twisted Euler operator (mixed omega identity). -/
theorem theta_mem_of_span (T : Submodule (↥Sub2) R2)
    (hT : ∀ x y, Phi Y₁ Y₂ x y ∈ T) (x : P₁.carrier) (y : P₂.carrier) :
    thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ x y) ∈ T := by
  obtain ⟨K, hK⟩ := mixedLHS_evZero Y₁ Y₂ x y
  have h0 := hK K le_rfl
  unfold mixedLHS at h0
  have he : thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ x y) =
      Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (-1) (shiftedOmega W) x) y -
        ∑ m ∈ Finset.range K, eis (m + 1) *
          Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 1 : ℕ) : ℤ)
            (shiftedOmega W) x) y -
        ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
          Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) (shiftedOmega W) y) := by
    linear_combination -h0
  rw [he]
  refine T.sub_mem (T.sub_mem (hT _ _) ?_) ?_
  · exact T.sum_mem fun m _ => Sub2.mul_mem_span (eis_mem_Sub2 _) (hT _ _)
  · refine T.sum_mem fun m _ => Sub2.mul_mem_span ?_ (hT _ _)
    refine add_mem (piK_mem_Sub2 m) ?_
    split_ifs
    · exact Sub2.algebraMap_mem _
    · exact zero_mem _

/-- Rows of an absolutely convergent spatial series are geometrically bounded. -/
theorem row_bound_of_conv {f : R2} {b : ℝ} (hb : 1 < b)
    (hf : Conv ((((b⁻¹ : ℝ)) : ℂ)) f) (n : ℕ) :
    ∃ B : ℝ, ∀ k, ‖c2 f n k‖ ≤ B * b ^ k := by
  have hb0 : 0 < b := by linarith
  have hs := hf n
  refine ⟨∑' k : ℕ, ‖PowerSeries.coeff k (PowerSeries.coeff n f) *
    (((b⁻¹ : ℝ)) : ℂ) ^ k‖, fun k => ?_⟩
  have hle := hs.le_tsum k (fun j _ => norm_nonneg _)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hb0.le)]
    at hle
  have hbk : 0 < b ^ k := pow_pos hb0 k
  have : ‖c2 f n k‖ = ‖PowerSeries.coeff k (PowerSeries.coeff n f)‖ * b⁻¹ ^ k * b ^ k := by
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hb0.ne', one_pow, mul_one]; rfl
  rw [this]
  exact mul_le_mul_of_nonneg_right hle hbk.le

theorem phi_row_bound (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (x : P₁.carrier) (y : P₂.carrier) (n : ℕ) {b : ℝ} (hb : 1 < b) :
    ∃ B : ℝ, ∀ k, ‖c2 (Phi Y₁ Y₂ x y) n k‖ ≤ B * b ^ k := by
  have hb0 : 0 < b := by linarith
  have hz₂ : (((b⁻¹ : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.mpr hb0).ne'
  have hz : ‖(((b⁻¹ : ℝ)) : ℂ)‖ < ‖(1 : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hb0.le), norm_one]
    exact inv_lt_one_of_one_lt₀ hb
  have hc := conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz x y
  rw [div_one] at hc
  exact row_bound_of_conv hb hc n

/-- **Every genus-one two-point series is two-variable subexponential.** -/
theorem phi_mem_Sub2 (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (x : P₁.carrier) (y : P₂.carrier) : Phi Y₁ Y₂ x y ∈ Sub2 := by
  classical
  obtain ⟨U, Z, hUZ⟩ := exists_phi_generators Y₁ Y₂ hV i₁ i₂
  set T := Submodule.span (↥Sub2) (Set.range fun k : U × Z => Phi Y₁ Y₂ k.1.val k.2.val)
  have hθ : ∀ k : U × Z, ∃ c : U × Z → ↥Sub2,
      ∑ l, c l • Phi Y₁ Y₂ l.1.val l.2.val =
        thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ k.1.val k.2.val) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun (↥Sub2)).mp
      (theta_mem_of_span Y₁ Y₂ T hUZ k.1.val k.2.val)
  choose c hc using hθ
  have hgen : ∀ k : U × Z, Phi Y₁ Y₂ k.1.val k.2.val ∈ Sub2 := by
    refine geo2_of_euler_system (lam := N.h - W.centralCharge / 24)
      (f := fun k : U × Z => Phi Y₁ Y₂ k.1.val k.2.val)
      (Cm := fun k l => ((c k l : ↥Sub2) : R2)) (fun k l => (c k l).property) ?_ ?_
    · intro k
      rw [← hc k]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
    · intro k n b hb
      exact phi_row_bound Y₁ Y₂ hV i₁ i₂ iN _ _ n hb
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Sub2)).mp (hUZ x y)
  rw [← hd]
  refine Subalgebra.sum_mem _ fun l _ => ?_
  rw [Subalgebra.smul_def, smul_eq_mul]
  exact Subalgebra.mul_mem _ (d l).property (hgen l)

/-- The level coefficients of the library are the coefficients of `Phi`. -/
theorem productLevelCoeff_eq_c2 {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (n k : ℕ) :
    productLevelCoeff Y₁ Y₂ x y α₁ α₂ n k = c2 (Phi Y₁ Y₂ x y) n k := by
  rw [Phi_homog Y₁ Y₂ hx hy]
  change _ = PowerSeries.coeff k (PowerSeries.coeff n (phiH Y₁ Y₂ x y α₁ α₂))
  rw [phiH_row]
  simp only [GenusTwoPoint.Separate.rawLevelSeries, PowerSeries.coeff_mk, productLevelCoeff]
  congr 1 <;> ring

/-- **`ProductModeGrowth` holds** (two-level subexponential growth of the
genus-one two-point product coefficients). -/
theorem productModeGrowth_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    ProductModeGrowth Y₁ Y₂ x y α₁ α₂ := by
  intro a ha
  obtain ⟨C, hC⟩ := phi_mem_Sub2 Y₁ Y₂ hV i₁ i₂ iN x y a ha
  refine ⟨C, Geo2.const_nonneg hC, fun n k => ?_⟩
  rw [productLevelCoeff_eq_c2 Y₁ Y₂ hx hy, mul_assoc, ← pow_add]
  exact hC n k

/-- **Absolute double convergence of the genus-one two-point product trace**
on Huang's region `|q| |z₁| < |z₂| < |z₁|`. -/
theorem productSewingSummable_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ * ‖z₁‖ < ‖z₂‖) :
    ProductSewingSummable Y₁ Y₂ x y α₁ α₂ z₁ z₂ τ :=
  GenusTwoPoint.productSewingSummable_of_modeGrowth Y₁ Y₂ x y α₁ α₂
    (productModeGrowth_holds Y₁ Y₂ hV i₁ i₂ iN hx hy) hz₂ hz τ hq

end Product

end VOA.Huang.GenusOneWard
