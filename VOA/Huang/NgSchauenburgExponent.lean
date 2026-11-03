import VOA.Huang.NgSchauenburgVafa
import Mathlib.Analysis.Normed.Ring.Finite

/-! # The numerical step in FS-exponent identification

The categorical Bantay trace formula remains a premise. The dimension identities
and positivity of squared simple dimensions are explicit premises as well;
none is added to `SphericalFusion` or `Modular`.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits

/-- Equality in the positive weighted phase bound forces every phase to be the unit phase. -/
theorem phases_eq_one_of_weighted_sum {J : Type*} [Fintype J]
    (w : J → ℝ) (t : J → ℂ) (j₀ : J) (hw : ∀ j, 0 < w j)
    (ht : ∀ j, ‖t j‖ = 1) (h₀ : t j₀ = 1)
    (h : ((∑ j, w j : ℝ) : ℂ) ^ 2 =
      ∑ i, ∑ j, (w i : ℂ) * (w j : ℂ) * (t i / t j)) : ∀ i, t i = 1 := by
  classical
  have hr (i j) : (t i / t j).re ≤ 1 := by
    calc
      _ ≤ ‖t i / t j‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_div, ht, ht]; norm_num
  have hn (i j) : 0 ≤ w i * w j * (1 - (t i / t j).re) :=
    mul_nonneg (mul_nonneg (hw i).le (hw j).le) (sub_nonneg.mpr (hr i j))
  have hs : ∑ i, ∑ j, w i * w j * (1 - (t i / t j).re) = 0 := by
    have hh := congrArg Complex.re h
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum, Complex.mul_re,
      Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, zero_add] at hh
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [← hh]
    simp [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have hi (i) : ∑ j, w i * w j * (1 - (t i / t j).re) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hn i j)).mp hs i
      (Finset.mem_univ i)
  intro i
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp (hi i) j₀
    (Finset.mem_univ j₀)
  have hre : (t i).re = 1 := by
    rw [h₀, div_one] at hij
    have := (mul_eq_zero.mp hij).resolve_left (ne_of_gt (mul_pos (hw i) (hw j₀)))
    linarith
  have hnorm := Complex.sq_norm_sub_sq_re (t i)
  rw [ht, hre] at hnorm
  apply Complex.ext
  · simpa using hre
  · have : (t i).im = 0 := by nlinarith [sq_nonneg (t i).im]
    simpa using this

attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Precise conditional identification, using Bantay and categorical dimension identities.
The three dimension premises are left visible until their trace proofs are supplied. -/
theorem isFSExponent_iff_twistOrder_dvd_of_bantay
    (F : SphericalFusion C) (M : Modular F) (hb : BantayFormula F M)
    (hsq : ∀ i, ∃ w : ℝ, 0 < w ∧ F.dimension (F.simple i) ^ 2 = (w : ℂ))
    (hmul : ∀ i j, (∑ k, (F.fusionMultiplicity i j (F.simple k) : ℂ) *
      F.dimension (F.simple k)) = F.dimension (F.simple i) * F.dimension (F.simple j))
    (hmass : ∀ V : C, (∑ i, ∑ j, (F.fusionMultiplicity i j V : ℂ) *
      F.dimension (F.simple i) * F.dimension (F.simple j)) = F.globalDimension * F.dimension V)
    {n : ℕ} (hn : 0 < n) : IsFSExponent F n ↔ M.toRibbon.twistOrder ∣ n := by
  classical
  choose w hw hd using hsq
  have hD : F.globalDimension = ((∑ i, w i : ℝ) : ℂ) := by
    simp [SphericalFusion.globalDimension, hd]
  have hpos : 0 < ∑ i, w i :=
    Finset.sum_pos (fun i _ => hw i) ⟨F.unitLabel, Finset.mem_univ _⟩
  have hD0 : F.globalDimension ≠ 0 := by rw [hD]; exact_mod_cast hpos.ne'
  constructor
  · intro hexp
    have htrace (k : F.Label) :
        F.globalDimension * F.dimension (F.simple k) =
          ∑ i, ∑ j, (F.fusionMultiplicity i j (F.simple k) : ℂ) *
            F.dimension (F.simple i) * F.dimension (F.simple j) *
              (M.twistScalar i / M.twistScalar j) ^ n := by
      rw [← hexp.2 (F.simple k), hb _ n hn]
      rw [← mul_assoc, mul_inv_cancel₀ hD0, one_mul]
    have hsum : F.globalDimension ^ 2 =
        ∑ i, ∑ j, F.dimension (F.simple i) ^ 2 * F.dimension (F.simple j) ^ 2 *
          (M.twistScalar i / M.twistScalar j) ^ n := by
      calc
        _ = ∑ k, F.dimension (F.simple k) *
            (F.globalDimension * F.dimension (F.simple k)) := by
          simp only [pow_two, mul_left_comm (F.dimension _) F.globalDimension]
          rw [← Finset.mul_sum]
          simp only [SphericalFusion.globalDimension, pow_two]
        _ = ∑ k, ∑ i, ∑ j, F.dimension (F.simple k) *
            ((F.fusionMultiplicity i j (F.simple k) : ℂ) *
              F.dimension (F.simple i) * F.dimension (F.simple j) *
                (M.twistScalar i / M.twistScalar j) ^ n) := by
          simp only [htrace, Finset.mul_sum]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          calc
            _ = (∑ k, (F.fusionMultiplicity i j (F.simple k) : ℂ) *
                F.dimension (F.simple k)) *
                  (F.dimension (F.simple i) * F.dimension (F.simple j) *
                    (M.twistScalar i / M.twistScalar j) ^ n) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k _; ring
            _ = _ := by rw [hmul]; ring
    have ht : ∀ i, M.twistScalar i ^ n = 1 := by
      apply phases_eq_one_of_weighted_sum w (fun i => M.twistScalar i ^ n) F.unitLabel hw
      · intro i
        simp [norm_pow, M.toRibbon.twistScalar_isOfFinOrder i |>.norm_eq_one]
      · simp [M.toRibbon.twistScalar_unitLabel]
      · simpa only [hD, hd, div_pow] using hsum
    rw [Ribbon.twistOrder, orderOf_dvd_iff_pow_eq_one]
    funext i
    exact ht i
  · intro hdiv
    have ht : ∀ i, M.twistScalar i ^ n = 1 := by
      have hpow := orderOf_dvd_iff_pow_eq_one.mp hdiv
      exact fun i => congrFun hpow i
    refine ⟨hn, fun V => ?_⟩
    rw [hb _ n hn]
    simp only [div_pow, ht, div_self one_ne_zero, mul_one]
    rw [hmass, ← mul_assoc, inv_mul_cancel₀ hD0, one_mul]

/-- FS exponent equals twist order once the explicit Bantay/dimension obligations hold. -/
theorem modularExponentTheorem_of_bantay_dimensions
    (F : SphericalFusion C) (M : Modular F) (hb : BantayFormula F M)
    (hsq : ∀ i, ∃ w : ℝ, 0 < w ∧ F.dimension (F.simple i) ^ 2 = (w : ℂ))
    (hmul : ∀ i j, (∑ k, (F.fusionMultiplicity i j (F.simple k) : ℂ) *
      F.dimension (F.simple k)) = F.dimension (F.simple i) * F.dimension (F.simple j))
    (hmass : ∀ V : C, (∑ i, ∑ j, (F.fusionMultiplicity i j V : ℂ) *
      F.dimension (F.simple i) * F.dimension (F.simple j)) = F.globalDimension * F.dimension V) :
    ModularExponentTheorem F M := by
  classical
  have hp := M.toRibbon.finite_twist.1
  have he := (isFSExponent_iff_twistOrder_dvd_of_bantay F M hb hsq hmul hmass hp).mpr dvd_rfl
  have hs := fsExponent_spec F ⟨_, he⟩
  refine ⟨hs.1, Nat.le_antisymm (fsExponent_le F he) ?_⟩
  exact Nat.le_of_dvd hs.1
    ((isFSExponent_iff_twistOrder_dvd_of_bantay F M hb hsq hmul hmass hs.1).mp hs)

end VOA.Huang.NgSchauenburg
