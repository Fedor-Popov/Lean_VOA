import VOA.Huang.GenusOneCloseResolve
import VOA.Huang.GenusOneCloseCompare
import VOA.Huang.GenusOneCloseGrowth

/-!
# Analytic logarithmic pairs of insertion blocks

Let `F, G` be analytic insertion blocks with `G(τ+1) = μG(τ)` and
`F(τ+1) = μF(τ) + G(τ)`, `μ ≠ 0`. Then `H = F − (τ/μ)G` is `μ`-periodic and
satisfies the block relations with omega defect `(2πiμ)⁻¹G`. Moderate growth
gives convergent expansions of `G` and `H` at one base exponent; coefficient
comparison makes them a formal block and a formal defect block; and the formal
resolution proves `G = 0` and that `F` is a finite sum of intertwiner traces.

With `G = 0` this is the log-free case of Miyamoto, math/0010180, Theorems 4.9
and 4.15; in general it is Proposition 4.14 for Jordan chains of length two,
which suffices for the quotient argument in `GenusOneCloseMain`.
-/
namespace VOA.Huang.GenusOne.Close
open VOA Complex
open scoped BigOperators Real
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-- The subtracted function `H = F − (τ/μ)G` satisfies the defect relations. -/
theorem isAnalyticDefect_pair {F G : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F)
    (hG : IsInsertionAnalyticBlock A G) (μ : ℂ) :
    IsAnalyticDefect A (fun v z => F v z - z * μ⁻¹ * G v z)
      (fun v z => ((2 * (π : ℂ) * I)⁻¹ * μ⁻¹) * G v z) where
  vanish ka hka a ha v z _ := by
    simp only [hF.vanish ka hka a ha v, hG.vanish ka hka a ha v, Pi.zero_apply, mul_zero,
      sub_zero]
  negTwo ka hka a ha v z hz := by
    obtain ⟨K₀, hK₀⟩ := sqAct_tail_eventually_zero A a ka v
    have hFn := hF.negTwo ka hka a ha v z hz
    have hGn := hG.negTwo ka hka a ha v z hz
    rw [insertionNegTwoSum hF.zerov hK₀ z] at hFn
    rw [insertionNegTwoSum hG.zerov hK₀ z] at hGn
    rw [insertionNegTwoSum (F := fun v z => F v z - z * μ⁻¹ * G v z)
      (fun z => by simp only [hF.zerov, hG.zerov, mul_zero, sub_zero]) hK₀ z]
    have hsplit : ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 1) z * (F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z
            - z * μ⁻¹ * G (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z))
        = (∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z))
          - z * μ⁻¹ * ∑ m ∈ Finset.range K₀, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z * G (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hsplit]
    linear_combination hFn - z * μ⁻¹ * hGn
  omega v z hz := by
    obtain ⟨K₀, hK₀⟩ := sqL_tail_eventually_zero A v
    have hFo := hF.omega v z hz
    have hGo := hG.omega v z hz
    rw [insertionOmegaSum hF.zerov hK₀ z] at hFo
    rw [insertionOmegaSum hG.zerov hK₀ z] at hGo
    rw [insertionOmegaSum (F := fun v z => F v z - z * μ⁻¹ * G v z)
      (fun z => by simp only [hF.zerov, hG.zerov, mul_zero, sub_zero]) hK₀ z]
    have hFd := ((hF.holo v) z hz).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
    have hGd := ((hG.holo v) z hz).differentiableAt ((isOpen_imGT 0).mem_nhds hz)
    have hd : HasDerivAt (fun y => F v y - y * μ⁻¹ * G v y)
        (_root_.deriv (F v) z - (1 * μ⁻¹ * G v z + z * μ⁻¹ * _root_.deriv (G v) z)) z :=
      hFd.hasDerivAt.sub (((hasDerivAt_id' z).mul_const μ⁻¹).mul hGd.hasDerivAt)
    rw [hd.deriv]
    have hsplit : ∑ m ∈ Finset.range K₀, zhuGC (m + 1) z
          * (F (sqL A (2 * (m + 1) - 2 : ℤ) v) z - z * μ⁻¹ * G (sqL A (2 * (m + 1) - 2 : ℤ) v) z)
        = (∑ m ∈ Finset.range K₀, zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z)
          - z * μ⁻¹ * ∑ m ∈ Finset.range K₀,
              zhuGC (m + 1) z * G (sqL A (2 * (m + 1) - 2 : ℤ) v) z := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hsplit]
    linear_combination hFo - z * μ⁻¹ * hGo

/-- **Analytic logarithmic pairs resolve.** -/
theorem log_pair_resolve {ι : Type u} [Fintype ι]
    (hAC2 : FusionC2.ModuleC2Cofinite A.toWeakModule) (P : ι → LWModule W)
    (hB : InsertionTopBimoduleExists A P) (hlift : InsertionTopSurjectivity A P)
    {F G : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F) (hG : IsInsertionAnalyticBlock A G)
    {μ : ℂ} (hμ : μ ≠ 0)
    (hFper : ∀ w, ∀ z ∈ imGT 0, F w (z + 1) = μ * F w z + G w z)
    (hGper : ∀ w, ∀ z ∈ imGT 0, G w (z + 1) = μ * G w z) :
    (∀ w, ∀ z ∈ imGT 0, G w z = 0) ∧ ∃ b : ℂ, ∃ Z : ∀ i, IntertwiningOperator A (P i).isMod
      (P i).isMod, SuppAt P b Z ∧
        ∀ w, ∀ z ∈ imGT 0, F w z = qEvalC ((∑ i, trace (Z i)) w) b z := by
  classical
  -- the exponent
  set r : ℂ := Complex.log μ / (2 * π * I) with hr
  have hrμ : cexp (2 * π * I * r) = μ := by
    rw [hr, mul_div_cancel₀ _ two_pi_I_ne_zero, Complex.exp_log hμ]
  obtain ⟨K, hK0, hgrowth⟩ := exists_uniform_growth hAC2
  set K' : ℝ := K + 1 with hK'
  set H : M → ℂ → ℂ := fun v z => F v z - z * μ⁻¹ * G v z with hHdef
  set κ : ℂ := (2 * (π : ℂ) * I)⁻¹ * μ⁻¹ with hκdef
  have hκ : κ ≠ 0 := mul_ne_zero (inv_ne_zero two_pi_I_ne_zero) (inv_ne_zero hμ)
  have hHdef' := isAnalyticDefect_pair hF hG μ
  -- periodicity
  have hHper : ∀ w, ∀ z ∈ imGT 0, H w (z + 1) = cexp (2 * π * I * r) * H w z := by
    intro w z hz
    simp only [H, hrμ, hFper w z hz, hGper w z hz]
    field_simp
    ring
  have hGper' : ∀ w, ∀ z ∈ imGT 0, G w (z + 1) = cexp (2 * π * I * r) * G w z := by
    intro w z hz
    rw [hrμ, hGper w z hz]
  -- holomorphy
  have hHholo : ∀ w, DifferentiableOn ℂ (H w) (imGT 0) := fun w =>
    (hF.holo w).sub (((differentiableOn_id.mul_const μ⁻¹)).mul (hG.holo w))
  -- growth with exponent `K + 1`
  have hexp : ∀ y : ℝ, 0 ≤ y → Real.exp (K * y) ≤ Real.exp (K' * y) := fun y hy =>
    Real.exp_le_exp.mpr (by rw [hK']; nlinarith)
  have hGbd : ∀ w, ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im →
      ‖G w z‖ ≤ C * Real.exp (K' * z.im) := by
    intro w
    obtain ⟨C, hC⟩ := hgrowth G hG w
    refine ⟨|C|, fun z h0 h1 him => (hC z h0 h1 him).trans ?_⟩
    exact mul_le_mul (le_abs_self C) (hexp _ (by linarith)) (Real.exp_pos _).le (abs_nonneg C)
  have hHbd : ∀ w, ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im →
      ‖H w z‖ ≤ C * Real.exp (K' * z.im) := by
    intro w
    obtain ⟨CF, hCF⟩ := hgrowth F hF w
    obtain ⟨CG, hCG⟩ := hgrowth G hG w
    refine ⟨|CF| + ‖μ⁻¹‖ * |CG|, fun z h0 h1 him => ?_⟩
    have hy : 0 ≤ z.im := by linarith
    have hz : ‖z‖ ≤ 1 + z.im := by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 + z.im := by rw [abs_of_nonneg h0, abs_of_nonneg hy]; linarith
    have hFz := hCF z h0 h1 him
    have hGz := hCG z h0 h1 him
    have h1y : 1 + z.im ≤ Real.exp z.im := by linarith [Real.add_one_le_exp z.im]
    have hprod : (1 + z.im) * Real.exp (K * z.im) ≤ Real.exp (K' * z.im) := by
      calc (1 + z.im) * Real.exp (K * z.im) ≤ Real.exp z.im * Real.exp (K * z.im) :=
            mul_le_mul_of_nonneg_right h1y (Real.exp_pos _).le
        _ = Real.exp (K' * z.im) := by rw [← Real.exp_add, hK']; ring_nf
    calc ‖H w z‖ = ‖F w z - z * μ⁻¹ * G w z‖ := rfl
      _ ≤ ‖F w z‖ + ‖z‖ * ‖μ⁻¹‖ * ‖G w z‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ |CF| * Real.exp (K * z.im) + (1 + z.im) * ‖μ⁻¹‖ * (|CG| * Real.exp (K * z.im)) := by
          gcongr
          · exact hFz.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
          · exact hGz.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
      _ = |CF| * Real.exp (K * z.im) + ‖μ⁻¹‖ * |CG| * ((1 + z.im) * Real.exp (K * z.im)) := by
          ring
      _ ≤ |CF| * Real.exp (K' * z.im) + ‖μ⁻¹‖ * |CG| * Real.exp (K' * z.im) :=
          add_le_add (mul_le_mul_of_nonneg_left (hexp _ hy) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hprod (by positivity))
      _ = (|CF| + ‖μ⁻¹‖ * |CG|) * Real.exp (K' * z.im) := by ring
  -- expansions at one base point
  obtain ⟨SG, hSG, hGeval⟩ := exists_family_expansion G r K' hG.holo
    (fun v w z _ => hG.addv v w z) (fun c v z _ => hG.smulv c v z) hGper' hGbd
  obtain ⟨SH, hSH, hHeval⟩ := exists_family_expansion H r K' hHholo
    (fun v w z _ => by simp only [H, hF.addv, hG.addv]; ring)
    (fun c v z _ => by simp only [H, hF.smulv, hG.smulv]; ring) hHper hHbd
  set b := expBase r K' with hb
  -- coefficient comparison
  have hGformal : IsInsertionFormalBlock A SG := by
    rw [← isDefectBlock_zero_iff]
    exact isDefectBlock_of_analytic (isAnalyticDefect_of_block hG) SG 0 hSG
      (fun _ => good_zero) hGeval (fun w z _ => by simp)
  have hHformal : IsDefectBlock A SH (κ • SG) :=
    isDefectBlock_of_analytic hHdef' SH (κ • SG) hSH (fun w => (hSG w).smul κ) hHeval
      (fun w z hz => by
        rw [LinearMap.smul_apply, qEvalC_smul, ← hGeval w z hz])
  obtain ⟨hG0, Z, hZ, hHZ⟩ := defect_pair_resolve P hB hlift hκ (fun w => (hSG w).1)
    (fun w => (hSH w).1) hGformal hHformal
  have hGz : ∀ w, ∀ z ∈ imGT 0, G w z = 0 := by
    intro w z hz
    rw [hGeval w z hz, hG0]
    simp
  refine ⟨hGz, b, Z, hZ, fun w z hz => ?_⟩
  have h := hHeval w z hz
  simp only [H, hGz w z hz, mul_zero, sub_zero] at h
  rw [h, hHZ]

end VOA.Huang.GenusOne.Close
