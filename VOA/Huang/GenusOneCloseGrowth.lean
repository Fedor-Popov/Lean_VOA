import VOA.Huang.GenusOneUniformSystem
import Mathlib.Analysis.ODE.Gronwall

/-!
# Moderate growth of analytic insertion blocks at the cusp

The uniform Eisenstein system `Uniform.exists_uniform_analytic_system` has
coefficients bounded on `Im z ≥ 1`. Grönwall's inequality along vertical lines
then bounds every analytic insertion block by `C_w e^{K Im z}` on the strip
`0 ≤ Re z ≤ 1, Im z ≥ 1`, with one exponent `K` for all blocks. This is the
regular-singularity input to the cusp expansion (Miyamoto, math/0010180,
Theorem 4.9; Zhu, JAMS 9 (1996), §5).
-/
namespace VOA.Huang.GenusOne.Close
open VOA Complex
open scoped BigOperators Real
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-- A bound for an Eisenstein-ring coefficient on `Im z ≥ 1`. -/
noncomputable def eisBound (g : ↥GSeries) : ℝ :=
  ∑' n : ℕ, ‖PowerSeries.coeff n (g : PowerSeries ℂ)‖ * Real.exp (-(2 * π * n))

theorem summable_eisBound (g : ↥GSeries) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff n (g : PowerSeries ℂ)‖ *
      Real.exp (-(2 * π * n))) := by
  have hz : (I : ℂ) ∈ imGT 0 := by change (0 : ℝ) < I.im; simp
  refine (summable_norm_eisenstein g hz).congr fun n => ?_
  rw [norm_mul, norm_qexp]
  simp

theorem eisBound_nonneg (g : ↥GSeries) : 0 ≤ eisBound g :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem norm_eisensteinEval_le (g : ↥GSeries) {z : ℂ} (hz : 1 ≤ z.im) :
    ‖eisensteinEval g z‖ ≤ eisBound g := by
  have hz0 : z ∈ imGT 0 := by change (0 : ℝ) < z.im; linarith
  refine (norm_tsum_le_tsum_norm (summable_norm_eisenstein g hz0)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eisenstein g hz0)
    (summable_eisBound g)
  rw [norm_mul, norm_qexp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) hn) (sub_nonneg.mpr hz)
  linarith [h, show 2 * π * n * (z.im - 1) = 2 * π * n * z.im - 2 * π * n by ring]

theorem hasDerivAt_vertical (f : ℂ → ℂ) (x s : ℝ) {d : ℂ}
    (hf : HasDerivAt f d ((x : ℂ) + I * (s : ℂ))) :
    HasDerivAt (fun t : ℝ => f ((x : ℂ) + I * (t : ℂ))) (d * I) s := by
  have hl : HasDerivAt (fun t : ℝ => (x : ℂ) + I * (t : ℂ)) I s := by
    have h1 := ((hasDerivAt_id s).ofReal_comp).const_mul I
    simpa using h1.const_add (x : ℂ)
  exact hf.comp s hl

/-- **Uniform moderate growth of analytic insertion blocks.** -/
theorem exists_uniform_growth (hAC2 : FusionC2.ModuleC2Cofinite A.toWeakModule) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : M → ℂ → ℂ, IsInsertionAnalyticBlock A F → ∀ w : M,
      ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ z.im →
        ‖F w z‖ ≤ C * Real.exp (K * z.im) := by
  classical
  obtain ⟨U, B, c, hsys⟩ := Uniform.exists_uniform_analytic_system hAC2
  set L : ℝ := ∑ k : U, ∑ l : U, eisBound (B k l) with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    eisBound_nonneg _
  set K : ℝ := 2 * π * L with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, hK0, fun F hF w => ?_⟩
  obtain ⟨hder, hgen⟩ := hsys F hF
  let v : ℝ → ℝ → (U → ℂ) := fun x t k => F k.val ((x : ℂ) + I * (t : ℂ))
  have hmem : ∀ x t : ℝ, 0 < t → (x : ℂ) + I * (t : ℂ) ∈ imGT 0 := by
    intro x t ht
    change (0 : ℝ) < ((x : ℂ) + I * (t : ℂ)).im
    simpa using ht
  -- the derivative of each component on the upper half-plane
  have hderiv : ∀ (k : U) (z : ℂ) (hz : z ∈ imGT 0),
      _root_.deriv (F k.val) z =
        2 * π * I * ∑ l : U, eisensteinEval (B k l) z * F l.val z := by
    intro k z hz
    have h := hder k ⟨z, hz⟩
    change (2 * (π : ℂ) * I)⁻¹ * _root_.deriv (F k.val) z =
      ∑ l : U, eisensteinEval (B k l) z * F l.val z at h
    rw [← h, ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
  have hhas : ∀ (x t : ℝ), 0 < t → HasDerivAt (v x)
      (fun k : U => _root_.deriv (F k.val) ((x : ℂ) + I * (t : ℂ)) * I) t := by
    intro x t ht
    apply hasDerivAt_pi.2
    intro k
    have hd := ((hF.holo k.val) _ (hmem x t ht)).differentiableAt
      ((isOpen_imGT 0).mem_nhds (hmem x t ht))
    exact hasDerivAt_vertical (F k.val) x t hd.hasDerivAt
  -- the derivative bound
  have hbound : ∀ (x t : ℝ), 1 ≤ t →
      ‖(fun k : U => _root_.deriv (F k.val) ((x : ℂ) + I * (t : ℂ)) * I)‖ ≤
        K * ‖v x t‖ + 0 := by
    intro x t ht
    rw [add_zero]
    have hz := hmem x t (by linarith)
    have him : 1 ≤ ((x : ℂ) + I * (t : ℂ)).im := by simpa using ht
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
    rw [norm_mul, Complex.norm_I, mul_one, hderiv k _ hz, norm_mul]
    have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        Real.pi_pos.le]
      norm_num
    rw [h2pi, hK]
    suffices key : ‖∑ l : U, eisensteinEval (B k l) ((x : ℂ) + I * (t : ℂ)) *
        F l.val ((x : ℂ) + I * (t : ℂ))‖ ≤ L * ‖v x t‖ by
      calc 2 * π * ‖∑ l : U, eisensteinEval (B k l) ((x : ℂ) + I * (t : ℂ)) *
            F l.val ((x : ℂ) + I * (t : ℂ))‖ ≤ 2 * π * (L * ‖v x t‖) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = 2 * π * L * ‖v x t‖ := by ring
    calc ‖∑ l : U, eisensteinEval (B k l) ((x : ℂ) + I * (t : ℂ)) *
          F l.val ((x : ℂ) + I * (t : ℂ))‖
        ≤ ∑ l : U, ‖eisensteinEval (B k l) ((x : ℂ) + I * (t : ℂ)) *
          F l.val ((x : ℂ) + I * (t : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ l : U, eisBound (B k l) * ‖v x t‖ := by
          apply Finset.sum_le_sum
          intro l _
          rw [norm_mul]
          exact mul_le_mul (norm_eisensteinEval_le _ him) (norm_le_pi_norm (v x t) l)
            (norm_nonneg _) (eisBound_nonneg _)
      _ = (∑ l : U, eisBound (B k l)) * ‖v x t‖ := by rw [Finset.sum_mul]
      _ ≤ L * ‖v x t‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact Finset.single_le_sum (f := fun k : U => ∑ l : U, eisBound (B k l))
            (fun k _ => Finset.sum_nonneg fun l _ => eisBound_nonneg _) (Finset.mem_univ k)
  -- the initial bound on the segment `Im z = 1`
  have hcont : ContinuousOn (fun x : ℝ => v x 1) (Set.Icc 0 1) := by
    apply continuousOn_pi.2
    intro k
    have hc : ContinuousOn (F k.val) (imGT 0) := (hF.holo k.val).continuousOn
    refine hc.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro x _
    exact hmem x 1 one_pos
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hgr : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, 1 ≤ t →
      ‖v x t‖ ≤ D * Real.exp (K * (t - 1)) := by
    intro x hx t ht
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := v x)
      (f' := fun s k => _root_.deriv (F k.val) ((x : ℂ) + I * (s : ℂ)) * I)
      (δ := D) (K := K) (ε := 0) (a := 1) (b := t)
      (fun s hs => (hhas x s (by linarith [hs.1])).continuousAt.continuousWithinAt)
      (fun s hs => (hhas x s (by linarith [hs.1])).hasDerivWithinAt)
      (hD x hx) (fun s hs => hbound x s hs.1) t ⟨ht, le_rfl⟩
    rwa [gronwallBound_ε0] at h
  -- conclusion for an arbitrary insertion vector
  set Cw : ℝ := (∑ l : U, eisBound (c w l)) * |D| with hCw
  refine ⟨Cw, fun z hre0 hre1 him => ?_⟩
  have hz : z ∈ imGT 0 := by change (0 : ℝ) < z.im; linarith
  have hzeq : z = (z.re : ℂ) + I * (z.im : ℂ) := by
    rw [mul_comm]; exact (Complex.re_add_im z).symm
  have hg := hgen w ⟨z, hz⟩
  change F w z = ∑ l : U, eisensteinEval (c w l) z * F l.val z at hg
  have hv := hgr z.re ⟨hre0, hre1⟩ z.im him
  have hvl : ∀ l : U, ‖F l.val z‖ ≤ ‖v z.re z.im‖ := by
    intro l
    have := norm_le_pi_norm (v z.re z.im) l
    simpa [v, ← hzeq] using this
  rw [hg]
  calc ‖∑ l : U, eisensteinEval (c w l) z * F l.val z‖
      ≤ ∑ l : U, ‖eisensteinEval (c w l) z * F l.val z‖ := norm_sum_le _ _
    _ ≤ ∑ l : U, eisBound (c w l) * ‖v z.re z.im‖ := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_mul]
        exact mul_le_mul (norm_eisensteinEval_le _ him) (hvl l) (norm_nonneg _)
          (eisBound_nonneg _)
    _ = (∑ l : U, eisBound (c w l)) * ‖v z.re z.im‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ l : U, eisBound (c w l)) * (|D| * Real.exp (K * z.im)) := by
        apply mul_le_mul_of_nonneg_left _
          (Finset.sum_nonneg fun l _ => eisBound_nonneg _)
        refine hv.trans ?_
        apply mul_le_mul (le_abs_self D) _ (Real.exp_pos _).le (abs_nonneg D)
        apply Real.exp_le_exp.mpr
        nlinarith
    _ = Cw * Real.exp (K * z.im) := by rw [hCw]; ring

end VOA.Huang.GenusOne.Close
