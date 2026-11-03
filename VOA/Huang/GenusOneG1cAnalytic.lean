import Mathlib

/-!
# Holomorphy of generalized power series and a real-segment identity theorem

Two elementary analytic tools for the complex overlap of the genus-one channels:

* `differentiableOn_tsum_cpow`: a series `Σ c_i w^{e_i}` (principal complex powers, exponents with
  a COMMON imaginary part) that converges at two positive reals `t₁ < t₂` is holomorphic on the
  open sector-annulus `{Re w > 0, t₁ < ‖w‖ < t₂}`. Domination: on that set
  `‖w^{e}‖ ≤ (t₁^{Re e} + t₂^{Re e}) e^{π|m|/2}` (`m` the common imaginary part), and convergence
  in `ℂ` is absolute (`summable_norm_iff`).
* `eqOn_of_real_segment`: two holomorphic functions on an open convex set that agree on a real
  segment inside it agree on the whole set (Mathlib's identity theorem, with the accumulation
  point supplied by the segment).

No VOA content; no axioms beyond Lean's three.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open Complex Filter Topology

/-- For `t₁ ≤ t ≤ t₂` (positive), `t^a ≤ t₁^a + t₂^a` for every real `a`. -/
theorem rpow_le_add_of_mem {t₁ t₂ t a : ℝ} (ht₁ : 0 < t₁) (h₁ : t₁ ≤ t) (h₂ : t ≤ t₂) :
    t ^ a ≤ t₁ ^ a + t₂ ^ a := by
  have ht : 0 < t := lt_of_lt_of_le ht₁ h₁
  have hp₁ : 0 ≤ t₁ ^ a := Real.rpow_nonneg ht₁.le a
  have hp₂ : 0 ≤ t₂ ^ a := Real.rpow_nonneg (ht₁.le.trans (h₁.trans h₂)) a
  rcases le_or_gt 0 a with ha | ha
  · have := Real.rpow_le_rpow ht.le h₂ ha
    linarith
  · have := Real.rpow_le_rpow_of_nonpos ht₁ h₁ ha.le
    linarith

/-- Bound on a principal power in the right half-plane. -/
theorem norm_cpow_le_of_re_pos {w e : ℂ} (hw : 0 < w.re) :
    ‖w ^ e‖ ≤ ‖w‖ ^ e.re * Real.exp (Real.pi / 2 * |e.im|) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  rw [Complex.norm_cpow_of_ne_zero hw0, div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.exp_le_exp.mpr
  have harg : |w.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hw.le
  have h1 : |w.arg * e.im| ≤ Real.pi / 2 * |e.im| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right harg (abs_nonneg _)
  have h2 := neg_abs_le (w.arg * e.im)
  linarith

/-- The open domain `{Re w > 0, t₁ < ‖w‖ < t₂}`. -/
def sectorAnnulus (t₁ t₂ : ℝ) : Set ℂ := {w | 0 < w.re} ∩ {w | t₁ < ‖w‖} ∩ {w | ‖w‖ < t₂}

theorem isOpen_sectorAnnulus (t₁ t₂ : ℝ) : IsOpen (sectorAnnulus t₁ t₂) :=
  ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const continuous_norm)).inter
    (isOpen_lt continuous_norm continuous_const)

/-- **Holomorphy of a generalized power series** with exponents of common imaginary part,
from convergence at two positive real points. -/
theorem differentiableOn_tsum_cpow {ι : Type*} (c e : ι → ℂ) (m : ℝ) (he : ∀ i, (e i).im = m)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁)
    (h₁ : Summable fun i => c i * ((t₁ : ℂ)) ^ (e i))
    (h₂ : Summable fun i => c i * ((t₂ : ℂ)) ^ (e i)) :
    DifferentiableOn ℂ (fun w => ∑' i, c i * w ^ (e i)) (sectorAnnulus t₁ t₂) := by
  set K : ℝ := Real.exp (Real.pi / 2 * |m|) with hK
  have hn₁ := summable_norm_iff.mpr h₁
  have hn₂ := summable_norm_iff.mpr h₂
  refine differentiableOn_tsum_of_summable_norm (u := fun i =>
      (‖c i * ((t₁ : ℂ)) ^ (e i)‖ + ‖c i * ((t₂ : ℂ)) ^ (e i)‖) * K)
    ((hn₁.add hn₂).mul_right K) ?_ (isOpen_sectorAnnulus t₁ t₂) ?_
  · intro i w hw
    have hre : 0 < w.re := hw.1.1
    have hsl : w ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
    exact ((differentiableAt_id.cpow (differentiableAt_const (e i)) hsl).const_mul
      (c i)).differentiableWithinAt
  · intro i w hw
    obtain ⟨⟨hre, hlo⟩, hhi⟩ := hw
    simp only [Set.mem_setOf_eq] at hre hlo hhi
    have ht₂ : 0 < t₂ := ht₁.trans (hlo.trans hhi)
    have hb := norm_cpow_le_of_re_pos (e := e i) hre
    rw [he i] at hb
    have hr := rpow_le_add_of_mem (a := (e i).re) ht₁ hlo.le hhi.le
    have hn1 : ‖c i * ((t₁ : ℂ)) ^ (e i)‖ = ‖c i‖ * t₁ ^ (e i).re := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₁]
    have hn2 : ‖c i * ((t₂ : ℂ)) ^ (e i)‖ = ‖c i‖ * t₂ ^ (e i).re := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₂]
    change ‖c i * w ^ e i‖ ≤ (‖c i * ((t₁ : ℂ)) ^ (e i)‖ + ‖c i * ((t₂ : ℂ)) ^ (e i)‖) * K
    rw [hn1, hn2, norm_mul]
    have hK0 : 0 ≤ K := (Real.exp_pos _).le
    calc ‖c i‖ * ‖w ^ e i‖ ≤ ‖c i‖ * (‖w‖ ^ (e i).re * K) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ ‖c i‖ * ((t₁ ^ (e i).re + t₂ ^ (e i).re) * K) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hK0) (norm_nonneg _)
      _ = (‖c i‖ * t₁ ^ (e i).re + ‖c i‖ * t₂ ^ (e i).re) * K := by ring

/-- **Identity theorem from a real segment** on an open convex domain. -/
theorem eqOn_of_real_segment {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : Convex ℝ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {a b : ℝ} (hab : a < b)
    (hsub : ∀ s : ℝ, a < s → s < b → (s : ℂ) ∈ U)
    (heq : ∀ s : ℝ, a < s → s < b → f s = g s) : Set.EqOn f g U := by
  set s₀ : ℝ := (a + b) / 2 with hs₀
  have ha₀ : a < s₀ := by rw [hs₀]; linarith
  have hb₀ : s₀ < b := by rw [hs₀]; linarith
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    hc.isPreconnected (hsub s₀ ha₀ hb₀) ?_
  rw [Metric.nhdsWithin_basis_ball.frequently_iff]
  intro ε hε
  set η : ℝ := min ε (b - s₀) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; exact half_pos (lt_min hε (by linarith))
  have hηε : η < ε := by
    rw [hη]; have := min_le_left ε (b - s₀); linarith
  have hηb : η < b - s₀ := by
    rw [hη]; have := min_le_right ε (b - s₀); linarith
  refine ⟨((s₀ + η : ℝ) : ℂ), ⟨?_, ?_⟩, heq _ (by linarith) (by linarith)⟩
  · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, show s₀ + η - s₀ = η by ring, abs_of_pos hη0]
    exact hηε
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := Complex.ofReal_injective h
    linarith

end VOA.Huang.GenusOneG1c
