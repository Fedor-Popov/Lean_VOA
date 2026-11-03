import VOA.Classification.COne.OrbPos12Analytic

/-! Removing the scalar monodromy from the action product. The normalized
product is single-valued and holomorphic across the logarithm cut in its
convergence region. The global product/reversed-product/iterate gluing and
the twisted Borcherds coefficient identity are not asserted here. -/
noncomputable section
namespace VOA.Classification.COne.OrbPos12
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit CategoryTheory
open VOA.Huang.TensorCat.HexagonClose OrbPos9 OrbPos10

/-- Factoring a fixed fractional power shifts every exponent by that power. -/
theorem normalized_exp_sum (c e : ℂ → ℂ) (r L : ℂ) :
    Complex.exp (-r * L) * (∑' w, c w * Complex.exp (e w * L)) =
      ∑' w, c w * Complex.exp ((e w - r) * L) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro w
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G))
  (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)
  (g : G) (hm : ActionMonodromyThrough G hSR X a g)
  (d : FourPointTest (ambient G) (ambient G) X X) (r : ℂ)
  (hx : g.1 d.x = Complex.exp (-(2 * Real.pi * Complex.I) * r) • d.x)

include hm hx

/-- Exponents of a nonzero action-product coefficient lie in the specified
coset of the integers. In a g-eigenspace one can take `r = j / orderOf g`. -/
theorem actionProduct_exponent_coset (w : ℂ)
    (hw : prodCoef (fusionChoice_pbw hSR) (actionProduct G hSR X a) d w ≠ 0) :
    ∃ n : ℤ, d.δ - d.α - w - r = n := by
  have he := actionProduct_coefficient_phase G hSR X a g hm d _ hx w hw
  rw [← Complex.exp_add, Complex.exp_eq_one_iff] at he
  obtain ⟨n, hn⟩ := he
  refine ⟨n, ?_⟩
  have hper : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  apply mul_right_cancel₀ hper
  linear_combination hn

/-- After removing the scalar monodromy, the action product depends only on
the exponential of its logarithmic coordinate. -/
theorem actionProduct_normalized_log_congr {L₁ L₂ : ℂ}
    (hL : Complex.exp L₁ = Complex.exp L₂) :
    Complex.exp (-r * L₁) * prodL (fusionChoice_pbw hSR) (actionProduct G hSR X a) d L₁ =
      Complex.exp (-r * L₂) * prodL (fusionChoice_pbw hSR) (actionProduct G hSR X a) d L₂ := by
  unfold prodL
  rw [normalized_exp_sum, normalized_exp_sum]
  exact VOA.Huang.HKLLoc.tsum_exp_congr _ _
    (actionProduct_exponent_coset G hSR X a g hm d r hx) hL

/-- The normalized product extends holomorphically across the principal-log
cut at every point outside the unit circle. This reuses HKL's branch descent. -/
theorem actionProduct_normalized_differentiable {z : ℂ} (hz : 1 < ‖z‖) :
    DifferentiableAt ℂ (fun z => Complex.exp (-r * Complex.log z) *
      prodL (fusionChoice_pbw hSR) (actionProduct G hSR X a) d (Complex.log z)) z := by
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  apply VOA.Huang.HKLLoc.differentiableAt_comp_clog
    (g := fun L => Complex.exp (-r * L) *
      prodL (fusionChoice_pbw hSR) (actionProduct G hSR X a) d L)
    (fun L₁ L₂ hL => actionProduct_normalized_log_congr G hSR X a g hm d r hx hL) hz0
  intro L hL
  have hre : 0 < L.re := by
    rw [VOA.Huang.HKLLoc.re_of_exp_eq hL]
    exact Real.log_pos hz
  exact ((differentiableAt_const (-r)).mul differentiableAt_id).cexp.mul
    (analyticOnNhd_prodL (fusionChoice_pbw hSR) hSR
      (actionProduct G hSR X a) d L hre).differentiableAt

end VOA.Classification.COne.OrbPos12
