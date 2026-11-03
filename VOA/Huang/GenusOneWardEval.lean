import VOA.Huang.GenusOneWardEvalKernels
import VOA.Huang.GenusTwoPointSepCoordinateCollection

/-!
# The actual evaluated trace as the evaluation of `Phi`

Every row of `Phi Y₁ Y₂ x y` is the library's `rawLevelSeries`, absolutely
convergent at `t₀ = z₂/z₁` by genus-zero convergence. With the insertions
rescaled by `exp(log zᵢ · L₀)`, the actual raw cusp trace is a fixed nonzero
constant times `evF t₀ (ρ/t₀) (Phi x y)`; all weight-dependent principal powers
cancel exactly.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.Separate
open VOA.Huang.GenusTwoPoint (moduleWeightExp moduleWeightExp_of_weight moduleWeightExp_add
  moduleWeightExp_zero logTwoPiI)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section Eval
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

theorem phiH_row (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (n : ℕ) :
    PowerSeries.coeff n (phiH Y₁ Y₂ x y α₁ α₂) = rawLevelSeries Y₁ Y₂ x y α₁ α₂ (N.h + n) := by
  ext k
  change c2 (phiH Y₁ Y₂ x y α₁ α₂) n k = _
  simp only [phiH, c2_mk2, tauZ, lvl, rawLevelSeries, PowerSeries.coeff_mk,
    GenusTwoPoint.productModeTrace]
  congr 1
  · congr 2
    · unfold sMode; push_cast; ring
    · unfold rMode; push_cast; ring
  · push_cast; ring

theorem conv_Phi (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (x : P₁.carrier) (y : P₂.carrier) :
    Conv (z₂ / z₁) (Phi Y₁ Y₂ x y) := by
  refine FusionTop.induction_weight P₁.isMod x (by simpa using conv_zero _)
    (fun a b ha hb => by simpa only [map_add, LinearMap.add_apply] using ha.add hb) ?_
  intro α₁ x hx
  refine FusionTop.induction_weight P₂.isMod y (by simpa using conv_zero _)
    (fun a b ha hb => by simpa only [map_add] using ha.add hb) ?_
  intro α₂ y hy
  rw [Phi_homog Y₁ Y₂ hx hy]
  intro n
  rw [phiH_row]
  exact rawLevelSeries_spatialSummable hV i₁ i₂ iN Y₁ Y₂ hx hy (N.h + n) hz₂ hz

/-- The weight-independent prefactor. -/
def wardPref (N Q : LWModule W) (z₁ z₂ : ℂ) : ℂ := z₁ ^ (N.h - Q.h) * z₂ ^ (Q.h - N.h)

theorem exp_log_mul_cpow {z : ℂ} (hz : z ≠ 0) (a b : ℂ) :
    Complex.exp (Complex.log z * a) * z ^ b = z ^ (a + b) := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.cpow_def_of_ne_zero hz, ← Complex.exp_add]
  ring_nf

/-- **The bridge**: the actual raw cusp trace of `L₀`-rescaled insertions is
the spatial evaluation of `Phi`, times a fixed constant. -/
theorem productCuspSeries_weightExp (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) (x : P₁.carrier) (y : P₂.carrier) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
        (moduleWeightExp P₁.isMod (Complex.log z₁) x)
        (moduleWeightExp P₂.isMod (Complex.log z₂) y) =
      wardPref N Q z₁ z₂ • evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂ x y) := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  refine FusionTop.induction_weight P₁.isMod x (by simp [evF_zero]) (fun a b ha hb => ?_) ?_
  · rw [map_add, map_add, LinearMap.add_apply, ha, hb, map_add, LinearMap.add_apply,
      evF_add (conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz a y) (conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz b y),
      smul_add]
  intro α₁ x hx
  refine FusionTop.induction_weight P₂.isMod y (by simp [evF_zero]) (fun a b ha hb => ?_) ?_
  · rw [map_add, map_add, ha, hb, map_add,
      evF_add (conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz x a) (conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz x b),
      smul_add]
  intro α₂ y hy
  rw [moduleWeightExp_of_weight _ _ hx, moduleWeightExp_of_weight _ _ hy, map_smul, map_smul,
    LinearMap.smul_apply, Phi_homog Y₁ Y₂ hx hy]
  ext n
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul,
    coeff_productCuspSeries_spatialEval hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz,
    PowerSeries.coeff_smul, coeff_evF, rawSpatialPrefactor_add_nat Q α₁ α₂ N.h hz₁ hz₂]
  have hrow : ∑' k, c2 (phiH Y₁ Y₂ x y α₁ α₂) n k * (z₂ / z₁) ^ k =
      spatialEval (z₂ / z₁) ⟨rawLevelSeries Y₁ Y₂ x y α₁ α₂ (N.h + n),
        rawLevelSeries_spatialSummable hV i₁ i₂ iN Y₁ Y₂ hx hy (N.h + n) hz₂ hz⟩ := by
    change ∑' k, PowerSeries.coeff k (PowerSeries.coeff n (phiH Y₁ Y₂ x y α₁ α₂)) *
      (z₂ / z₁) ^ k = _
    rw [phiH_row]
    rfl
  rw [hrow]
  simp only [smul_eq_mul, rawSpatialPrefactor, wardPref]
  have e1 := exp_log_mul_cpow hz₁ α₁ (N.h - Q.h - α₁)
  have e2 := exp_log_mul_cpow hz₂ α₂ (Q.h - N.h - α₂)
  rw [show α₁ + (N.h - Q.h - α₁) = N.h - Q.h by ring] at e1
  rw [show α₂ + (Q.h - N.h - α₂) = Q.h - N.h by ring] at e2
  rw [← e1, ← e2, mul_pow, inv_pow]
  ring

end Eval

end VOA.Huang.GenusOneWard
