import VOA.Huang.GenusOneWardMixed

/-!
# Third clause of `RawCuspCoordinateCollection`: the mixed omega identity
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.Separate
open VOA.Huang.GenusTwoPoint (moduleWeightExp moduleWeightExp_of_weight moduleWeightExp_add
  moduleWeightExp_zero logTwoPiI)
open VOA.Huang.GenusTwoPoint.QEquation (TailBound exists_tailBound ellipticCoeff Kernels)
open VOA.Huang.GenusOne.SquareModule (shiftedOmega)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section MixedClause
variable (hV : StronglyRational W)
  (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
  (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

theorem S_sq_left_omega {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (x : P₁.carrier) (y : P₂.carrier) (m : ℤ) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
        (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector m x) y =
      (huangModeScale m * wardPref N Q z₁ z₂ * (2 * (Real.pi : ℂ) * Complex.I) ^ 2) •
        evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂
          (GenusOne.SquareModule.sqMode P₁.isMod m (shiftedOmega W)
            (moduleWeightExp P₁.isMod (-Complex.log z₁) x))
          (moduleWeightExp P₂.isMod (-Complex.log z₂) y)) := by
  rw [S_sq_left, huangStateU_conformal, map_smul, LinearMap.smul_apply, map_smul,
    LinearMap.smul_apply, evF_smul, smul_smul]

theorem S_sq_right_omega {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (x : P₁.carrier) (y : P₂.carrier) (m : ℤ) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
        (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector m y) =
      (huangModeScale m * wardPref N Q z₁ z₂ * (2 * (Real.pi : ℂ) * Complex.I) ^ 2) •
        evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂
          (moduleWeightExp P₁.isMod (-Complex.log z₁) x)
          (GenusOne.SquareModule.sqMode P₂.isMod m (shiftedOmega W)
            (moduleWeightExp P₂.isMod (-Complex.log z₂) y))) := by
  rw [S_sq_right, huangStateU_conformal, map_smul, LinearMap.smul_apply, map_smul,
    evF_smul, smul_smul]

/-- **Third clause of `RawCuspCoordinateCollection`**: the mixed omega Ward
identity on the actual raw cusp trace. -/
theorem mixedClause {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    ∀ (x : P₁.carrier) (y : P₂.carrier), ∃ K,
      TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule W.conformalVector
        ((huangU P₁ (Complex.log z₁)).symm x) ((huangU P₂ (Complex.log z₂)).symm y) K ∧
      (2 * (Real.pi : ℂ) * Complex.I) ^ 2 • FuchsianODE.thetaShift (N.h - W.centralCharge / 24)
          (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y) +
        (cuspEnergyG2 hz₂ hz hr • (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
              (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector 1 x) y +
            productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
              (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector 1 y) +
            cuspLogCoordinate z₁ • productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
              (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector 0 x) y +
            cuspLogCoordinate z₂ • productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
              (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector 0 y)) -
          cuspEnergyP1 hz₂ hz hr • productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
            (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector 0 y)) =
      productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
          (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector (-1) x) y -
        (∑ k ∈ Finset.range K, (cuspWardKernels hz₂ hz hr).G k •
          productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
            (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector (2 * (k + 1) + 1) x) y) +
        ∑ m ∈ Finset.range K, ((-1 : SubexpPS) ^ (m + 1) * (cuspWardKernels hz₂ hz hr).Pleft m) •
          productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
            (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector (m + 1) y) := by
  intro x y
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have ht0 : z₂ / z₁ ≠ 0 := div_ne_zero hz₂ hz₁
  have ht : ‖z₂ / z₁‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz₁)]; exact hz
  have hEne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  set x' := moduleWeightExp P₁.isMod (-Complex.log z₁) x with hx'
  set y' := moduleWeightExp P₂.isMod (-Complex.log z₂) y with hy'
  obtain ⟨K₀, hK₀⟩ := mixedLHS_evZero Y₁ Y₂ x' y'
  obtain ⟨K₁, hK₁⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule
    W.conformalVector ((huangU P₁ (Complex.log z₁)).symm x) ((huangU P₂ (Complex.log z₂)).symm y)
  refine ⟨max K₀ K₁ + 1, fun j hj => hK₁ j (by omega), ?_⟩
  set K := max K₀ K₁ + 1 with hKdef
  have hΦ := conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz
  set E := 2 * (Real.pi : ℂ) * Complex.I with hE
  set p := wardPref N Q z₁ z₂ with hp
  set ev := evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) with hev_def
  set ω' := shiftedOmega W with hω'
  -- the formal identity, evaluated
  have hform := congrArg ev (hK₀ (K + 1) (by omega))
  rw [hev_def, evF_mixedLHS Y₁ Y₂ ht hΦ, evF_zero] at hform
  rw [← hev_def] at hform
  -- the zero-mode relation, evaluated
  have hzm := congrArg ev (Phi_zero_mode_shiftedOmega Y₁ Y₂ x' y')
  rw [hev_def, evF_add (hΦ _ _) (hΦ _ _), evF_zero] at hzm
  rw [← hev_def] at hzm
  push_cast at hform hzm
  -- abbreviations for the evaluated insertions
  have eA : E ^ 2 • FuchsianODE.thetaShift (N.h - W.centralCharge / 24)
      (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y) =
      (E ^ 2 * p) • ev (thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ x' y')) := by
    rw [S_plain hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y, map_smul, thetaShift_evF, smul_smul]
  have h1 := huangModeScale_mul_pow_succ 1
  have h0 := huangModeScale_mul_pow 0
  push_cast at h1 h0
  have eB1 : productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
      (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector 1 x) y =
      p • ev (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod 1 ω' x') y') := by
    rw [S_sq_left_omega]
    congr 1
    linear_combination p * h1
  have eB2 : productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
      (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector 1 y) =
      p • ev (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod 1 ω' y')) := by
    rw [S_sq_right_omega]
    congr 1
    linear_combination p * h1
  have eC1 : productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
      (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector 0 x) y =
      (E * p) • ev (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod 0 ω' x') y') := by
    rw [S_sq_left_omega]
    congr 1
    linear_combination p * h0
  have eC2 : productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
      (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector 0 y) =
      (E * p) • ev (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod 0 ω' y')) := by
    rw [S_sq_right_omega]
    congr 1
    linear_combination p * h0
  have eD : productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
      (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector (-1) x) y =
      (E ^ 2 * p) • ev (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (-1) ω' x') y') := by
    rw [S_sq_left_omega, huangModeScale_neg_one]
    congr 1
    ring
  have eE : ∀ k ∈ Finset.range K, (cuspWardKernels hz₂ hz hr).G k •
      productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
        (spatialSquareMode P₁ (Complex.log z₁) W.conformalVector (2 * (k + 1) + 1) x) y =
      (E ^ 2 * p) • (ev (eis (k + 2)) * ev (Phi Y₁ Y₂
        (GenusOne.SquareModule.sqMode P₁.isMod (2 * ((k : ℤ) + 1) + 1) ω' x') y')) := by
    intro k _
    rw [Subalgebra.smul_def, smul_eq_mul, S_sq_left_omega]
    have hG : (((cuspWardKernels hz₂ hz hr).G k : SubexpPS) : PowerSeries ℂ) =
        E ^ (2 * (k + 2)) • ev (eis (k + 2)) := by
      change eisensteinCuspSeries (k + 2) rho = _
      rw [eisensteinCuspSeries, hev_def, evF_eis ht0]
    have hsc : huangModeScale (2 * ((k : ℤ) + 1) + 1) * E ^ (2 * k + 3 + 1) = 1 := by
      have := huangModeScale_mul_pow_succ (2 * k + 3)
      rwa [show ((2 * k + 3 : ℕ) : ℤ) = 2 * ((k : ℤ) + 1) + 1 by push_cast; ring] at this
    rw [hG, smul_mul_smul_comm, ← hev_def, ← hx', ← hy', ← hω']
    congr 1
    rw [show 2 * (k + 2) = 2 * k + 3 + 1 by ring]
    linear_combination (E ^ 2 * p) * hsc
  have eF : ∀ m ∈ Finset.range K,
      ((-1 : SubexpPS) ^ (m + 1) * (cuspWardKernels hz₂ hz hr).Pleft m) •
        productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
          (spatialSquareMode P₂ (Complex.log z₂) W.conformalVector (m + 1) y) =
      (E ^ 2 * p) • (((if m = 0 then ev (eis 1) else 0) - ev (piK (m + 1))) *
        ev (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod ((m : ℤ) + 1) ω' y'))) := by
    intro m _
    rw [Subalgebra.smul_def, smul_eq_mul, S_sq_right_omega]
    have hco : (((-1 : SubexpPS) ^ (m + 1) * (cuspWardKernels hz₂ hz hr).Pleft m : SubexpPS) :
        PowerSeries ℂ) = (-1 : PowerSeries ℂ) ^ (m + 1) * wpCuspSeries (m + 1) (z₂ / z₁) 0 rho := by
      push_cast; rfl
    have hw := wpCusp_scale_mixed ht0 ht rho m
    rw [← hev_def] at hw
    push_cast at hw
    rw [hco, ← hev_def, ← hx', ← hy', ← hω']
    calc ((-1 : PowerSeries ℂ) ^ (m + 1) * wpCuspSeries (m + 1) (z₂ / z₁) 0 rho) *
          ((huangModeScale ((m : ℤ) + 1) * p * E ^ 2) •
            ev (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod ((m : ℤ) + 1) ω' y'))) =
        p • ((huangModeScale ((m : ℤ) + 1) • (E ^ 2 •
          ((-1 : PowerSeries ℂ) ^ (m + 1) * wpCuspSeries (m + 1) (z₂ / z₁) 0 rho))) *
            ev (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod ((m : ℤ) + 1) ω' y'))) := by
          rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul, smul_smul]
          congr 1
          ring
      _ = p • ((E ^ 2 • ((if m = 0 then ev (eis 1) else 0) - ev (piK (m + 1)))) *
            ev (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod ((m : ℤ) + 1) ω' y'))) := by
          rw [hw]
      _ = _ := by rw [smul_mul_assoc, smul_smul, mul_comm p]
  have hg : ((cuspEnergyG2 hz₂ hz hr : SubexpPS) : PowerSeries ℂ) = E ^ 2 • ev (eis 1) := by
    change eisensteinCuspSeries 1 rho = _
    rw [eisensteinCuspSeries, hev_def, evF_eis ht0]
  have hp1 := cuspEnergyP1_val hz₂ hz hr
  rw [← hev_def, ← hE] at hp1
  rw [← hω'] at hform hzm
  rw [eA, eB1, eB2, eC1, eC2, eD, Finset.sum_congr rfl eE, Finset.sum_congr rfl eF,
    Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, hg, hp1,
    ← Finset.smul_sum, ← Finset.smul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, if_pos (show 0 < K by omega), Nat.cast_zero, zero_add]
  have hs₁ : PowerSeries.C (cuspLogCoordinate z₁) * PowerSeries.C E =
      PowerSeries.C (Complex.log z₁) := by
    rw [← map_mul, cuspLogCoordinate, div_mul_cancel₀ _ hEne]
  have hs₂ : PowerSeries.C (cuspLogCoordinate z₂) * PowerSeries.C E =
      PowerSeries.C (Complex.log z₂) := by
    rw [← map_mul, cuspLogCoordinate, div_mul_cancel₀ _ hEne]
  simp only [PowerSeries.smul_eq_C_mul, map_mul, map_pow, map_sub] at hform hzm ⊢
  set R1 := ev (eis 1)
  set L0 := ev (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod 0 ω' x') y')
  set R0 := ev (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod 0 ω' y'))
  linear_combination (-(PowerSeries.C E ^ 2 * PowerSeries.C p)) * hform +
    (PowerSeries.C E ^ 2 * PowerSeries.C p * R1 * PowerSeries.C (Complex.log z₁)) * hzm +
    (PowerSeries.C E ^ 2 * PowerSeries.C p * R1 * L0) * hs₁ +
    (PowerSeries.C E ^ 2 * PowerSeries.C p * R1 * R0) * hs₂

end MixedClause

end VOA.Huang.GenusOneWard
