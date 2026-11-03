import VOA.Huang.NgSchauenburgGeneralizedTwist
import VOA.Huang.NgSchauenburgBalancing
import VOA.Huang.NgSchauenburgIndicatorGalois
import VOA.Huang.NgSchauenburgCongruenceDescent

/-! # Explicit modular-data formula from generalized equivariance

The formula below is a consequence of the still-open full equivariance theorem,
not a proof of that theorem. The degree-one twist formula used here is proved
categorically in `NgSchauenburgGeneralizedTwist`.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

/-- The word taking the row `(1,0)` to `(m,1)`, with our convention for S. -/
theorem rowAction_one_T_neg_S_inv (m : ℤ) :
    rowAction 1 0 (ModularGroup.T ^ (-m) * ModularGroup.S⁻¹) = (m, 1) := by
  simp [rowAction, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    ModularGroup.S_inv, ModularGroup.coe_S]

theorem modularInvolution_T_neg_S_inv (m : ℤ) :
    modularInvolution (ModularGroup.T ^ (-m) * ModularGroup.S⁻¹) =
      ModularGroup.T ^ m * ModularGroup.S := by
  change modularOuterAutomorphism (_ * _) = _
  rw [map_mul, map_zpow, map_inv]
  change (modularInvolution ModularGroup.T) ^ (-m) *
    (modularInvolution ModularGroup.S)⁻¹ = _
  rw [modularInvolution_T, modularInvolution_S]
  simp

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [RightRigidCategory (Center C)] [HasKernels (Center C)] [HasFiniteBiproducts (Center C)]

/-- Integer powers of the pinned raw T action. -/
theorem canonicalCenter_T_zpow (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (m : ℤ) (z : Z.Label → ℂ)
    (i : Z.Label) : ρ (ModularGroup.T ^ m) z i = M.twistScalar i ^ m * z i := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one, map_mul]
      change ρ (ModularGroup.T ^ (n : ℤ)) (ρ ModularGroup.T z) i = _
      rw [ih, hr.2.2.2, zpow_add_one₀ (M.toRibbon.twistScalar_ne_zero i)]
      ring
  | pred n ih =>
      have hi (w : Z.Label → ℂ) : ρ ModularGroup.T⁻¹ w i =
          (M.twistScalar i)⁻¹ * w i := by
        have h := hr.2.2.2 (ρ ModularGroup.T⁻¹ w) i
        have hc : ρ ModularGroup.T (ρ ModularGroup.T⁻¹ w) = w := by
          rw [map_inv]; exact (ρ ModularGroup.T).apply_symm_apply w
        rw [hc] at h
        rw [h]
        simp [M.toRibbon.twistScalar_ne_zero i]
      rw [zpow_sub_one, map_mul]
      change ρ (ModularGroup.T ^ (-(n : ℤ))) (ρ ModularGroup.T⁻¹ z) i = _
      rw [ih, hi, zpow_sub_one₀ (M.toRibbon.twistScalar_ne_zero i)]
      ring

/-- The canonical center action has exactly the raw categorical T order. -/
theorem canonicalCenter_T_pow_eq_one_iff (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (n : ℕ) :
    (ρ ModularGroup.T) ^ n = 1 ↔ M.toRibbon.twistOrder ∣ n := by
  have hp (z : Z.Label → ℂ) (i : Z.Label) :
      ((ρ ModularGroup.T) ^ n) z i = M.twistScalar i ^ n * z i := by
    simpa using canonicalCenter_T_zpow F Z M ρ hr (n : ℤ) z i
  rw [Ribbon.twistOrder, orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    funext i
    have hi := hp (fun _ => 1) i
    simpa [h] using hi.symm
  · intro h
    ext z i
    rw [hp]
    have hi := congrFun h i
    simpa using congrArg (fun a : ℂ => a * z i) hi

theorem canonicalCenter_T_orderOf (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) :
    orderOf (ρ ModularGroup.T) = M.toRibbon.twistOrder := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_iff_pow_eq_one.mpr
      ((canonicalCenter_T_pow_eq_one_iff F Z M ρ hr _).mpr dvd_rfl)
  · exact (canonicalCenter_T_pow_eq_one_iff F Z M ρ hr _).mp (pow_orderOf_eq_one _)

/-- A proved indicator-row periodicity result, requiring no full equivariance. -/
theorem generalizedIndicator_one_periodic (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (i : Z.Label) (l : ℤ) :
    generalizedIndicatorAll F (Z.simple i) V 1 (l + M.toRibbon.twistOrder) =
      generalizedIndicatorAll F (Z.simple i) V 1 l := by
  have hp : M.twistScalar i ^ M.toRibbon.twistOrder = 1 :=
    congrFun (pow_orderOf_eq_one (fun j : Z.Label => M.twistScalar j)) i
  rw [generalizedIndicatorAll_one_twist F Z M ρ hr,
    generalizedIndicatorAll_one_twist F Z M ρ hr, neg_add,
    zpow_add₀ (M.toRibbon.twistScalar_ne_zero i)]
  simp [zpow_neg, hp]

/-- NS's `(m,1)` formula with all normalizations explicit. Full generalized
equivariance is an explicit hypothesis; no symmetry of S is needed. -/
theorem generalizedIndicator_m_one_of_equivariance (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (he : GeneralizedIndicatorEquivariance F Z M)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (m : ℤ) (i : Z.Label) :
    generalizedIndicatorAll F (Z.simple i) V m 1 =
      F.globalDimension⁻¹ * ∑ j,
        M.twistScalar j ^ m * categoricalS Z j i *
          (Module.finrank ℂ ((Z.simple j).1 ⟶ V) : ℂ) := by
  classical
  have h := he ρ hr V 1 0 (ModularGroup.T ^ (-m) * ModularGroup.S⁻¹) (Pi.single i 1)
  rw [rowAction_one_T_neg_S_inv, modularInvolution_T_neg_S_inv,
    equivariantIndicator_basis, equivariantIndicator_one_zero, map_mul] at h
  rw [h]
  simp only [LinearEquiv.mul_apply, canonicalCenter_T_zpow F Z M ρ hr, hr.2.2.1]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end VOA.Huang.NgSchauenburg
