import VOA.Huang.NgSchauenburgTOrbits

/-! # Center dimension forced by the canonical modular normalization

A canonical center representation has S normalized by the base global dimension.
Its order-four relation forces the center global dimension to be the square of
that normalizing dimension. Positivity rules out the negative square root.

This proves the dimension equality under the existing representation contract;
it does not construct that representation or prove the general center theorem.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
open scoped MatrixGroups
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- The square of the pinned S action, before determining its scalar. -/
theorem canonicalCenter_S_square (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (z : Z.Label → ℂ) (i : Z.Label) :
    ρ ModularGroup.S (ρ ModularGroup.S z) i =
      (F.globalDimension⁻¹ ^ 2 * Z.globalDimension) * z (Z.dualLabel i) := by
  classical
  simp only [hr.2.2.1]
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  have h (k : Z.Label) :
      (∑ j, F.globalDimension⁻¹ * categoricalS Z i j * F.globalDimension⁻¹ *
        categoricalS Z j k * z k) =
      F.globalDimension⁻¹ ^ 2 *
        (∑ j, categoricalS Z i j * categoricalS Z j k) * z k := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [h]
  have hsum (k : Z.Label) : (∑ j, categoricalS Z i j * categoricalS Z j k) =
      if k = Z.dualLabel i then Z.globalDimension else 0 := by
    simpa only [Matrix.mul_apply, Matrix.smul_apply, chargeConjugation,
      smul_eq_mul, mul_ite, mul_one, mul_zero] using
      congrArg (fun A : Matrix Z.Label Z.Label ℂ => A i k) (categoricalS_sq Z M)
  simp [hsum]

/-- The fourth power of S determines the square of the normalizing scalar. -/
theorem canonicalCenter_dimension_square (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) :
    (F.globalDimension⁻¹ ^ 2 * Z.globalDimension) ^ 2 = 1 := by
  have hs : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by decide
  have he : ρ ModularGroup.S (ρ ModularGroup.S
      (ρ ModularGroup.S (ρ ModularGroup.S (fun _ => 1)))) = (fun _ => 1) := by
    have hp : (ρ ModularGroup.S) ^ 4 = 1 := by rw [← map_pow, hs, map_one]
    have h := congrArg (fun g : (Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ) =>
      g (fun _ => 1)) hp
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have h := congrFun he Z.unitLabel
  rw [canonicalCenter_S_square F Z M ρ hr,
    canonicalCenter_S_square F Z M ρ hr] at h
  simpa only [mul_one, pow_two] using h

/-- The dimension equality follows from an existing canonical representation.
Existence of such a representation is not assumed to have been constructed. -/
theorem center_globalDimension_of_canonicalRepresentation (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) :
    Z.globalDimension = F.globalDimension ^ 2 := by
  obtain ⟨d, hd, hF⟩ := F.globalDimension_pos
  obtain ⟨e, he, hZ⟩ := Z.globalDimension_pos
  have h := canonicalCenter_dimension_square F Z M ρ hr
  rw [hF, hZ] at h
  have hreal : (d⁻¹ ^ 2 * e) ^ 2 = (1 : ℝ) := by exact_mod_cast h
  have hpos : 0 < d⁻¹ ^ 2 * e := mul_pos (sq_pos_of_pos (inv_pos.mpr hd)) he
  have hone : d⁻¹ ^ 2 * e = 1 := by nlinarith
  have hdim : e = d ^ 2 := by
    have hd0 := ne_of_gt hd
    field_simp at hone
    nlinarith
  rw [hZ, hF, hdim]
  push_cast
  rfl

/-- With the forced dimension, S squared is exactly charge conjugation. -/
theorem canonicalCenter_S_square_dual (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (z : Z.Label → ℂ) (i : Z.Label) :
    ρ ModularGroup.S (ρ ModularGroup.S z) i = z (Z.dualLabel i) := by
  rw [canonicalCenter_S_square F Z M ρ hr,
    center_globalDimension_of_canonicalRepresentation F Z M ρ hr]
  simp [F.globalDimension_ne_zero]

variable [BraidedCategory C]

/-- The existing canonical-representation contract supplies the missing
numerical premise of the mixed-label exhaustion theorem. -/
theorem mixedCenter_exhausts_of_canonicalRepresentation (F : SphericalFusion C)
    (M : Modular F) (Z : SphericalFusion (Center C)) (MZ : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z MZ ρ) (A : Center C) [Simple A] :
    ∃ i j : F.Label, Nonempty (A ≅ mixedCenter (F.simple i) (F.simple j)) :=
  mixedCenter_exhausts_simples_of_globalDimension F M Z hr.1
    (center_globalDimension_of_canonicalRepresentation F Z MZ ρ hr) A

end VOA.Huang.NgSchauenburg
