import VOA.Huang.NgSchauenburgCentralOrder
import VOA.Huang.NgSchauenburgModularFormula

/-! # General T-equivariance and finite order of central rotations

The formulas concern the existing integer-index indicators. S-equivariance
and the smaller cyclotomic field bound are not assumed or proved here.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- The zero-degree indicator is supported on twist eigenvalue one. -/
theorem generalizedIndicatorAll_zero_twist (F : SphericalFusion C) (A : Center C)
    (V : C) {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j A.1).hom = t • centralDrinfeldMorphism A) (l : ℤ) :
    generalizedIndicatorAll F A V 0 l = t⁻¹ * generalizedIndicatorAll F A V 0 l := by
  have hf (f : A.1 ⟶ 𝟙_ C) : t⁻¹ • f = f := by
    rw [← generalizedRotation_one_scalar F.toPivotal A (𝟙_ C) ht hj,
      generalizedRotation_unit_output]
  have he : t⁻¹ • closedRotation F.toPivotal A (signedTensorPower V l) =
      closedRotation F.toPivotal A (signedTensorPower V l) := by
    ext f
    exact hf _
  have h := congrArg (LinearMap.trace ℂ (A.1 ⟶ 𝟙_ C)) he
  simpa [generalizedIndicatorAll, map_smul] using h.symm

/-- The twist shift holds for every integer pair, including negative and zero degrees. -/
theorem generalizedIndicatorAll_add_degree (F : SphericalFusion C) (A : Center C)
    (V : C) {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j A.1).hom = t • centralDrinfeldMorphism A) (m l : ℤ) :
    generalizedIndicatorAll F A V m (l + m) =
      t⁻¹ * generalizedIndicatorAll F A V m l := by
  rcases lt_trichotomy 0 m with hm | hm | hm
  · have hc : ((m.toNat - 1 + 1 : ℕ) : ℤ) = m := by omega
    simpa only [generalizedIndicatorAll, if_pos hm, hc] using
      generalizedIndicatorInt_add_degree F A V (m.toNat - 1) ht hj l
  · subst m
    simpa using generalizedIndicatorAll_zero_twist F A V ht hj l
  · have hpos : ¬ 0 < m := by omega
    have hzero : ¬ m = 0 := by omega
    have hc : - (l + m) = -l + (m.natAbs - 1 + 1 : ℕ) := by omega
    simp only [generalizedIndicatorAll, if_neg hpos, if_neg hzero, hc]
    exact generalizedIndicatorInt_add_degree F A Vᘁ (m.natAbs - 1) ht hj (-l)

section Center
variable [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]
open scoped MatrixGroups

/-- T-equivariance on the whole integer lattice for the pinned center representation. -/
theorem equivariantIndicator_T (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (m l : ℤ) (z : Z.Label → ℂ) :
    equivariantIndicator F Z.simple V m (l + m) z =
      equivariantIndicator F Z.simple V m l (ρ ModularGroup.T⁻¹ z) := by
  have hi (i : Z.Label) : ρ ModularGroup.T⁻¹ z i = (M.twistScalar i)⁻¹ * z i := by
    simpa using canonicalCenter_T_zpow F Z M ρ hr (-1) z i
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk, hi]
  apply Finset.sum_congr rfl
  intro i _
  rw [generalizedIndicatorAll_add_degree F (Z.simple i) V
    (M.toRibbon.twistScalar_ne_zero i) (hr.2.1 i)]
  ring

/-- The actual central rotations have positive finite period dividing degree times
center twist order. This is independent of full SL₂-equivariance. -/
theorem generalizedRotation_center_period (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (i : Z.Label) (n : ℕ) :
    0 < (n + 1) * M.toRibbon.twistOrder ∧
      (generalizedRotation F.toPivotal (Z.simple i) V n).toLinearMap ^
        ((n + 1) * M.toRibbon.twistOrder) = 1 := by
  refine ⟨Nat.mul_pos (Nat.succ_pos n) M.toRibbon.finite_twist.1, ?_⟩
  apply generalizedRotation_pow_mul_eq_one F.toPivotal (Z.simple i) V n
    M.toRibbon.twistOrder (M.toRibbon.twistScalar_ne_zero i) (hr.2.1 i)
  exact congrFun (pow_orderOf_eq_one (fun j : Z.Label => M.twistScalar j)) i

/-- Integral cyclotomicity in the degree-times-twist-order field. This does not
assert the smaller field required by the congruence argument. -/
theorem generalizedIndicator_center_cyclotomic (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (i : Z.Label) (n l : ℕ) :
    generalizedIndicator F.toPivotal (Z.simple i) V n l ∈
      Algebra.adjoin ℤ ({Complex.exp
        (2 * Real.pi * Complex.I / ((n + 1) * M.toRibbon.twistOrder))} : Set ℂ) := by
  letI := F.homFinite (Z.simple i).1 (tensorPower V (n + 1))
  obtain ⟨hp, he⟩ := generalizedRotation_center_period F Z M ρ hr V i n
  have hel : ((generalizedRotation F.toPivotal (Z.simple i) V n).toLinearMap ^ l) ^
      ((n + 1) * M.toRibbon.twistOrder) = 1 := by
    rw [← pow_mul, Nat.mul_comm l, pow_mul, he, one_pow]
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    trace_mem_standardCyclotomicIntegers _ hp hel

/-- The Galois consumer does not need an assumed rotation-order identity.
Only its smaller cyclotomic-field premise remains. -/
theorem generalizedIndicator_mul_eq_of_center_modEq (F : SphericalFusion C)
    (Z : SphericalFusion (Center C)) (M : Modular Z)
    (ρ : SL(2, ℤ) →* ((Z.Label → ℂ) ≃ₗ[ℂ] (Z.Label → ℂ)))
    (hr : CanonicalCenterRepresentation F Z M ρ) (V : C) (i : Z.Label) (n l : ℕ)
    {k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ ((n + 1) * M.toRibbon.twistOrder))
    (hk : Nat.Coprime k ((n + 1) * M.toRibbon.twistOrder))
    (hmod : Nat.ModEq M.toRibbon.twistOrder k 1)
    (hmem : generalizedIndicator F.toPivotal (Z.simple i) V n l ∈
      Algebra.adjoin ℚ ({ζ ^ (n + 1)} : Set ℂ)) :
    generalizedIndicator F.toPivotal (Z.simple i) V n (k * l) =
      generalizedIndicator F.toPivotal (Z.simple i) V n l := by
  exact generalizedIndicator_mul_eq_of_modEq F (Z.simple i) V n l
    M.toRibbon.finite_twist.1
    (generalizedRotation_center_period F Z M ρ hr V i n).2 hζ hk hmod hmem

end Center
end VOA.Huang.NgSchauenburg
