import VOA.Huang.NgSchauenburgSemisimple

/-! # Determinants on categorical Hom spaces -/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits

/-- Determinant of a scalar on each component of a dependent finite product. -/
theorem det_of_scalar_components {J : Type*} [Fintype J]
    {M : J → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, FiniteDimensional ℂ (M i)]
    (f : Module.End ℂ (∀ i, M i)) (c : J → ℂ)
    (h : ∀ x i, f x i = c i • x i) :
    f.det = ∏ i, c i ^ Module.finrank ℂ (M i) := by
  classical
  let b := Pi.basis (fun i => Module.finBasis ℂ (M i))
  have hb (k) : f (b k) = c k.1 • b k := by
    funext i
    rw [h]
    by_cases hi : i = k.1
    · subst i; rfl
    · simp [b, Pi.basis_apply, hi]
  have hm : LinearMap.toMatrix b b f = Matrix.diagonal (fun k => c k.1) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Fintype.prod_sigma]
  simp

/-- Determinant from scalar coordinates under a specified linear equivalence. -/
theorem det_of_scalar_coordinates {J : Type*} [Fintype J]
    {M : J → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, FiniteDimensional ℂ (M i)]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] (∀ i, M i)) (f : Module.End ℂ V) (c : J → ℂ)
    (h : ∀ x i, e (f x) i = c i • e x i) :
    f.det = ∏ i, c i ^ Module.finrank ℂ (M i) := by
  classical
  rw [← LinearMap.det_conj f e]
  apply det_of_scalar_components
  intro x i
  simpa using h (e.symm x) i

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The endomorphism of a Hom space induced by postcomposition. -/
def homPost (Z : C) {X : C} (f : X ⟶ X) : Module.End ℂ (Z ⟶ X) where
  toFun g := g ≫ f
  map_add' g h := by simp [Preadditive.add_comp]
  map_smul' z g := by simp

/-- Determinant of postcomposition, with the Hom space retained in the notation. -/
def homDet (Z : C) {X : C} (f : X ⟶ X) : ℂ := (homPost Z f).det

@[simp] theorem homPost_apply (Z : C) {X : C} (f : X ⟶ X) (g : Z ⟶ X) :
    homPost Z f g = g ≫ f := rfl

theorem homDet_comp (Z : C) {X : C} (f g : X ⟶ X) :
    homDet Z (f ≫ g) = homDet Z f * homDet Z g := by
  classical
  have h : homPost Z (f ≫ g) = (homPost Z g).comp (homPost Z f) := by
    ext x; simp [Category.assoc]
  simp [homDet, h, LinearMap.det_comp, mul_comm]

theorem homDet_conj (Z : C) {X Y : C} (e : X ≅ Y) (f : Y ⟶ Y) :
    homDet Z (e.hom ≫ f ≫ e.inv) = homDet Z f := by
  classical
  let E := homCongr (Iso.refl Z) e.symm
  have h : homPost Z (e.hom ≫ f ≫ e.inv) =
      E.toLinearMap.comp ((homPost Z f).comp E.symm.toLinearMap) := by
    ext x
    simp [E, homCongr, Category.assoc]
  unfold homDet
  rw [h]
  exact LinearMap.det_conj (homPost Z f) E

variable [BraidedCategory C]

/-- Double braiding, with its source and target order fixed. -/
def monodromy (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (β_ X Y).hom ≫ (β_ Y X).hom

/-- The hexagon determinant relation before decomposition into simple channels. -/
theorem homDet_monodromy_tensor (W X Y Z : C) :
    homDet W (monodromy (X ⊗ Y) Z) =
      homDet W (monodromy X Z ▷ Y) * homDet W (X ◁ monodromy Y Z) := by
  classical
  let e : (X ⊗ Y) ⊗ Z ≅ (X ⊗ Z) ⊗ Y :=
    (α_ X Y Z) ≪≫ whiskerLeftIso X (β_ Y Z) ≪≫ (α_ X Z Y).symm
  have h : monodromy (X ⊗ Y) Z =
      (e.hom ≫ monodromy X Z ▷ Y ≫ e.inv) ≫
        ((α_ X Y Z).hom ≫ X ◁ monodromy Y Z ≫ (α_ X Y Z).inv) := by
    simp [monodromy, e, BraidedCategory.braiding_tensor_left_hom,
      BraidedCategory.braiding_tensor_right_hom]
  rw [h, homDet_comp, homDet_conj, homDet_conj]

attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C]

namespace SphericalFusion
variable (F : SphericalFusion C)

/-- Products over summands regroup with intrinsic Hom multiplicities as exponents. -/
theorem prod_decomposition {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (c : F.Label → ℂ) :
    (∏ k, c (a k)) = ∏ i, c i ^ Module.finrank ℂ (F.simple i ⟶ X) := by
  classical
  simp only [F.multiplicity_eq_card e, ← Finset.prod_const]
  rw [← Finset.prod_fiberwise_of_maps_to (f := fun k => c (a k))
    (fun k _ => Finset.mem_univ (a k))]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k hk => by
    rw [(Finset.mem_filter.mp hk).2]

end SphericalFusion

namespace Ribbon
variable {F : SphericalFusion C} (R : Ribbon F.toPivotal)

/-- The dual form of the channel eigenvalue equation, on a projection to a simple. -/
theorem monodromy_projection (i j k : F.Label)
    (f : F.simple i ⊗ F.simple j ⟶ F.simple k) :
    monodromy (F.simple i) (F.simple j) ≫ f =
      (R.twistScalar k / (R.twistScalar i * R.twistScalar j)) • f := by
  classical
  have h := R.naturality f
  rw [R.balance, ← R.twistScalar_smul_id i, ← R.twistScalar_smul_id j,
    ← R.twistScalar_smul_id k] at h
  simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, id_whiskerRight, whiskerLeft_id,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id,
    smul_smul, mul_comm (R.twistScalar j) (R.twistScalar i)] at h
  simp only [Category.assoc] at h
  have hn := mul_ne_zero (R.twistScalar_ne_zero i) (R.twistScalar_ne_zero j)
  calc
    _ = (R.twistScalar i * R.twistScalar j)⁻¹ •
        ((R.twistScalar i * R.twistScalar j) •
          (monodromy (F.simple i) (F.simple j) ≫ f)) := (inv_smul_smul₀ hn _).symm
    _ = _ := by
      simp only [monodromy, Category.assoc]
      rw [← h]
      simp [smul_smul, div_eq_mul_inv, mul_comm]

/-- Determinant of a pair's monodromy inside a triple tensor product. -/
theorem det_monodromy_whiskerRight (i j : F.Label) (Y Z : C) :
    homDet Z (monodromy (F.simple i) (F.simple j) ▷ Y) =
      ∏ p, (R.twistScalar p / (R.twistScalar i * R.twistScalar j)) ^
        (F.fusionMultiplicity i j (F.simple p) *
          Module.finrank ℂ (Z ⟶ F.simple p ⊗ Y)) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition (F.simple i ⊗ F.simple j)
  letI := fun k => F.homFinite Z (F.simple (a k) ⊗ Y)
  rw [homDet, det_of_scalar_coordinates (F.homTensorDecomposition e Y Z)
    _ (fun k => R.twistScalar (a k) / (R.twistScalar i * R.twistScalar j))]
  · rw [F.prod_decomposition e
      (fun p => (R.twistScalar p / (R.twistScalar i * R.twistScalar j)) ^
        Module.finrank ℂ (Z ⟶ F.simple p ⊗ Y))]
    simp [SphericalFusion.fusionMultiplicity, ← pow_mul, Nat.mul_comm]
  · intro f k
    change (f ≫ monodromy (F.simple i) (F.simple j) ▷ Y) ≫
      (e.hom ≫ biproduct.π _ k) ▷ Y = _
    rw [Category.assoc, ← comp_whiskerRight, R.monodromy_projection]
    simp [SphericalFusion.homTensorDecomposition]

/-- Left-tensored pair determinant, by transport across the braiding. -/
theorem det_whiskerLeft_monodromy (i j : F.Label) (Y Z : C) :
    homDet Z (Y ◁ monodromy (F.simple i) (F.simple j)) =
      ∏ p, (R.twistScalar p / (R.twistScalar i * R.twistScalar j)) ^
        (F.fusionMultiplicity i j (F.simple p) *
          Module.finrank ℂ (Z ⟶ Y ⊗ F.simple p)) := by
  classical
  have h : Y ◁ monodromy (F.simple i) (F.simple j) =
      (β_ Y (F.simple i ⊗ F.simple j)).hom ≫
        monodromy (F.simple i) (F.simple j) ▷ Y ≫
          (β_ Y (F.simple i ⊗ F.simple j)).inv := by
    rw [← BraidedCategory.braiding_naturality_right_assoc]
    simp only [Iso.hom_inv_id, Category.comp_id]
  rw [h, homDet_conj, R.det_monodromy_whiskerRight]
  congr 1
  funext p
  rw [(homCongr (Iso.refl Z) (β_ (F.simple p) Y)).finrank_eq]

/-- Block monodromy determinant, decomposing the first two tensor factors. -/
theorem det_monodromy_block (i j k r : F.Label) :
    homDet (F.simple r) (monodromy (F.simple i ⊗ F.simple j) (F.simple k)) =
      ∏ p, (R.twistScalar r / (R.twistScalar p * R.twistScalar k)) ^
        (F.fusionMultiplicity i j (F.simple p) * F.fusionMultiplicity p k (F.simple r)) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition (F.simple i ⊗ F.simple j)
  letI := fun l => F.homFinite (F.simple r) (F.simple (a l) ⊗ F.simple k)
  rw [homDet, det_of_scalar_coordinates (F.homTensorDecomposition e (F.simple k) (F.simple r))
    _ (fun l => R.twistScalar r / (R.twistScalar (a l) * R.twistScalar k))]
  · rw [F.prod_decomposition e
      (fun p => (R.twistScalar r / (R.twistScalar p * R.twistScalar k)) ^
        Module.finrank ℂ (F.simple r ⟶ F.simple p ⊗ F.simple k))]
    simp [SphericalFusion.fusionMultiplicity, ← pow_mul, Nat.mul_comm]
  · intro f l
    change (f ≫ monodromy (F.simple i ⊗ F.simple j) (F.simple k)) ≫
      (e.hom ≫ biproduct.π _ l) ▷ F.simple k = _
    simp only [monodromy, Category.assoc,
      ← BraidedCategory.braiding_naturality_right,
      ← BraidedCategory.braiding_naturality_left_assoc]
    rw [← Category.assoc, R.monodromy_channel]
    rfl

/-- The categorical three-channel determinant relation, with actual fusion dimensions. -/
theorem three_channel_determinant (i j k r : F.Label) :
    (∏ p, (R.twistScalar r / (R.twistScalar p * R.twistScalar k)) ^
      (F.fusionMultiplicity i j (F.simple p) * F.fusionMultiplicity p k (F.simple r))) =
    (∏ p, (R.twistScalar p / (R.twistScalar i * R.twistScalar k)) ^
      (F.fusionMultiplicity i k (F.simple p) * F.fusionMultiplicity p j (F.simple r))) *
    (∏ p, (R.twistScalar p / (R.twistScalar j * R.twistScalar k)) ^
      (F.fusionMultiplicity j k (F.simple p) * F.fusionMultiplicity i p (F.simple r))) := by
  classical
  rw [← R.det_monodromy_block, homDet_monodromy_tensor,
    R.det_monodromy_whiskerRight, R.det_whiskerLeft_monodromy]
  rfl

end Ribbon

end VOA.Huang.NgSchauenburg
