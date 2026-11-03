import VOA.Huang.NgSchauenburgVafaRelations
import VOA.Huang.NgSchauenburgRotationOrder

/-! # Balancing on actual fusion channels

The determinant computed below is on `Hom(Xₖ, Xᵢ ⊗ Xⱼ)`. Deriving the
three-channel determinant equation from the hexagon, including the tensor
product decomposition of these Hom spaces, remains separate from this lemma.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

namespace Ribbon
variable {F : SphericalFusion C} (R : Ribbon F.toPivotal)

/-- Balancing determines the monodromy on each actual simple fusion channel. -/
theorem monodromy_channel (i j k : F.Label)
    (f : F.simple k ⟶ F.simple i ⊗ F.simple j) :
    f ≫ (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom =
      (R.twistScalar k / (R.twistScalar i * R.twistScalar j)) • f := by
  have h := R.naturality f
  rw [R.balance, ← R.twistScalar_smul_id i, ← R.twistScalar_smul_id j,
    ← R.twistScalar_smul_id k] at h
  simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight,
    MonoidalLinear.whiskerLeft_smul, id_whiskerRight, whiskerLeft_id,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id,
    smul_smul, mul_comm (R.twistScalar j) (R.twistScalar i)] at h
  have hn := mul_ne_zero (R.twistScalar_ne_zero i) (R.twistScalar_ne_zero j)
  calc
    _ = (R.twistScalar i * R.twistScalar j)⁻¹ •
        ((R.twistScalar i * R.twistScalar j) •
          (f ≫ (β_ (F.simple i) (F.simple j)).hom ≫
            (β_ (F.simple j) (F.simple i)).hom)) := (inv_smul_smul₀ hn _).symm
    _ = _ := by rw [h]; simp [smul_smul, div_eq_mul_inv, mul_comm]

/-- Postcomposition by double braiding on a fusion-channel vector space. -/
def channelMonodromy (i j k : F.Label) :
    Module.End ℂ (F.simple k ⟶ F.simple i ⊗ F.simple j) where
  toFun f := f ≫ (β_ (F.simple i) (F.simple j)).hom ≫
    (β_ (F.simple j) (F.simple i)).hom
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' z f := by simp

/-- The channel endomorphism is scalar, as forced by categorical balancing. -/
theorem channelMonodromy_eq_smul (i j k : F.Label) :
    channelMonodromy (F := F) i j k =
      (R.twistScalar k / (R.twistScalar i * R.twistScalar j)) •
        (1 : Module.End ℂ (F.simple k ⟶ F.simple i ⊗ F.simple j)) := by
  ext f
  exact R.monodromy_channel i j k f

/-- Its determinant has the integral exponent given by the fusion multiplicity. -/
theorem det_channelMonodromy (i j k : F.Label) :
    LinearMap.det (channelMonodromy (F := F) i j k) =
      (R.twistScalar k / (R.twistScalar i * R.twistScalar j)) ^
        F.fusionMultiplicity i j (F.simple k) := by
  letI := F.homFinite (F.simple k) (F.simple i ⊗ F.simple j)
  simp [R.channelMonodromy_eq_smul, LinearMap.det_smul, SphericalFusion.fusionMultiplicity]

end Ribbon
end VOA.Huang.NgSchauenburg
