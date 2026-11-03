import VOA.Classification.COne.McRaeM2LogPentagon
import VOA.Classification.COne.McRaeM2LogTriangle
import VOA.Classification.COne.McRaeM2TensorEvaluationNatural

/-! # The logarithmic monoidal category of a C₂-cofinite VOA

The genuine logarithmic tensor product of finite logarithmic modules, its
canonical associator, and the vacuum unitors form a Mathlib `MonoidalCategory`
on `LogModuleCat W`, for every C₂-cofinite VOA `W`. The unitors are natural by
the universal property and naturality of the actual module vertex operator; the
pentagon is `tensorPentagon`, the triangle `associatorIso_triangle`. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.SelfDual
universe u
variable {V R X : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup R] [Module ℂ R] [AddCommGroup X] [Module ℂ X]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

section Compose
variable {M₁ M₂ M₃ M₄ M₅ X₁ X₂ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅] [AddCommGroup X₁] [Module ℂ X₁]
  [AddCommGroup X₂] [Module ℂ X₂]
  {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {A₄ : WeakModule W M₄} {A₅ : WeakModule W M₅}
  {B₁ : WeakModule W X₁} {B₂ : WeakModule W X₂}

/-- Postcomposition with a composite is iterated postcomposition. -/
theorem postcompose_homComp' (f : A₃.Hom A₄) (g : A₄.Hom A₅)
    (Y : LogIntertwiningOperator A₁ A₂ A₃) :
    postcompose (homComp g f) Y=postcompose g (postcompose f Y) := by
  apply Subtype.ext
  funext n k
  ext x y
  rfl

/-- Postcomposition and precomposition commute. -/
theorem postcompose_precompose' (f : B₁.Hom A₁) (g : B₂.Hom A₂)
    (h : A₃.Hom A₄) (Y : LogIntertwiningOperator A₁ A₂ A₃) :
    postcompose h (precompose f g Y)=precompose f g (postcompose h Y) := by
  apply Subtype.ext
  funext n k
  ext x y
  rfl

end Compose

/-- The actual left vacuum unit is natural. -/
theorem tensorLeftUnit_natural (N : LogVModule W R) (P : LogVModule W X)
    (hN : FinGen N.toWeakModule) (hP : FinGen P.toWeakModule)
    (f : N.toWeakModule.Hom P.toWeakModule) :
    (homComp (tensorLeftUnitHom hC2 P hP)
      (tensorMap hC2 (adjointModule W).toLog N finGen_adjoint hN (adjointModule W).toLog P
        finGen_adjoint hP (weakIdentity (adjointModule W).toWeakModule) f)).toLinearMap=
    (homComp f (tensorLeftUnitHom hC2 N hN)).toLinearMap := by
  apply tensor_morphism_ext hC2 (adjointModule W).toLog N finGen_adjoint hN P
  rw [postcompose_homComp', postcompose_homComp', tensorMap_intertwiner,
    postcompose_precompose', tensorLeftUnit_intertwiner, tensorLeftUnit_intertwiner]
  exact (logModuleIntertwiner_natural N P f).symm

/-- The actual right vacuum unit is natural. -/
theorem tensorRightUnit_natural (N : LogVModule W R) (P : LogVModule W X)
    (hN : FinGen N.toWeakModule) (hP : FinGen P.toWeakModule)
    (f : N.toWeakModule.Hom P.toWeakModule) :
    (homComp (tensorRightUnitHom hC2 P hP)
      (tensorMap hC2 N (adjointModule W).toLog hN finGen_adjoint P (adjointModule W).toLog
        hP finGen_adjoint f (weakIdentity (adjointModule W).toWeakModule))).toLinearMap=
    (homComp f (tensorRightUnitHom hC2 N hN)).toLinearMap := by
  apply tensor_morphism_ext hC2 N (adjointModule W).toLog hN finGen_adjoint P
  rw [postcompose_homComp', postcompose_homComp', tensorMap_intertwiner,
    postcompose_precompose', tensorRightUnit_intertwiner, tensorRightUnit_intertwiner]
  exact (rightUnitIntertwiner_natural N P f).symm

end VOA.C2Rigid.LocalInjective

namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.C2Rigid.LocalInjective
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The categorical left unitor is natural. -/
theorem leftUnitIso_naturality {X Y : LogModuleCat W} (f : X ⟶ Y) :
    tensorMorphism hC2 (𝟙 unitObject) f ≫ (leftUnitIso hC2 Y).hom=
      (leftUnitIso hC2 X).hom ≫ f := by
  apply hom_ext
  intro q
  exact congrArg (fun F => F q) (tensorLeftUnit_natural hC2 X.act Y.act
    X.finiteGeneration Y.finiteGeneration (toWeakHom f))

/-- The categorical right unitor is natural. -/
theorem rightUnitIso_naturality {X Y : LogModuleCat W} (f : X ⟶ Y) :
    tensorMorphism hC2 f (𝟙 unitObject) ≫ (rightUnitIso hC2 Y).hom=
      (rightUnitIso hC2 X).hom ≫ f := by
  apply hom_ext
  intro q
  exact congrArg (fun F => F q) (tensorRightUnit_natural hC2 X.act Y.act
    X.finiteGeneration Y.finiteGeneration (toWeakHom f))

-- Nested actual categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- **The logarithmic monoidal category** of finite logarithmic modules of
a C₂-cofinite VOA (Huang–Lepowsky–Zhang): the genuine logarithmic tensor product,
the canonical associator, and the vacuum unitors, with all coherence laws proved. -/
abbrev logarithmicMonoidalCategory : MonoidalCategory (LogModuleCat W) :=
  letI := logarithmicTensorStruct hC2
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X Y => (tensorBifunctor hC2).map_id (X,Y))
    (id_tensorHom := fun _ _ _ _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ =>
      ((tensorBifunctor hC2).map_comp (X := (_,_)) (Y := (_,_)) (Z := (_,_))
        (f₁,f₂) (g₁,g₂)).symm)
    (associator_naturality := fun f₁ f₂ f₃ => associatorIso_naturality hC2 f₁ f₂ f₃)
    (leftUnitor_naturality := fun f => leftUnitIso_naturality hC2 f)
    (rightUnitor_naturality := fun f => rightUnitIso_naturality hC2 f)
    (pentagon := fun N P Q R => tensorPentagon hC2 N P Q R)
    (triangle := fun N P => associatorIso_triangle hC2 N P)

/-- The monoidal structure uses the genuine logarithmic tensor objects. -/
theorem logarithmicMonoidalCategory_tensorObj (N P : LogModuleCat W) :
    (logarithmicMonoidalCategory hC2).tensorObj N P=tensorObject hC2 N P := rfl

/-- The monoidal structure uses the proved logarithmic associator. -/
theorem logarithmicMonoidalCategory_associator (N P Q : LogModuleCat W) :
    @MonoidalCategoryStruct.associator _ _
      (logarithmicMonoidalCategory hC2).toMonoidalCategoryStruct N P Q=
      associatorIso hC2 N P Q := rfl

/-- The monoidal unit is the adjoint module. -/
theorem logarithmicMonoidalCategory_tensorUnit :
    (logarithmicMonoidalCategory hC2).tensorUnit=unitObject := rfl

/-- Existence of the logarithmic monoidal structure for every C₂-cofinite VOA. -/
theorem nonempty_logarithmicMonoidalCategory (hC2 : C2Cofinite W) :
    Nonempty (MonoidalCategory (LogModuleCat W)) :=
  ⟨logarithmicMonoidalCategory hC2⟩

end VOA.LogTensor.LogModuleCat
