import VOA.Huang.LogAssocCoefficientCoproductCompatAt
import VOA.Classification.COne.McRaeM2TensorObject

/-! The actual compatible coefficient module embeds faithfully in the true
maximal tensor-dual module. For every C₂-cofinite VOA this gives
finite length, finite generation, and its genuine generalized grading. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCoproduct
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.C2Rigid VOA.C2Rigid.LocalInjective VOA.LogTensor.LogFin
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

/-- Inclusion of actual compatible spaces intertwines every genuine mode. -/
noncomputable def compatibleSpaceInclusionHom {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    (S T : CompatibleSpace A₁ A₂) (h : S.carrier≤T.carrier) : S.weakModule.Hom T.weakModule where
  toLinearMap := Submodule.inclusion h
  map_act u p b := by
    apply Subtype.ext
    change (mode (S.field u) p b : BilinearDual (M₁ := M₁) (M₂ := M₂))=
      (mode (T.field u) p (Submodule.inclusion h b) : BilinearDual (M₁ := M₁) (M₂ := M₂))
    have hu : u∈⨆ d,W.grading d := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
    refine Submodule.iSup_induction W.grading (motive := fun u =>
      (mode (S.field u) p b : BilinearDual (M₁ := M₁) (M₂ := M₂))=
      (mode (T.field u) p (Submodule.inclusion h b) : BilinearDual (M₁ := M₁) (M₂ := M₂))) hu ?_ ?_ ?_
    · intro d u hu
      rw [CompatibleSpace.mode_field,CompatibleSpace.mode_field,
        CompatibleSpace.action_homogeneous _ p hu,CompatibleSpace.action_homogeneous _ p hu]
      rfl
    · dsimp only
      have hS : mode (S.field (0 : V)) p=0 := by rw [map_zero]; rfl
      have hT : mode (T.field (0 : V)) p=0 := by rw [map_zero]; rfl
      rw [hS,hT]
      rfl
    · intro u v hu hv
      dsimp only at hu hv ⊢
      rw [map_add,map_add,mode_add,mode_add,LinearMap.add_apply,LinearMap.add_apply,
        Submodule.coe_add,Submodule.coe_add,hu,hv]

variable {M₃ M₄ M₅ : Type u}
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅


/-- The actual coefficient-span inclusion into the maximal compatible
carrier is a genuine injective weak-module morphism. -/
noncomputable def coefficientSpanHom :
    (coefficientWeakModule hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).Hom
      (maximalWeakModule N₁.toWeakModule N₂.toWeakModule) :=
  compatibleSpaceInclusionHom
    (coefficientCompatibleSpace hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule)
    (coefficientSpan_le_maximal hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)

@[simp] theorem coefficientSpanHom_apply
    (b : coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :
    ((coefficientSpanHom hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap b :
      BilinearDual (M₁ := M₁) (M₂ := M₂))=b.1 := rfl

theorem coefficientSpanHom_injective : Function.Injective
    (coefficientSpanHom hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap := by
  intro b c h
  apply Subtype.ext
  exact congrArg (fun b : maximalCarrier N₁.toWeakModule N₂.toWeakModule => b.1) h


/-- The actual coefficient submodule has finite length, by its proved
faithful inclusion in the actual finite-length maximal carrier. -/
theorem coefficientSpan_finiteLength :
    IsFiniteLength (modeAlg (coefficientWeakModule hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂))
      (coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :=
  finiteLength_of_injective_hom
    (coefficientSpanHom hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (coefficientSpanHom_injective hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (finiteLength_maximal_of_c2 hC2 N₁ N₂ hfg₁ hfg₂)

/-- Finite generation is a conclusion on the actual coefficient module. -/
theorem coefficientSpan_finGen :
    FinGen (coefficientWeakModule hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) := by
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp
    (coefficientSpan_finiteLength hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)).1
  exact finGen_of_isNoetherian _

/-- The actual coefficient carrier gets its canonical generalized-module
grading from the proved finite-length theorem, with the original action. -/
noncomputable def coefficientLogModule : LogVModule W
    (coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) :=
  logOfFiniteLength hC2
    (coefficientWeakModule hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (coefficientSpan_finiteLength hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)

end VOA.Huang.LogAssocCoefficientCoproduct
