import VOA.Classification.COne.OrbPos8Exceptional
import VOA.Huang.TensorCatUnit
import VOA.Huang.RepPackagingSemisimple

/-!
# The split unit in orbifold induction

For a finite group, the inclusion of the fixed-point VOA into the ambient
adjoint module has an explicit module-linear Reynolds retraction. Tensoring
this split inclusion gives an injective map into the actual fusion product.
Neither positivity nor rigidity is used.
-/

noncomputable section
namespace VOA.Classification.COne.OrbPos9
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat CategoryTheory
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V}

/-- The ambient VOA, regarded as an ordinary module for its fixed algebra. -/
def ambient (G : Subgroup (Aut W)) : Ordinary (orbifoldVOA G) :=
  Ordinary.of (orbifold G).adjointRestrictOrd

/-- The actual inclusion of the tensor unit. -/
def unitInclusion (G : Subgroup (Aut W)) : vacuumObject ⟶ ambient G :=
  ⟨(orbifold G).carrier.subtype, fun _ _ _ => rfl⟩

/-- Normalized finite-group averaging, with codomain the fixed-point space. -/
def reynolds (G : Subgroup (Aut W)) [Fintype G] : V →ₗ[ℂ] (orbifold G).carrier :=
  (((Fintype.card G : ℂ)⁻¹) •
    ∑ g : G, g.1.toLinearEquiv.toLinearMap).codRestrict _ (by
      intro x g hg
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearEquiv.coe_coe]
      rw [map_smul, map_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : G)) _ _ (fun h => rfl))

@[simp] theorem reynolds_apply (G : Subgroup (Aut W)) [Fintype G] (x : V) :
    (reynolds G x : V) = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, g.1 x := by
  classical
  simp [reynolds]

/-- Reynolds averaging intertwines every mode of the fixed-point VOA. -/
def unitRetraction (G : Subgroup (Aut W)) [Fintype G] : ambient G ⟶ vacuumObject :=
  ⟨reynolds G, by
    intro v k x
    apply Subtype.ext
    change (reynolds G (W.smul v.1 k x) : V) = W.smul v.1 k (reynolds G x : V)
    rw [reynolds_apply, reynolds_apply]
    simp only [PreVertexAlgebra.smul, map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    exact (g.1.map_smul' v.1 k x).trans (by rw [v.2 g.1 g.2]; rfl)⟩

@[simp] theorem unitInclusion_retraction (G : Subgroup (Aut W)) [Fintype G] :
    unitInclusion G ≫ unitRetraction G = 𝟙 vacuumObject := by
  apply Ordinary.hom_ext
  intro x
  apply Subtype.ext
  change (reynolds G x.1 : V) = x.1
  rw [reynolds_apply]
  have hfix : ∀ g : G, g.1 x.1 = x.1 := fun g => x.2 g.1 g.2
  simp only [hfix, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

/-- The canonical unit map into induction on the underlying ordinary modules. -/
def inductionUnit (G : Subgroup (Aut W)) (F : FusionChoice (orbifoldVOA G))
    (X : Ordinary (orbifoldVOA G)) : X ⟶ tensorObj F (ambient G) X :=
  (leftUnitor F X).inv ≫ tensorHom F (unitInclusion G) (𝟙 X)

/-- The ordinary-module retraction of the induction unit. -/
def inductionRetraction (G : Subgroup (Aut W)) [Fintype G]
    (F : FusionChoice (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G)) :
    tensorObj F (ambient G) X ⟶ X :=
  tensorHom F (unitRetraction G) (𝟙 X) ≫ (leftUnitor F X).hom

@[simp] theorem inductionUnit_retraction (G : Subgroup (Aut W)) [Fintype G]
    (F : FusionChoice (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G)) :
    inductionUnit G F X ≫ inductionRetraction G F X = 𝟙 X := by
  unfold inductionUnit inductionRetraction
  rw [Category.assoc, ← Category.assoc (tensorHom F _ _), ← tensorHom_comp]
  simp

/-- In particular, the actual linear map into the actual fusion product is injective. -/
theorem inductionUnit_injective (G : Subgroup (Aut W)) [Finite G]
    (F : FusionChoice (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G)) :
    Function.Injective (inductionUnit G F X).val := by
  letI := Fintype.ofFinite G
  have h := inductionUnit_retraction G F X
  have hr : Function.LeftInverse (inductionRetraction G F X).val
      (inductionUnit G F X).val :=
    fun x => congrArg (fun f : X ⟶ X => f.val x) h
  exact hr.injective

/-- Strong rationality supplies the fusion products needed for induction;
`VOA.pbw` is inherited through `fusionChoice_pbw`. -/
theorem exceptional_induction_embedding
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : IsExceptionalV2Group G)
    (hSR : StronglyRational (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G)) :
    ∃ f : X ⟶ tensorObj (fusionChoice_pbw hSR) (ambient G) X,
      Function.Injective f.val := by
  letI := exceptionalV2Group_finite hG
  exact ⟨inductionUnit G (fusionChoice_pbw hSR) X,
    inductionUnit_injective G (fusionChoice_pbw hSR) X⟩

end VOA.Classification.COne.OrbPos9
