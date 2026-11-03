import VOA.Classification.COne.OrbPos11Dictionary
import VOA.Classification.COne.OrbPos10Regular

/-! # Concrete checks of the reconstruction and the lowest-weight shortcut -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat VOA.Huang.HKLRational
open CategoryTheory MonoidalCategory OrbPos9 OrbPos10 OrbPos2

/-- On the actual regular action, the reconstructed period-one fields are
exactly the adjoint fields. -/
theorem regularAction_modes
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (E : CanonicalExtensionAlgebra G hSR) :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    actionModes G hSR (regularSimpleAction G hSR E).obj
      (regularSimpleAction G hSR E).act 1 = (adjointModule (V2m 1 le_rfl)).toTwisted.YM := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  ext v k x
  simp only [actionModes, actionIntertwiner, LinearMap.coe_mk, AddHom.coe_mk,
    Nat.cast_one, div_one, VOA.Huang.FusionProduct.postcompose_apply]
  change (MonObj.mul : tensorObj (fusionChoice_pbw hSR) (ambient G) (ambient G) ⟶
    ambient G).val (((fusionChoice_pbw hSR) (ambient G) (ambient G)).intertwiner.val
      (k : ℂ) v x) = _
  rw [E.mul_eq, ambientMultiplication_intertwiner, moduleModes_apply_intCast]
  rfl

/-- The remaining Jacobi identity is proved for the nonzero regular simple
action. This is a test case, not the universally quantified residual. -/
theorem regularAction_twistedJacobi
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (E : CanonicalExtensionAlgebra G hSR) :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    TwistedJacobi (1 : Aut (V2m 1 le_rfl)) 1
      (actionModes G hSR (regularSimpleAction G hSR E).obj
        (regularSimpleAction G hSR E).act 1) := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  rw [regularAction_modes G hSR E]
  exact twistedJacobi_of_twistedModule (adjointModule (V2m 1 le_rfl)).toTwisted

/-- Both constructed charge labels at the half twist have the same attained
lowest energy. This states no equivalence or inequivalence of the two modules;
it records why the numerical lowest weight does not select a unique label. -/
theorem halfTwist_lowest_labels_coincide :
    OrbPos8.HasLowestEnergy (OrbPos7.latticeShiftedTwistedModule (n := 2) (by decide) 1 0)
      (1 / 16 : ℂ) ∧
    OrbPos8.HasLowestEnergy (OrbPos7.latticeShiftedTwistedModule (n := 2) (by decide) 1 1)
      (1 / 16 : ℂ) := by
  constructor
  · convert OrbPos8.constructed_lowest_energy (n := 2) (by decide)
      (a := 1) (ε := 0) (by omega) (by omega) (Or.inl rfl) using 1;
      norm_num [innerEnergy]
  · convert OrbPos8.constructed_lowest_energy (n := 2) (by decide)
      (a := 1) (ε := 1) (by omega) (by omega) (Or.inr rfl) using 1;
      norm_num [innerEnergy]

end VOA.Classification.COne.OrbPos11
