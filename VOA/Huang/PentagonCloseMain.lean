import VOA.Huang.PentagonCloseFaithful

/-! # The monoidal category of ordinary modules of a strongly rational VOA

All three pentagon/triangle inputs are proved for the associator produced by
the library's evaluation construction (`naturalReassociationOfEvaluation` applied to
`ordinaryFourPointInput_pbw`):

* `fivePointLeftFaithfulness_pbw` (`PentagonCloseFaithful`);
* `fivePointFiberEdges_pbw` (`PentagonCloseEdges`);
* `vacuumCreationCompatibility_pbw` (`PentagonCloseVacuum`).

Together with the proved joint five-point summability
(`FivePointSep.fivePointSummability_pbw`) this discharges `FivePointSewingInput`,
hence the pentagon, and the triangle. The only hypothesis left is
`StronglyRational W`; the PBW input is the theorem `VOA.pbw`, so
no non-core axiom is used.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- The five-point sewing input for the actual associator (strongly rational `W`). -/
theorem fivePointSewingInput_stronglyRational_pbw (hV : StronglyRational W) :
    FivePointSewingInput F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators :=
  FivePointSep.fivePointSewingInput_pbw F hV _ (fivePointLeftFaithfulness_pbw F hV)
    (fivePointFiberEdges_pbw F hV)

/-- **The pentagon** for the actual associator of a strongly rational VOA. -/
theorem pentagon_stronglyRational_pbw (hV : StronglyRational W) (X Y Z T : Ordinary W) :
    pentagonLong F
        (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators
        X Y Z T =
      pentagonShort F
        (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators
        X Y Z T :=
  pentagon_of_modes F _
    (pentagonOnModes_of_fivePointSewing F _ (fivePointSewingInput_stronglyRational_pbw F hV))
    X Y Z T

/-- **The triangle** for the actual associator of a strongly rational VOA. -/
theorem triangle_stronglyRational_pbw (hV : StronglyRational W) (X Y : Ordinary W) :
    ((naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators
        X vacuumObject Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom =
      tensorHom F (rightUnitor F X).hom (𝟙 Y) :=
  triangle_of_modes F _ (triangleOnModes_pbw F hV) X Y

/-- **The monoidal category of ordinary modules** of a strongly rational VOA, for any
choice of fusion products: tensor product `tensorObj F`, unit the adjoint module, the
analytically normalized associator, and the proved unitors. -/
abbrev monoidalCategoryOfStronglyRational_pbw (hV : StronglyRational W) :
    MonoidalCategory (Ordinary W) :=
  monoidalCategoryOfStronglyRationalSewing F hV (fivePointSewingInput_stronglyRational_pbw F hV)
    (vacuumCreationCompatibility_pbw F hV)

/-- The construction really uses the chosen fusion products and the evaluation associator. -/
theorem monoidalCategoryOfStronglyRational_pbw_tensorObj (hV : StronglyRational W)
    (X Y : Ordinary W) :
    (monoidalCategoryOfStronglyRational_pbw F hV).tensorObj X Y = tensorObj F X Y := rfl

theorem monoidalCategoryOfStronglyRational_pbw_associator (hV : StronglyRational W)
    (X Y Z : Ordinary W) :
    @MonoidalCategoryStruct.associator _ _
        (monoidalCategoryOfStronglyRational_pbw F hV).toMonoidalCategoryStruct X Y Z =
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators
        X Y Z := rfl

theorem monoidalCategoryOfStronglyRational_pbw_tensorUnit (hV : StronglyRational W) :
    (monoidalCategoryOfStronglyRational_pbw F hV).tensorUnit = vacuumObject := rfl

/-- Existence, with the library's own fusion products (strong rationality only). -/
theorem nonempty_monoidalCategory_stronglyRational_pbw (hV : StronglyRational W) :
    Nonempty (MonoidalCategory (Ordinary W)) :=
  ⟨monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hV) hV⟩

end VOA.Huang.TensorCat
