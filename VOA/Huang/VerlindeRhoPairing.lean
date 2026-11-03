import VOA.Huang.VerlindeRhoInput
import VOA.Huang.VerlindeVacuumFusion

/-!
# Nonvanishing of the contragredient vacuum channel

The FHL map and skew-symmetry take the nonzero module intertwiner to a
nonzero vacuum channel. The finite-dimensional target is supplied by the
vacuum upper bound, so the conclusion concerns an honest positive dimension.
Neither completeness nor irredundancy of the family is needed.
-/

namespace VOA.Huang.VerlindeRho

open VOA VOA.Classification.COne VOA.Huang.VerlindeFusion
  VOA.Huang.VerlindeVacuum VOA.Huang.ATransform VOA.Huang.FusionUnit
  VOA.Huang.BraidingSkew

universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The contragredient-labelled vacuum fusion rule is positive, without a
completeness, irredundancy, or modularity hypothesis. -/
theorem one_le_famFusion_contragredient (hV : Nice W) (D : VOA.ModularData W ι)
    (v0 : ι) (e0 : ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))
    (a b : ι) (g : ModuleEquiv W (contragredientModule (D.Mfam a).isMod)
      (D.Mfam b).isMod) : 1 ≤ famFusion D a b v0 := by
  obtain ⟨e'⟩ := contra_vacuum_equiv hV (D.Mfam v0).isMod (D.Mfam v0).irreducible e0
  let Emid := intertwiningEquivMid (A₁ := (D.Mfam a).isMod)
    (A₃ := (D.Mfam v0).isMod) g
  let Eright := intertwiningEquivRight (A₁ := (D.Mfam a).isMod)
    (A₂ := contragredientModule (D.Mfam a).isMod) (e'.trans e0.symm)
  haveI : FiniteDimensional ℂ
      (intertwiningSpace (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam v0).isMod) :=
    (vacuum_upper D v0 e' b a).1
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam a).isMod
      (contragredientModule (D.Mfam a).isMod)
      (contragredientModule (D.Mfam v0).isMod)) :=
    LinearEquiv.finiteDimensional (Eright.trans Emid).symm
  have hunit : fusionRule (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod = 1 := by
    rw [← fusionRule_swap (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod,
      fusionRule_congr_left e0]
    exact fusionRule_adjoint_self (lwOf D a) (lwOf_irreducible D a)
  calc
    1 = fusionRule (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod := hunit.symm
    _ ≤ fusionRule (D.Mfam a).isMod (contragredientModule (D.Mfam a).isMod)
        (contragredientModule (D.Mfam v0).isMod) := fusionRule_le_atrans _ _ _
    _ = famFusion D a b v0 := (Eright.trans Emid).finrank_eq

/-- The exact nonzero-channel input in the existing rho reduction. -/
theorem contragredientVacuumNonzeroInput : ContragredientVacuumNonzeroInput.{u, w} := by
  intro V _ _ W hV ι _ _ D v0 hv0 a b hab
  obtain ⟨e0⟩ := hv0
  obtain ⟨g⟩ := hab
  exact Nat.ne_of_gt (one_le_famFusion_contragredient hV D v0 e0 a b g)

end VOA.Huang.VerlindeRho
