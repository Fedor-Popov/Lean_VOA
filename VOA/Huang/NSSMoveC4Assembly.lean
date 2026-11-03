import VOA.Huang.NSSMoveC3Forward
import VOA.Huang.NSGaloisCore
import VOA.Huang.DLNSchurTwo

/-! # The mixed S move: closing the Ng–Schauenburg channel cancellation

The two complete sewn diagrams agree for every central interaction
(`interactionTransposeDefect_eq_zero_of_central`): the forward diagram is a
right partial trace over `X` (`forwardSewing_leftInteractionLoop`), the inverse
diagram is a left partial trace over `X` (`inverseSewing_rightInteractionLoop`),
and sphericality (`partialTraceRight_eq_left_braiding`) identifies them after
conjugation by the braiding (`braiding_conj_forwardIntegrand`).

The isotypic projectors are central, so every channel defect vanishes and the
weighted cancellation `MixedTwistChannelCancellation` holds for every spherical
fusion category with a ribbon structure. Consequently the mixed S move and the
kernel half of Ng–Schauenburg 6.8 hold with no residual hypothesis.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- Every central interaction transposes through the two sewn diagrams. -/
theorem interactionTransposeDefect_eq_zero_of_central (F : SphericalFusion C) (X Y : C)
    (i j : F.Label) (c : Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ) (hc : ∀ e : Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ, e ≫ c = c ≫ e) :
    interactionTransposeDefect F X Y i j c = 0 := by
  simp only [interactionTransposeDefect, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [forwardSewing_leftInteractionLoop F X Y i j c hc, inverseSewing_rightInteractionLoop,
    partialTraceRight_eq_left_braiding, braiding_conj_forwardIntegrand, sub_self]

/-- Each intrinsic isotypic channel transposes separately. -/
theorem interactionTransposeDefect_simpleProjector (F : SphericalFusion C) (X Y : C)
    (i j k : F.Label) :
    interactionTransposeDefect F X Y i j (F.simpleProjector k (Y ⊗ Xᘁ)) = 0 :=
  interactionTransposeDefect_eq_zero_of_central F X Y i j _
    (fun e => (F.simpleProjector_naturality k e).symm)

/-- The weighted channel cancellation holds for every ribbon structure. -/
theorem mixedTwistChannelCancellation_holds (F : SphericalFusion C)
    (R : Ribbon F.toPivotal) : MixedTwistChannelCancellation F R := by
  intro r b i j
  apply Finset.sum_eq_zero
  intro k _
  rw [interactionTransposeDefect_simpleProjector, smul_zero]

/-- The local two-loop transposition holds whenever a ribbon structure exists. -/
theorem mixedLoopTranspose_of_ribbon (F : SphericalFusion C) (R : Ribbon F.toPivotal) :
    MixedLoopTranspose F :=
  (mixedLoopTranspose_iff_twistChannelCancellation F R).mpr
    (mixedTwistChannelCancellation_holds F R)

/-- The mixed nonzero-row S move holds in every modular category. -/
theorem mixedNonzeroSMove_holds (F : SphericalFusion C) (M : Modular F) :
    MixedNonzeroSMove F M :=
  mixedNonzeroSMove_of_twistChannelCancellation F M
    (mixedTwistChannelCancellation_holds F M.toRibbon)

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge
open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence
universe v w

theorem nsMixedTwistChannelCancellationAll_holds :
    NSMixedTwistChannelCancellationAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact mixedTwistChannelCancellation_holds F M.toRibbon

theorem nsMixedNonzeroSMoveAll_holds : NSMixedNonzeroSMoveAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M
  exact mixedNonzeroSMove_holds F M

/-- The kernel half of Ng–Schauenburg Theorem 6.8, with no residual premise. -/
theorem nsProjectiveKernelAll_holds : NSProjectiveKernelAll.{v, w} :=
  nsProjectiveKernelAll_of_twistChannelCancellation nsMixedTwistChannelCancellationAll_holds

end VOA.Huang.DLNBridge

namespace VOA.Huang.NSGaloisCore
open VOA.Huang.DLNBridge
universe u

/-- Both DLN classification inputs from DLN 2.3 (`MatrixDLNLifting`) alone. -/
theorem dln_inputs_of_lifting (hlift : MatrixDLNLifting) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_nonzeroSMove_lifting nsMixedNonzeroSMoveAll_holds hlift

/-- Both DLN classification inputs from the two remaining prime-power Schur facts. -/
theorem dln_inputs_of_beyl (hodd : VOA.Huang.DLNBeyl.OddPrimePowerSchur)
    (htwo : VOA.Huang.DLNSchur.TwoPowerInflationFromTwo) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_lifting (VOA.Huang.DLNSchur.matrixDLNLifting_of_remaining hodd htwo)

end VOA.Huang.NSGaloisCore
