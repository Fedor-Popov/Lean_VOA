/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCongruenceTwist

/-!
# Assembly: the kernel half of NS 6.8 from two mixed residuals

With `mixedTwistIdentity_holds` the `T` move of the actual mixed indicators holds on every row
(`mixedTMove_holds`), and the Galois rescaling needs only cyclotomic membership.  What remains
open for `DLNBridge.NSProjectiveKernelAll` is exactly:

* `MixedSMoveOrbit F M` — the `S` generator step of the mixed indicators at every primitive row
  (the categorical core of Ng–Schauenburg Theorem 5.4, specialised to `C ⊠ C^rev`);
* `MixedRowCyclotomic F M` — membership of the `(s,-1)` mixed indicator values (`s ≠ 0`) in
  `ℚ(ζ_N)`, `N` the raw twist order (Ng–Schauenburg Prop 5.7 / Lemma 6.4).

Both are true consequences of Ng–Schauenburg; neither is proved here.
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSCongruence

open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- **The `T` move of the actual mixed indicators holds on every integer row.** -/
theorem mixedTMove_holds (F : SphericalFusion C) (M : Modular F) : MixedTMove F M :=
  mixedTMove_of_twistIdentity F M (mixedTwistIdentity_holds F M)

/-- **Galois rescaling from cyclotomic membership alone.** -/
theorem mixedRescaling_of_cyclotomic (F : SphericalFusion C) (M : Modular F)
    (hc : MixedRowCyclotomic F M) : MixedPrimitiveRescaling F M :=
  mixedRescaling_of_twist_cyclotomic F M (mixedTwistIdentity_holds F M) hc

/-- **Orbit equivariance from the `S` move alone.** -/
theorem orbitEquivariance_of_SMove (F : SphericalFusion C) (M : Modular F)
    (hS : MixedSMoveOrbit F M) : MixedOrbitEquivariance F M :=
  orbitEquivariance_of_moves F M (mixedTMove_holds F M) hS

open Classical in
/-- **Projective congruence of every modular lift at the raw twist order, from the `S` move
along the orbit of `(1,0)` and cyclotomic membership.** -/
theorem projectiveKernel_of_SMove_cyclotomic (F : SphericalFusion C) (M : Modular F)
    (hS : MixedSMoveOrbit F M) (hc : MixedRowCyclotomic F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    ProjectiveKernelContainsGamma ρ M.toRibbon.twistOrder :=
  projectiveKernel_of_mixedResiduals F M (mixedTwistIdentity_holds F M) hS hc ρ hr

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence

universe u v w

/-- **The two open mixed residuals, for every modular category.** -/
def NSMixedCoreResidualsAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F),
    MixedSMoveOrbit F M ∧ MixedRowCyclotomic F M

/-- The three-residual contract follows from the two-residual one (the twist identity is
proved). -/
theorem nsMixedResidualsAll_of_core (h : NSMixedCoreResidualsAll.{v, w}) :
    NSMixedResidualsAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M
  obtain ⟨hS, hc⟩ := h C F M
  exact ⟨mixedTwistIdentity_holds F M, hS, hc⟩

/-- **The kernel half of NS 6.8 from the two open mixed residuals.** -/
theorem nsProjectiveKernelAll_of_coreResiduals (h : NSMixedCoreResidualsAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} :=
  nsProjectiveKernelAll_of_mixedResiduals (nsMixedResidualsAll_of_core h)

/-- **Both classification inputs from the two open mixed residuals**, DLN 3.10, DLN 2.3 and
the scaled twist law. -/
theorem dln_inputs_of_coreResiduals (h : NSMixedCoreResidualsAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hT : ZhuGaloisTwistInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_NSKernel_twist (nsProjectiveKernelAll_of_coreResiduals h) hB hlift hT

end VOA.Huang.DLNBridge
