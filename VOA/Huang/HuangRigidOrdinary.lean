import VOA.Huang.HuangRigidG1
import VOA.Huang.HuangRigidAbstract
import VOA.Huang.RepPackagingAssembly
import VOA.Huang.ZhuModData

/-!
# Huang's rigidity theorem for the category of ordinary modules

For a nice VOA `W` and any fusion choice `F`, the proved monoidal category
`monoidalCategoryOfStronglyRational_pbw F hW.1` on `Ordinary W` is right rigid.

* `hasRightDual_famObj` — every member `M_b` of a complete irredundant Zhu family has a right dual
  `M_{σ b}` (the contragredient label): the nonzero vacuum pairings `ε : M_{σb} ⊠ M_b → V`,
  `η : V → M_b ⊠ M_{σb}` have nonzero zig-zag (`zigzagNonzeroInput_holds`, Huang's Prop. 5.1,
  proved via (G1)); rescaling `η` makes the `M_b`-zig-zag the identity, the `M_{σb}`-zig-zag is a
  scalar by Schur, and the snake identity (`snake_eval`) with `ε ≠ 0` forces that scalar to be `1`.
* `rightRigid_ordinary` — right rigidity of `Ordinary W` (semisimplicity
  `semisimple_lw_pbw` + duals of biproducts `exactPairingBiprod`).
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HuangRigid

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeFusion
  VOA.Huang.VerlindeEigen VOA.Huang.VerlindeTransport VOA.Huang.VerlindeVacuum
  VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.RepPackaging
  CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

universe u w

section Simple

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **Every member of a complete irredundant Zhu family has a right dual, which is the
family member isomorphic to its contragredient.** -/
theorem exactPairing_famObj (F : FusionChoice W) (hNice : Nice W) (D : VOA.ModularData W ι)
    (hZ : ZhuModularityAnalytic D) (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam)
    (v0 : ι) (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (b : ι) :
    letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
    ∃ a : ι, Nonempty (ModuleEquiv W (contragredientModule (D.Mfam b).isMod) (D.Mfam a).isMod) ∧
      Nonempty (ExactPairing (famObj D b) (famObj D a)) := by
  letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
  letI := monoidalPreadditive_pbw F hNice.1
  letI := monoidalLinear_pbw F hNice.1
  let H := ordinaryFourPointInput_pbw F hNice.1
  obtain ⟨a, ha⟩ := hcomp (contraIrr D b)
  have h1 : famFusion D b a v0 ≠ 0 := famFusion_vacuum_ne_zero D hNice v0 hv0 b a ha
  have h2 : famFusion D a b v0 ≠ 0 := by
    rw [famFusion, BraidingSkew.fusionRule_swap (D.Mfam b).isMod (D.Mfam a).isMod
      (D.Mfam v0).isMod]
    exact h1
  obtain ⟨ε, hε⟩ := exists_ne_zero_to_vacuum hNice F D v0 hv0 a b h2
  obtain ⟨η, hη⟩ := exists_ne_zero_from_vacuum hNice F D hcomp v0 hv0 b a h1
  choose r lab inc proj htot using fun x =>
    exists_split hNice.1 D hcomp (tensorObj F (famObj D b) (famObj D x))
  let c : TransferChoice F D a b := ⟨ε, hε, η, hη, r, lab, inc, proj, htot⟩
  have hz : zigzag F H c ≠ 0 :=
    zigzagNonzeroInput_holds 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 F H a b c
  obtain ⟨s, hs⟩ := endo_scalar D b (zigzag F H c)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hz (by rw [hs, zero_smul])
  -- the zig-zag of the library is the Mathlib zig-zag
  have hzig : zigX (C := Ordinary W) η ε = s • 𝟙 (famObj D b) := hs
  let η' : 𝟙_ (Ordinary W) ⟶ famObj D b ⊗ famObj D a := s⁻¹ • η
  have hzig' : zigX η' ε = 𝟙 (famObj D b) := by
    have : zigX η' ε = s⁻¹ • zigX η ε := by
      simp only [zigX, η', MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]
    rw [this, hzig, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  obtain ⟨t, ht⟩ := endo_scalar D a (zigY η' ε)
  exact ⟨a, ha, ⟨exactPairingOfZigzag η' ε hzig' t ht hε⟩⟩

/-- Every member of a complete irredundant Zhu family has a right dual. -/
theorem hasRightDual_famObj (F : FusionChoice W) (hNice : Nice W) (D : VOA.ModularData W ι)
    (hZ : ZhuModularityAnalytic D) (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam)
    (v0 : ι) (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (b : ι) :
    letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
    Nonempty (HasRightDual (famObj D b)) := by
  letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
  obtain ⟨a, -, ⟨p⟩⟩ := exactPairing_famObj F hNice D hZ hirr hcomp v0 hv0 b
  exact ⟨{ rightDual := famObj D a, exact := p }⟩

end Simple

section Rigid

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

open VOA.VHat VOA.VHat.DLM3 VOA.Huang.ZhuFiniteIrr VOA.Huang.ZhuSemisimple in
/-- **Huang's rigidity theorem**: for a nice VOA and any fusion choice, the proved
monoidal category of ordinary modules is right rigid. -/
theorem rightRigid_ordinary (F : FusionChoice W) (hNice : Nice W) :
    letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
    Nonempty (RightRigidCategory (Ordinary W)) := by
  classical
  letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
  letI := monoidalPreadditive_pbw F hNice.1
  have hSR : StronglyRational W := hNice.1
  let Pr := voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))
  have hss := isSemisimpleRing_A_of_admissiblyRational Pr hSR.rational
  haveI : Finite (Φ W) := finite_Φ_of_C2Cofinite Pr hSR.c2Cofinite hss
  letI : Fintype (Φ W) := Fintype.ofFinite (Φ W)
  obtain ⟨D, hM, -, hZ⟩ := zhuModularity_canonical_of_Pr (W := W) Pr hSR.c2Cofinite hss
  have hic := canonicalIrrFamily_irredundant_complete (W := W)
  have hirr : Irredundant D.Mfam := by rw [hM]; exact hic.1
  have hcomp : Complete D.Mfam := by rw [hM]; exact hic.2
  let c0 : Φ W := (adjointIrr W hSR.simple).toΦ
  have hvac : Nonempty (ModuleEquiv W (D.Mfam c0).isMod (adjointModule W)) := by
    rw [hM]; exact Quotient.exact (canonicalIrrModule_toΦ c0)
  have hdual : ∀ c, Nonempty (HasRightDual (famObj D c)) :=
    hasRightDual_famObj F hNice D hZ hirr hcomp c0 hvac
  refine ⟨rightRigidOfDecomposition (fun X => ?_)⟩
  obtain ⟨n, R, hR, ⟨e⟩⟩ := semisimple_lw_pbw hSR X
  refine ⟨n, fun j => Ordinary.of (R j).isMod, fun j => ?_, ⟨e⟩⟩
  obtain ⟨c, ⟨g⟩⟩ := hcomp ⟨(R j).carrier, (R j).isMod, hR j⟩
  obtain ⟨d⟩ := hdual c
  let i : Ordinary.of (R j).isMod ≅ famObj D c := Ordinary.isoOfModuleEquiv g
  exact ⟨{ rightDual := (famObj D c)ᘁ, exact := exactPairingCongrLeft i }⟩

end Rigid

section Model

/-- Right rigidity transported to any structural small model. -/
theorem rigidityInput_of_nice {V : Type u} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} (hW : Nice W) (M : StructuralModel W) : RigidityInput M := by
  letI := monoidalCategoryOfStronglyRational_pbw M.F M.stronglyRational
  letI := M.monoidalFunctor
  obtain ⟨r⟩ := rightRigid_ordinary M.F hW
  letI : RightRigidCategory (Ordinary W) := r
  exact ⟨rightRigidCategoryOfEquivalence M.E.toAdjunction⟩

/-- **`HuangRigidityInput`** (Huang 2008, rigidity of the module category of a nice
VOA), on the fixed small model `canonicalModel`. -/
theorem huangRigidityInput_holds : HuangRigidityInput.{u} := by
  intro V _ _ W hW D hD
  exact rigidityInput_of_nice hW (canonicalModel hW D hD)

end Model

end VOA.Huang.HuangRigid
