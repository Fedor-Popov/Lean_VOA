/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangModularityG1
import VOA.Huang.HuangModularityDim

/-!
# Huang's dimension theorem: `dim M_b = d_b` for the twist pivotal structure

For a nice `W`, `D : COne.ModularData W` with `hD : D.IsModularData`, any right duals on the
canonical model, and the twist pivotal structure `modelPivotal`, we prove
`dim M_b = d_b = S_{b,vac} / S_{vac,vac}` (`qdim_eq_d`, hence `huangQDimInput_holds`).

**Genus zero.** Let `a = σ b` (the contragredient label), `ε : M_a ⊠ M_b → V`,
`η : V → M_b ⊠ M_a` nonzero, `s` the zig-zag scalar (`zigzag = s • 𝟙`, `s ≠ 0` by Huang's
Prop. 5.1), `π` a retraction of `η`, and `μ` the skew constant `Y^π = μ Ω₀(Y^ε)`. Since the
library braiding is defined by the same skew map (`postcompose_braidingP_comp`),
`π = μ (β_{b,a} ≫ ε)`, so `η ≫ β_{b,a} ≫ ε = μ⁻¹` (`coev_braid_ev_ord`). The twist-pivotal
dimension computed with the exact pairing `(s⁻¹ η, ε)` (`twistPivotal_trL_id`), transported to the
model (`map_coev_braid_ev`), is `dim M_b = e^{2πi h_b} s⁻¹ μ⁻¹`.

**Genus one.** The vacuum row of (G1) with explicit eigenvalue (`vacuumRow_explicit`), the B-cycle
matrix `s N_{b·}^{·}` (`transferMatrix_eq_zigzag_scalar`), `N_{by}^{vac} = δ_{y,σb}` and
`d_{σb} = d_b` give `μ s d_b = e^{2πi h_b}` (`mu_s_d`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HuangModularity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Module VOA Complex
  VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon
  VOA.Huang.TensorCat.RepPackaging VOA.Huang.Tannakian VOA.Huang.HuangRigid
  VOA.Huang.FusionProduct VOA.Huang.FusionUnit VOA.Huang.SPinning VOA.Huang.VerlindeEigen
  VOA.Huang.VerlindeFusion VOA.Huang.VerlindeTransport VOA.Huang.GenusOneG1c
  VOA.Huang.GenusOneG1d VOA.Huang.GenusOneG1f
open VOA.Huang.GenusTwoPoint (vacuumLW)

universe u

section Ord

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Genus zero: `η ≫ β_{b,a} ≫ ε = μ⁻¹`**, where `Y^π = μ Ω₀(Y^ε)` and `η ≫ π = 𝟙`. -/
theorem coev_braid_ev_ord (F : FusionChoice W) {D : VOA.ModularData W ι} {a b : ι}
    (c : TransferChoice F D a b) (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject)
    (hπ : c.η ≫ π = 𝟙 _) (μ : ℂ) (hμ : μ ≠ 0)
    (hpi : (piInt F π).val = μ • BraidingSkew.skewModes
      (VOA.SkewIntertwiner.Lm1 (adjointModule W).toWeakModule) BraidingSkew.omegaPhase
        (epsInt F c).val) :
    c.η ≫ (braiding F (famObj D b) (famObj D a)).hom ≫ c.ε = μ⁻¹ • 𝟙 _ := by
  have hpost : postcompose (F (famObj D b) (famObj D a)).intertwiner (adjointModule W) π =
      postcompose (F (famObj D b) (famObj D a)).intertwiner (adjointModule W)
        (μ • ((braiding F (famObj D b) (famObj D a)).hom ≫ c.ε)) := by
    erw [LinearMap.map_smul]
    have h := postcompose_braidingP_comp Phase.upper F (X := famObj D b) (Y := famObj D a)
      (T := vacuumObject) c.ε
    apply Subtype.ext
    change (piInt F π).val = _
    rw [hpi]
    erw [h]
    rfl
  have hinj := ((F (famObj D b) (famObj D a)).universal 𝒱 (adjointModule W)).1
  have hπ' : π = μ • ((braiding F (famObj D b) (famObj D a)).hom ≫ c.ε) := hinj hpost
  rw [hπ', Linear.comp_smul] at hπ
  rw [← hπ, smul_smul, inv_mul_cancel₀ hμ, one_smul]

end Ord

section Main

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- `d_{σb} = d_b` from `S² = C` and `σ vac = vac`. -/
theorem S_vac_sigma {ι : Type} [Fintype ι] [DecidableEq ι] (S : ι → ι → ℂ) (σ : ι → ι)
    (hσ : ∀ x, σ (σ x) = x) (v0 : ι) (hσ0 : σ v0 = v0)
    (hSC : Matrix.of S * Matrix.of S = Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0)
    (b : ι) : S v0 (σ b) = S v0 b := by
  have hA : Matrix.of S * (Matrix.of S * Matrix.of S) = (Matrix.of S * Matrix.of S) * Matrix.of S :=
    (Matrix.mul_assoc _ _ _).symm
  rw [hSC] at hA
  have h := congrFun (congrFun hA v0) (σ b)
  simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hσ0] at h
  have hiff : ∀ x, (σ b = σ x) ↔ (x = b) := fun x =>
    ⟨fun h' => by rw [← hσ x, ← h', hσ], fun h' => by rw [h']⟩
  simp_rw [hiff] at h
  simpa using h.symm

/-- **Huang's dimension theorem**: for the canonical model, any right duals, and the twist
pivotal structure, `dim M_b = d_b`. -/
theorem qdim_eq_d (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) [r : RightRigidCategory (canonicalModel hW D hD).C] (b : D.ι) :
    (modelPivotal (canonicalModel hW D hD)).qdim
        (modelSimple (canonicalModel hW D hD).E D b) = (D.d b : ℂ) := by
  classical
  obtain ⟨⟨Mfam, h, hw, rep, repS, hrS, hrT⟩, hM, hh, hZ⟩ := exists_zhuData hW D hD
  simp only at hM hh
  subst hM hh
  set D' : VOA.ModularData W D.ι := ⟨famOf D hD, hOf D, hw, rep, repS, hrS, hrT⟩ with hD'
  obtain ⟨Pr⟩ := ZhuModData.zhuPBWBottomInput_of_pbw V W
  have hSeq : D.S = D'.repS :=
    S_eq_repS Pr hW.1.c2Cofinite D hD D' hZ (fun _ _ _ => rfl)
  have hirr : Irredundant D'.Mfam := irredundant_famOf D hD
  have hcomp : Complete D'.Mfam := complete_famOf D hD
  have hv0 : Nonempty (ModuleEquiv W (D'.Mfam D.vac).isMod (adjointModule W)) := hD.vac_iso
  have hv : W.vacuum ≠ 0 := hW.1.toStronglyFinite.vacuum_ne_zero
  obtain ⟨σ, hσ, hvac, hSC⟩ := exists_charge hW D hD
  obtain ⟨-, hunit, -⟩ := zhu_facts hW D hD
  have hσ0 : σ D.vac = D.vac := by
    have h1 := hvac D.vac D.vac
    rw [hunit, if_pos rfl] at h1
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h1
    exact one_ne_zero h1
  let M := canonicalModel hW D hD
  let F : FusionChoice W := M.F
  letI := monoidalCategoryOfStronglyRational_pbw F hW.1
  haveI := monoidalPreadditive_pbw F hW.1
  haveI := monoidalLinear_pbw F hW.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hW.1
  let H := ordinaryFourPointInput_pbw F hW.1
  -- the genus-zero data
  set a := σ b with ha
  have h1 : famFusion D' b a D.vac ≠ 0 := by
    change fus D b (σ b) D.vac ≠ 0
    rw [hvac, if_pos rfl]; exact one_ne_zero
  have h2 : famFusion D' a b D.vac ≠ 0 := by
    rw [famFusion, BraidingSkew.fusionRule_swap]; exact h1
  obtain ⟨ε, hε⟩ := exists_ne_zero_to_vacuum hW F D' D.vac hv0 a b h2
  obtain ⟨η, hη⟩ := exists_ne_zero_from_vacuum hW F D' hcomp D.vac hv0 b a h1
  choose rr lab inc proj htot using fun x =>
    exists_split hW.1 D' hcomp (tensorObj F (famObj D' b) (famObj D' x))
  let c : TransferChoice F D' a b := ⟨ε, hε, η, hη, rr, lab, inc, proj, htot⟩
  choose β hβ using fun x j => endo_scalar D' (c.lab x j) (bTransfer F H c x j)
  obtain ⟨s, hs⟩ := endo_scalar D' b (zigzag F H c)
  have hz : zigzag F H c ≠ 0 :=
    zigzagNonzeroInput_holds V W hW D.ι D' hZ hirr hcomp D.vac hv0 F H a b c
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hz (by rw [hs, zero_smul])
  obtain ⟨π, hπ⟩ := exists_vacuumRetraction F hW hcomp D.vac hv0 c.η c.η_ne
  obtain ⟨μ, hμ, hpi⟩ := piInt_eq_smul_skew hW F c hv π hπ
  -- genus one: `μ s d_b = e^{2πi h_b}`
  have iQ : (vacuumLW W hv).IsIrreducibleLW :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hW.1.simple
  have hrow := vacuumRow_explicit F H hW hZ hirr hcomp D.vac hv0 c hβ π hπ μ
    (fun hv' => vacuumSCovarianceInput_holds.{u, 0} V W hW D.ι D' hZ hirr hcomp F a b c hv')
    (fun hv' σ' hP ins τ => conjugation_explicit F hW.1 D' hZ hv' c π hP μ
      (fun n wa wb x τ' => traceFun_bracketModes_skew hW D' hv' (epsInt F c) (piInt F π) μ hpi
        n wb wa x τ')
      (intertwinerSubstitutionInput_holds V W hW (lwOf D' a) (lwOf D' b) (vacuumLW W hv')
        (lwOf_irreducible D' a) (lwOf_irreducible D' b)
        ((isSimple_iff_adjointModule_isIrreducible W).mp hW.1.simple) (epsInt F c)) ins τ)
    (fun η' hη' => channelSStabilityInput_holds.{u, 0} V W hW D.ι D' hZ hirr hcomp F a b c η' hη')
    (fun hv' η' hη' => channelIndependenceInput_holds.{u, 0} V W hW D.ι D' hZ hirr hcomp F a b c
      hv' η' hη') D.vac
  have htm : ∀ y, transferMatrix c β y D.vac = s * (if y = σ b then 1 else 0) := by
    intro y
    rw [transferMatrix_eq_zigzag_scalar hW D' hirr F H c β hβ s hs y D.vac]
    change s * ((fus D b y D.vac : ℕ) : ℂ) = _
    rw [hvac]
    split_ifs <;> simp
  simp only [htm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hrow
  rw [← hSeq] at hrow
  have hd : D.S D.vac (σ b) = D.S D.vac b := S_vac_sigma D.S σ hσ D.vac hσ0 hSC b
  rw [hd, hD.S_vac_left, hD.S_vac_vac] at hrow
  have hhv : (D'.h D.vac) = 0 := by
    change ((D.h D.vac : ℚ) : ℂ) = 0
    rw [hD.h_vac]; simp
  rw [hhv, sub_zero, sub_self, mul_zero, Complex.exp_zero, mul_one] at hrow
  have hS00 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  have hnum : μ * s * (D.d b : ℂ) = twistOf (D.h b : ℂ) := by
    have : (D.S00 : ℂ) * (μ * s * (D.d b : ℂ)) = (D.S00 : ℂ) * twistOf (D.h b : ℂ) := by
      rw [twistOf]
      change _ = _ * Complex.exp (2 * Real.pi * Complex.I * D'.h b)
      linear_combination hrow
    exact mul_left_cancel₀ hS00 this
  -- genus zero: `η ≫ β ≫ ε = μ⁻¹`
  have hg0 := coev_braid_ev_ord F c π hπ μ hμ hpi
  -- the exact pairing `(s⁻¹ η, ε)` in `Ordinary W`
  have hzig : zigX (C := Ordinary W) η ε = s • 𝟙 (famObj D' b) := hs
  let η' : 𝟙_ (Ordinary W) ⟶ famObj D' b ⊗ famObj D' a := s⁻¹ • η
  have hzig' : zigX η' ε = 𝟙 (famObj D' b) := by
    have : zigX η' ε = s⁻¹ • zigX η ε := by
      simp only [zigX, η', MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]
    rw [this, hzig, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  obtain ⟨t, ht⟩ := endo_scalar D' a (zigY η' ε)
  letI pO : ExactPairing (famObj D' b) (famObj D' a) := exactPairingOfZigzag η' ε hzig' t ht hε
  -- transport to the model
  letI := M.monoidalFunctor
  letI FC := M.fusion D hD
  set Xb := modelSimple M.E D b
  set Xa := modelSimple M.E D a
  let iB : M.E.functor.obj Xb ≅ famObj D' b := modelSimpleIso M.E D b
  let iA : M.E.functor.obj Xa ≅ famObj D' a := modelSimpleIso M.E D a
  letI pE : ExactPairing (M.E.functor.obj Xb) (M.E.functor.obj Xa) := exactPairingCongr iB iA
  set k : ℂ := s⁻¹ * μ⁻¹ with hk
  have hOrd : η_ (M.E.functor.obj Xb) (M.E.functor.obj Xa) ≫
      (β_ (M.E.functor.obj Xb) (M.E.functor.obj Xa)).hom ≫
        ε_ (M.E.functor.obj Xb) (M.E.functor.obj Xa) = k • 𝟙 _ := by
    have hcoev : η_ (M.E.functor.obj Xb) (M.E.functor.obj Xa) =
        (η' ≫ (famObj D' b ◁ iA.inv)) ≫ (iB.inv ▷ M.E.functor.obj Xa) := rfl
    have hev : ε_ (M.E.functor.obj Xb) (M.E.functor.obj Xa) =
        (M.E.functor.obj Xa ◁ iB.hom) ≫ (iA.hom ▷ famObj D' b) ≫ ε := rfl
    rw [hcoev, hev]
    simp only [Category.assoc]
    rw [BraidedCategory.braiding_naturality_left_assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
      whiskerLeft_id, Category.id_comp, BraidedCategory.braiding_naturality_right_assoc,
      ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
    have hbr : (β_ (famObj D' b) (famObj D' a)).hom = (braiding F (famObj D' b) (famObj D' a)).hom :=
      rfl
    rw [hbr]
    simp only [η', Linear.smul_comp]
    rw [hg0, smul_smul]
    rfl
  letI pC : ExactPairing Xb Xa := ExactPairing.ofFullyFaithful M.E.functor Xb Xa
  have hC : η_ Xb Xa ≫ (β_ Xb Xa).hom ≫ ε_ Xb Xa = k • 𝟙 _ := by
    apply M.E.functor.map_injective
    rw [map_coev_braid_ev M.E.functor (fun X Y => M.braiding_eq X Y) Xb Xa, hOrd,
      Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Category.id_comp,
      Linear.comp_smul, Functor.Monoidal.η_ε]
  -- the pivotal dimension
  have htw := modelTwist_simple M.E D hD b
  have htr : (modelPivotal M).trL (𝟙 Xb) =
      Complex.exp (2 * Real.pi * Complex.I * (D.h b : ℂ)) • (k • 𝟙 (𝟙_ M.C)) := by
    rw [modelPivotal, twistPivotal_trL_id (fun f => modelTwist_naturality M.E f) Xb Xa pC]
    rw [htw, MonoidalLinear.smul_whiskerRight, id_whiskerRight, Linear.smul_comp,
      Linear.comp_smul, Category.id_comp, hC]
  unfold PivotalStructure.qdim
  erw [htr]
  rw [smul_smul, toScalar_smul (FusionCategory.finrank_end_unit (C := M.C))]
  rw [hk]
  have hT : Complex.exp (2 * Real.pi * Complex.I * (D.h b : ℂ)) = μ * s * (D.d b : ℂ) := by
    rw [hnum]; rfl
  rw [hT]
  field_simp

end Main

/-! ## The main results -/

/-- **`HuangQDimInput`** (Huang's dimension theorem for the twist pivotal structure). -/
theorem huangQDimInput_holds : HuangQDimInput.{u} := by
  intro V _ _ W hW D hD r a
  letI := r
  exact qdim_eq_d hW D hD a

/-- **`HuangModularityInput`** (Huang 2008: `S̃ = S/S₀₀`, `dim M_a = d_a`,
multiplicativity), for the canonical model, every choice of right duals, and the twist pivotal
structure. -/
theorem huangModularityInput_holds : HuangModularityInput.{u} :=
  huangModularityInput_of_qdimInput huangQDimInput_holds

/-- **`HuangRepInput`**: the pinned ribbon realization of `Rep V` exists. -/
theorem huangRepInput_holds : HuangRepInput.{u} :=
  huangRepInput_of_qdimInput huangQDimInput_holds

/-- **The numerical Huang interface**: every nice `V` with modular data has a ribbon
realization (`HuangRibbonInterface`, the numerical shadow of `HuangHKLInterface`). -/
theorem huangRibbonInterface_holds : HuangRibbonInterface.{u, 0, 0} :=
  huangRibbonInterface_of_rep huangRepInput_holds

/-- **`HuangHKLInterface` reduces to HKL alone**: with Huang's half proved, the bundled
interface (a hypothesis of the conditional `gannonRayhaun_*` theorems) follows from
`HKLRepInput`. -/
theorem huangHKLInterface_of_hklRep (h : HKLRepInput.{u}) : HuangHKLInterface.{u, 0, 0} :=
  huangHKLInterface_of_rep huangRepInput_holds h

end VOA.Huang.HuangModularity
