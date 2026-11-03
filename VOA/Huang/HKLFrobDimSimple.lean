/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangModularityQDim
import VOA.Huang.HuangRigidOrdinary
import VOA.Huang.HKLFrobDimAbstract

/-!
# Huang's dimension theorem directly on `Ordinary W`, for an arbitrary fusion choice

`HuangModularity.qdim_eq_d` computes the twist-pivotal dimension on the canonical small model,
which is built on the fixed fusion choice `fusionChoice_pbw`.  Here the same computation is run
directly on `Ordinary W` with the monoidal structure of an ARBITRARY fusion choice `F` and any
right duals:

* `twistPivotal_trL_module` — `tr(𝟙_{M_b}) = d_b • 𝟙` for the twist pivotal structure
  `twistPivotal twistIso` (genus zero: `coev_braid_ev_ord`; genus one: `vacuumRow_explicit`;
  twist eigenvalue: `twistIso_module_eq`).  The proof is the `Ordinary`-level half of
  `qdim_eq_d`, with no transport to a model.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Huang.HKLRational

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Module VOA Complex
  VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.BraidRibbon
  VOA.Huang.TensorCat.RepPackaging VOA.Huang.Tannakian VOA.Huang.HuangRigid
  VOA.Huang.FusionProduct VOA.Huang.FusionUnit VOA.Huang.SPinning VOA.Huang.VerlindeEigen
  VOA.Huang.VerlindeFusion VOA.Huang.VerlindeTransport VOA.Huang.GenusOneG1c
  VOA.Huang.GenusOneG1d VOA.Huang.GenusOneG1f VOA.Huang.HuangModularity
open VOA.Huang.GenusTwoPoint (vacuumLW)

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- **Huang's dimension theorem on `Ordinary W`, any fusion choice, any right duals**:
the twist-pivotal trace of `𝟙_{M_b}` is `d_b • 𝟙`. -/
theorem twistPivotal_trL_module (hW : Nice W) (F : FusionChoice W)
    (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData) (b : D.ι) :
    letI := monoidalCategoryOfStronglyRational_pbw F hW.1
    letI := HexagonClose.braidedCategory_stronglyRational_pbw F hW.1
    ∀ r : RightRigidCategory (Ordinary W),
      (letI := r
       (twistPivotal (θ := fun X => twistIso X) (fun f => twist_naturality f)).trL
        (𝟙 (Ordinary.of (D.module b)))) = (D.d b : ℂ) • 𝟙 _ := by
  classical
  letI := monoidalCategoryOfStronglyRational_pbw F hW.1
  haveI := monoidalPreadditive_pbw F hW.1
  haveI := monoidalLinear_pbw F hW.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hW.1
  intro r
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
  let pO : ExactPairing (famObj D' b) (famObj D' a) := exactPairingOfZigzag η' ε hzig' t ht hε
  have hbr : (β_ (famObj D' b) (famObj D' a)).hom = (braiding F (famObj D' b) (famObj D' a)).hom :=
    rfl
  have hOrd : η' ≫ (β_ (famObj D' b) (famObj D' a)).hom ≫ ε = (s⁻¹ * μ⁻¹) • 𝟙 _ := by
    rw [hbr]
    simp only [η', Linear.smul_comp]
    rw [hg0, smul_smul]
    rfl
  -- the twist eigenvalue on `M_b`
  have htw : (twistIso (famObj D' b)).hom =
      Complex.exp (2 * Real.pi * Complex.I * (D.h b : ℂ)) • 𝟙 (famObj D' b) :=
    twistIso_module_eq D hD b
  letI := r
  change (twistPivotal (θ := fun X => twistIso X) (fun f => twist_naturality f)).trL
    (𝟙 (famObj D' b)) = (D.d b : ℂ) • 𝟙 _
  rw [twistPivotal_trL_id (fun f => twist_naturality f) (famObj D' b) (famObj D' a) pO]
  have hθ : η' ≫ ((twistIso (famObj D' b)).hom ▷ famObj D' a) ≫
      (β_ (famObj D' b) (famObj D' a)).hom ≫ ε =
      Complex.exp (2 * Real.pi * Complex.I * (D.h b : ℂ)) •
        (η' ≫ (β_ (famObj D' b) (famObj D' a)).hom ≫ ε) := by
    simp only [htw, MonoidalLinear.smul_whiskerRight, id_whiskerRight, Linear.smul_comp,
      Linear.comp_smul, Category.id_comp]
  refine hθ.trans ?_
  rw [hOrd, smul_smul]
  congr 1
  have hT : Complex.exp (2 * Real.pi * Complex.I * (D.h b : ℂ)) = μ * s * (D.d b : ℂ) := by
    rw [hnum]; rfl
  rw [hT]
  field_simp

end VOA.Huang.HKLRational
