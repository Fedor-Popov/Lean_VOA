/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BGPackageMatter

/-!
# The unitary factor `L_1(sl₂)` with its canonical form and compact conjugation

The endpoint takes an arbitrary invariant form `BB` and real structure `RB` on the unitary factor
`B = L_1(sl₂)` together with `hB : Unitary BB RB`. Beem–Garner's argument needs more of `(BB, RB)`
than unitarity (`CompactUnitaryB`: `ρ_B² = 1`, compact conjugation of the current modes,
skewness of the current modes). This file constructs the canonical choice and proves those
properties:

* `bForm` — the normalized canonical form `simpleForm 1` on `L_1(sl₂)`;
* `bRealStructure` — the universal compact conjugation descended through the maximal ideal
  (the same construction as `affineRealStructure` at level `-4/3`);
* `bCompactUnitary : CompactUnitaryB bForm bRealStructure` — **proved**;
* `bgMatterData hA : MatterBGData hA bForm bRealStructure` — the entire matter factor of the
  Beem–Garner data, **with no hypothesis besides `hA`**.

Unitarity of `L_1(sl₂)` for this pair, `Unitary bForm bRealStructure`, is **not** proved here; it
remains the input `hB` of the endpoint.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open AffineVOA AffineVOA.Inst
open scoped TensorProduct

noncomputable section

theorem bLevel_real : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _

private abbrev bUniversalRealStructure : RealStructure (universal 1 bNoncritical) :=
  compactRealStructure bLevel_real bNoncritical

/-- Universal compact conjugation at level one, as a semilinear map. -/
def bUniversalConj : WakModule 1 →ₛₗ[starRingEnd ℂ] WakModule 1 where
  toAddHom := bUniversalRealStructure.rho
  map_smul' := bUniversalRealStructure.antilinear

theorem bUniversalConj_sq (x : WakModule 1) : bUniversalConj (bUniversalConj x) = x :=
  compactRho_compactRho bLevel_real x

private theorem bUniversalConj_comap_isIdeal {I : Submodule ℂ (WakModule 1)}
    (hI : (universal 1 bNoncritical).IsIdeal I) :
    (universal 1 bNoncritical).IsIdeal (I.comap bUniversalConj) := by
  intro u v n hv
  change bUniversalRealStructure.rho ((universal 1 bNoncritical).smul u n v) ∈ I
  rw [bUniversalRealStructure.map_smul]
  exact hI _ _ n hv

theorem bUniversalConj_maxIdeal_stable :
    QuotVOA.maxGradedIdeal (universal 1 bNoncritical) ≤
      (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).comap bUniversalConj := by
  let I := QuotVOA.maxGradedIdeal (universal 1 bNoncritical)
  have hproper : (universal 1 bNoncritical).vacuum ∉ I.comap bUniversalConj := by
    intro hv
    change bUniversalRealStructure.rho (universal 1 bNoncritical).vacuum ∈ I at hv
    rw [bUniversalRealStructure.map_vacuum] at hv
    exact QuotVOA.vacuum_not_mem_maxGradedIdeal _
      (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero _ _) hv
  have hle : I.comap bUniversalConj ≤ I :=
    QuotVOA.le_maxGradedIdeal'
      (bUniversalConj_comap_isIdeal (QuotVOA.maxGradedIdeal_isIdeal _)) hproper
  intro x hx
  apply hle
  change bUniversalConj (bUniversalConj x) ∈ I
  simpa only [bUniversalConj_sq] using hx

/-- The descended compact conjugation on `L_1(sl₂)`. -/
def bConj : BSpace →ₛₗ[starRingEnd ℂ] BSpace :=
  (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mapQ
    (QuotVOA.maxGradedIdeal (universal 1 bNoncritical))
    bUniversalConj bUniversalConj_maxIdeal_stable

@[simp] theorem bConj_mkQ (x : WakModule 1) :
    bConj ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ (bUniversalConj x) := rfl

/-- **The compact real structure on `L_1(sl₂)`**, with square one. -/
def bRealStructure : RealStructure BVOA where
  rho := bConj.toAddMonoidHom
  antilinear := bConj.map_smulₛₗ
  map_smul := by
    intro u n v
    obtain ⟨u, rfl⟩ := (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ_surjective u
    obtain ⟨v, rfl⟩ := (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ_surjective v
    change bConj ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ
      ((universal 1 bNoncritical).smul u n v)) =
        BVOA.smul
          (bConj ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ u)) n
          (bConj ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ v))
    rw [bConj_mkQ, bConj_mkQ, bConj_mkQ, SimpleQuot.maxQuotientVOA_mkQ_smul]
    exact congrArg (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ
      (bUniversalRealStructure.map_smul u n v)
  map_vacuum := by
    change bConj ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ
      (universal 1 bNoncritical).vacuum) = _
    rw [bConj_mkQ]
    exact congrArg (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ
      bUniversalRealStructure.map_vacuum
  map_omega := by
    change bConj ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ
      (universal 1 bNoncritical).conformalVector) = _
    rw [bConj_mkQ]
    exact congrArg (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ
      bUniversalRealStructure.map_omega
  parity := fun _ => 1
  sq := by
    intro h v hv
    obtain ⟨v, rfl⟩ := (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ_surjective v
    change bConj (bConj ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ v)) = _
    rw [bConj_mkQ, bConj_mkQ, bUniversalConj_sq, one_smul]

theorem bRealStructure_rho (x : BSpace) : bRealStructure.rho x = bConj x := rfl

/-- The normalized canonical form on `L_1(sl₂)`. -/
abbrev bForm : InvariantForm BVOA := simpleForm 1 bNoncritical

theorem bMode_mkQ (a : Fin 3) (n : ℤ) (x : WakModule 1) :
    bMode a n ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ (J 1 a n x) := by
  have h : bMode a n ((QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ
        ((universal 1 bNoncritical).smul (currentState 1 a) n x) :=
    SimpleQuot.maxQuotientVOA_mkQ_smul _ _ _ _
  rw [h]
  congr 1
  exact smul_currentState_eq_J 1 bNoncritical a n x

/-- **The compactness hypotheses for `(bForm, bRealStructure)`**, all proved. -/
theorem bCompactUnitary : CompactUnitaryB bForm bRealStructure where
  sq x := by
    obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ_surjective x
    rw [bRealStructure_rho, bRealStructure_rho, bConj_mkQ, bConj_mkQ, bUniversalConj_sq]
  rho_mode a n x := by
    obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ_surjective x
    rw [bRealStructure_rho, bRealStructure_rho, bMode_mkQ, bConj_mkQ, bConj_mkQ, bMode_mkQ,
      ← map_neg]
    exact congrArg _ (compactRho_J bLevel_real (k := 1) a n x)
  skew a n x y := by
    obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ_surjective x
    obtain ⟨y, rfl⟩ := (QuotVOA.maxGradedIdeal (universal 1 bNoncritical)).mkQ_surjective y
    rw [bMode_mkQ, bMode_mkQ]
    change (simpleForm 1 bNoncritical).form _ _ = -(simpleForm 1 bNoncritical).form _ _
    rw [simpleForm_mkQ, simpleForm_mkQ]
    exact universalForm_current_adj bNoncritical a n x y

/-- **The matter factor of the Beem–Garner data, with no hypothesis besides `hA`.** -/
def bgMatterData (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    MatterBGData hA bForm bRealStructure :=
  matterBGData hA bCompactUnitary

/-! ### The remaining data -/

/-- **What remains of the Beem–Garner package** once `Λ`, the matter factor (`bgMatterData`), the
ghost form (`bgPG`) and the grading are fixed: the ghost conjugation data, and the two
statements about the BRST differential, `ρ_D` and `B_E`, for `ρ = ρ_M ⊗ ρ_G`, `B = B_M ⊗ B_G`. -/
structure BGGhostRemainder (hA : GradedUnitary affineForm affineRealStructure affineFlag) where
  G : GhostBGData bgPG
  hsG : G.s ≠ 0
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg bgGh ((j, g), (n : ℂ)) →
    brstρ (bgMatterData hA) G (brstQ x) =
      (κ * (-1 : ℂ) ^ g) • brstE n (brstρ (bgMatterData hA) G x)
  B_E : ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg bgGh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n,
      brstB (bgMatterData hA) G (brstE n u) v =
        -((-1 : ℂ) ^ g) * brstB (bgMatterData hA) G u (brstE n v)

/-- The factor data from the remainder. -/
def BGGhostRemainder.toFactor {hA : GradedUnitary affineForm affineRealStructure affineFlag}
    (Rm : BGGhostRemainder hA) : BGFactorData bgGh hA bForm bRealStructure where
  M := bgMatterData hA
  G := Rm.G
  hsM := one_ne_zero
  hsG := Rm.hsG
  κ := Rm.κ
  hκ := Rm.hκ
  ρ_D := Rm.ρ_D
  B_E := Rm.B_E

/-- **Affine GU ⇒ Lee–Yang GU, current best endpoint.** `Λ`, the whole matter factor, the
ghost form, its positivity and the standard grading are constructed/proved. `#print axioms`-clean,
conditional on: `hA` (the hypothesis), `hB` (unitarity of `L_1(sl₂)` for the canonical form and
compact conjugation), `Rm` (ghost conjugation data, `ρ_D`, `B_E`) and the downstream `symbols`,
`character`, `vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgRemainder
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure) (Rm : BGGhostRemainder hA)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2
        (((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).conj0)) :
    VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_bgFactor_colour hA hB Rm.toFactor symbols character
    vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
