/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteFactors
import VOA.Examples.AffineSl2BelowCriticalRealStructure
import VOA.Examples.AffineSl2BelowCriticalAnchor
import VOA.Examples.AffineSl2GoodFiltration
import VOA.Examples.VirasoroBoundaryRealStructure

/-!
# Concrete affine input for the Lee--Yang transfer assembly

The affine carrier is the actual maximal-ideal quotient at level `-4/3` used
in `Sl2CosetConcrete`.  Its normalized invariant form and corrected quotient
flag are already constructed in the library.  Here the universal compact
conjugation is descended through the maximal ideal, so none of these three
objects is an additional existence hypothesis of the transfer theorem.

OPEN: graded unitarity for this concrete triple.
-/

namespace VOA.LeeYangTransferAssembly

open Sl2CosetConcrete AffineSl2GeneralRigidity AffineSl2BelowCritical
open AffineVOA AffineVOA.Inst AffineVOA.HighestModule VertexOperatorAlgebra

noncomputable section

/-- The normalized canonical form on the actual simple affine factor. -/
abbrev affineForm : InvariantForm AVOA := simpleForm ALevel aNoncritical

theorem affineForm_normalized : affineForm.Normalized :=
  simpleForm_normalized ALevel aNoncritical

/-- The corrected current-and-stress flag descended to the actual simple factor. -/
def affineFlag : GradedFlag AVOA :=
  CorrectedR.correctedAffineRQuotientFlag ALevel aNoncritical
    (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical))
    (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _)

theorem affineFlag_modeCompatible : affineFlag.ModeCompatible :=
  CorrectedR.correctedAffineRQuotientFlag_modeCompatible ALevel aNoncritical
    (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical))
    (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _)

/-- Every simple current has corrected degree at most one. -/
theorem affineCurrent_mem_flag_one (a : Fin 3) :
    simpleCurrent ALevel aNoncritical a ∈ affineFlag.piece 1 1 := by
  apply Submodule.mem_map.mpr
  refine ⟨currentState ALevel a, ?_, rfl⟩
  exact ⟨CorrectedR.currentState_mem_piece_one ALevel aNoncritical a,
    currentState_mem_grading ALevel aNoncritical a⟩

/-- The simple Sugawara vector has corrected degree at most one. -/
theorem affineConformal_mem_flag_one : AVOA.conformalVector ∈ affineFlag.piece 1 2 := by
  apply Submodule.mem_map.mpr
  refine ⟨(universal ALevel aNoncritical).conformalVector, ?_, rfl⟩
  exact ⟨CorrectedR.conformalVector_mem_piece_one ALevel aNoncritical,
    (universal ALevel aNoncritical).conformalVector_mem_grading_two⟩

/-- The level of the first concrete affine factor is real. -/
theorem affineLevel_real : (starRingEnd ℂ) ALevel = ALevel := by
  rw [aLevel_eq]
  simp only [map_div₀, map_neg, map_ofNat]

private abbrev affineUniversalRealStructure :
    RealStructure (universal ALevel aNoncritical) :=
  compactRealStructure affineLevel_real aNoncritical

/-- Universal compact conjugation, bundled as a semilinear map for quotient descent. -/
def affineUniversalConj :
    WakModule ALevel →ₛₗ[starRingEnd ℂ] WakModule ALevel where
  toAddHom := affineUniversalRealStructure.rho
  map_smul' := affineUniversalRealStructure.antilinear

theorem affineUniversalConj_sq (x : WakModule ALevel) :
    affineUniversalConj (affineUniversalConj x) = x :=
  compactRho_compactRho affineLevel_real x

private theorem affineUniversalConj_comap_isIdeal
    {I : Submodule ℂ (WakModule ALevel)}
    (hI : (universal ALevel aNoncritical).IsIdeal I) :
    (universal ALevel aNoncritical).IsIdeal (I.comap affineUniversalConj) := by
  intro u v n hv
  change affineUniversalRealStructure.rho
    ((universal ALevel aNoncritical).smul u n v) ∈ I
  rw [affineUniversalRealStructure.map_smul]
  exact hI _ _ n hv

/-- Compact conjugation preserves the actual maximal ideal.  Its inverse image
is a proper ideal, and applying involutivity gives the reverse inclusion. -/
theorem affineUniversalConj_maxIdeal_stable :
    QuotVOA.maxGradedIdeal (universal ALevel aNoncritical) ≤
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).comap
        affineUniversalConj := by
  let I := QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)
  have hproper : (universal ALevel aNoncritical).vacuum ∉
      I.comap affineUniversalConj := by
    intro hv
    change affineUniversalRealStructure.rho
      (universal ALevel aNoncritical).vacuum ∈ I at hv
    rw [affineUniversalRealStructure.map_vacuum] at hv
    exact QuotVOA.vacuum_not_mem_maxGradedIdeal _
      (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero _ _) hv
  have hle : I.comap affineUniversalConj ≤ I :=
    QuotVOA.le_maxGradedIdeal'
      (affineUniversalConj_comap_isIdeal (QuotVOA.maxGradedIdeal_isIdeal _)) hproper
  intro x hx
  apply hle
  change affineUniversalConj (affineUniversalConj x) ∈ I
  simpa only [affineUniversalConj_sq] using hx

/-- The descended compact conjugation on the actual simple affine factor. -/
def affineConj : ASpace →ₛₗ[starRingEnd ℂ] ASpace :=
  (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mapQ
    (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical))
    affineUniversalConj affineUniversalConj_maxIdeal_stable

@[simp] theorem affineConj_mkQ (x : WakModule ALevel) :
    affineConj ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
        (affineUniversalConj x) := rfl

/-- The compact real structure on `L_{-4/3}(sl2)`, with square equal to one. -/
def affineRealStructure : RealStructure AVOA where
  rho := affineConj.toAddMonoidHom
  antilinear := affineConj.map_smulₛₗ
  map_smul := by
    intro u n v
    obtain ⟨u, rfl⟩ :=
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective u
    obtain ⟨v, rfl⟩ :=
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective v
    change affineConj ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
      ((universal ALevel aNoncritical).smul u n v)) =
        AVOA.smul
          (affineConj ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ u)) n
          (affineConj ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ v))
    rw [affineConj_mkQ, affineConj_mkQ, affineConj_mkQ,
      SimpleQuot.maxQuotientVOA_mkQ_smul]
    exact congrArg (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
      (affineUniversalRealStructure.map_smul u n v)
  map_vacuum := by
    change affineConj ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
      (universal ALevel aNoncritical).vacuum) = _
    rw [affineConj_mkQ]
    exact congrArg (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
      affineUniversalRealStructure.map_vacuum
  map_omega := by
    change affineConj ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
      (universal ALevel aNoncritical).conformalVector) = _
    rw [affineConj_mkQ]
    exact congrArg (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
      affineUniversalRealStructure.map_omega
  parity := fun _ => 1
  sq := by
    intro h v hv
    obtain ⟨v, rfl⟩ :=
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective v
    change affineConj (affineConj
      ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ v)) = _
    rw [affineConj_mkQ, affineConj_mkQ, affineUniversalConj_sq, one_smul]

/-- The descended conjugation acts by compact Chevalley conjugation on currents. -/
theorem affineRealStructure_current (a : Fin 3) :
    affineRealStructure.rho (simpleCurrent ALevel aNoncritical a) =
      -simpleCurrent ALevel aNoncritical (adjointColour a) := by
  change affineConj ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
    (currentState ALevel a)) = _
  rw [affineConj_mkQ]
  change (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
    (affineUniversalRealStructure.rho (currentState ALevel a)) = _
  rw [(compactRealStructure_isCompact affineLevel_real aNoncritical).current, map_neg]
  rfl

@[simp] theorem affineRealStructure_parity (n : ℤ) :
    affineRealStructure.parity n = 1 := rfl

/-- The already constructed partition-basis real structure at Lee--Yang
central charge, obtained from the boundary family at index two. -/
def leeYangRealStructure : RealStructure (VirSimple.virasoroSimple LeeYang.leeYangC) :=
  virasoroSimpleRealStructure
    ((VirGradedUnitarity.boundaryBackgroundCharge_spec 2).trans
      VirGradedUnitarity.boundaryCharge_two_eq_leeYangC)
    (VirGradedUnitarity.boundaryBackgroundCharge_fixed 2)

/-- Any real structure preserves integer conformal weight because it commutes
with `L₀` and conjugation fixes the integer eigenvalue. -/
theorem realStructure_mem_grading {X : Type*} [AddCommGroup X] [Module ℂ X]
    {V : VertexOperatorAlgebra X} (R : RealStructure V) {n : ℤ} {x : X}
    (hx : x ∈ V.grading n) : R.rho x ∈ V.grading n := by
  rw [Deform.grading_eq_L_zero_eigenspace, Module.End.mem_eigenspace_iff]
  rw [← R.rho_L, V.L_zero_grading x hx, R.antilinear, map_intCast]

/-- Canonical Lee--Yang conjugation restricted to one actual conformal weight. -/
def leeYangRhoWeight (n : ℤ) :
    (VirSimple.virasoroSimple LeeYang.leeYangC).grading n →ₛₗ[starRingEnd ℂ]
      (VirSimple.virasoroSimple LeeYang.leeYangC).grading n where
  toFun x := ⟨leeYangRealStructure.rho x, realStructure_mem_grading _ x.property⟩
  map_add' x y := Subtype.ext (leeYangRealStructure.map_add x y)
  map_smul' c x := Subtype.ext (leeYangRealStructure.antilinear c x)

@[simp] theorem leeYangRhoWeight_apply_coe (n : ℤ)
    (x : (VirSimple.virasoroSimple LeeYang.leeYangC).grading n) :
    (leeYangRhoWeight n x : VirModule.VirUniv LeeYang.leeYangC ⧸
      VirSimple.maxIdealVir LeeYang.leeYangC) = leeYangRealStructure.rho x := rfl

/-- The actual auxiliary affine factor carries its normalized universal form. -/
abbrev auxiliaryForm : InvariantForm UVOA := universalForm (-11 / 3) uNoncritical

theorem auxiliaryLevel_real : (starRingEnd ℂ) (-11 / 3 : ℂ) = -11 / 3 := by
  simp only [map_div₀, map_neg, map_ofNat]

/-- Compact conjugation on the auxiliary universal affine factor. -/
abbrev auxiliaryRealStructure : RealStructure UVOA :=
  compactRealStructure auxiliaryLevel_real uNoncritical

/-- The ordinary current-PBW flag used on the auxiliary factor. -/
abbrev auxiliaryFlag : GradedFlag UVOA := ordinaryFlag (-11 / 3) uNoncritical

/-- The auxiliary level is below critical, so its required graded unitarity is
an existing theorem, specialized to the actual factor in the BRST complex. -/
theorem auxiliaryGradedUnitary :
    GradedUnitary auxiliaryForm auxiliaryRealStructure auxiliaryFlag := by
  have h := universal_gradedUnitary_belowCritical_unconditional
    (-11 / 3 : ℝ) (by norm_num)
  have hlevel : ((-11 / 3 : ℝ) : ℂ) = (-11 / 3 : ℂ) := by norm_num
  dsimp only [compactRealFamily] at h
  have specialize : ∀ (k : ℂ) (hk : k + 2 ≠ 0)
      (hr : (starRingEnd ℂ) k = k), k = ((-11 / 3 : ℝ) : ℂ) →
      GradedUnitary (universalForm k hk) (compactRealStructure hr hk)
        (ordinaryFlag k hk) := by
    intro k hk hr he
    subst k
    exact h
  exact specialize _ uNoncritical auxiliaryLevel_real hlevel.symm

end
end VOA.LeeYangTransferAssembly
