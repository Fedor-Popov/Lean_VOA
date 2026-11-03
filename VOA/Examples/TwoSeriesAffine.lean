/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesFactors
import VOA.Examples.LeeYangTransferAssemblyAffine

/-!
# Forms, conjugations and flags of the endpoint VOAs, for any `CosetLevels`

The generalization of `LeeYangTransferAssemblyAffine`:

* `affineForm L`, `affineFlag L`, `affineRealStructure L` — the canonical normalized form,
  the corrected current-and-stress flag, and the descended compact conjugation on the actual
  simple `L_{kA}(sl₂)`.  The hypothesis `hA` of the transfer theorem is
  `GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)`.
* `auxiliaryGradedUnitary L` — graded unitarity of the auxiliary universal factor, proved
  for every `L` from the below-critical theorem (`kU < -2`).
* `targetRealStructure L` — the partition-basis real structure on `L(c)`.

At `L = leeYangLevels` all of these are the existing objects, by `rfl`.
-/

namespace VOA.TwoSeries

open VOA.Sl2CosetConcrete AffineSl2GeneralRigidity AffineSl2BelowCritical
open AffineVOA AffineVOA.Inst AffineVOA.HighestModule VertexOperatorAlgebra

noncomputable section

variable (L : CosetLevels)

/-- The normalized canonical form on the actual simple affine factor. -/
abbrev affineForm : InvariantForm (AVOA L) := simpleForm L.kA L.aNoncritical

/-- The corrected current-and-stress flag descended to the actual simple factor. -/
def affineFlag : GradedFlag (AVOA L) :=
  CorrectedR.correctedAffineRQuotientFlag L.kA L.aNoncritical
    (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical))
    (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _)

private abbrev affineUniversalRealStructure : RealStructure (universal L.kA L.aNoncritical) :=
  compactRealStructure L.aReal L.aNoncritical

/-- Universal compact conjugation, bundled as a semilinear map for quotient descent. -/
def affineUniversalConj : WakModule L.kA →ₛₗ[starRingEnd ℂ] WakModule L.kA where
  toAddHom := (affineUniversalRealStructure L).rho
  map_smul' := (affineUniversalRealStructure L).antilinear

theorem affineUniversalConj_sq (x : WakModule L.kA) :
    affineUniversalConj L (affineUniversalConj L x) = x :=
  compactRho_compactRho L.aReal x

private theorem affineUniversalConj_comap_isIdeal
    {I : Submodule ℂ (WakModule L.kA)}
    (hI : (universal L.kA L.aNoncritical).IsIdeal I) :
    (universal L.kA L.aNoncritical).IsIdeal (I.comap (affineUniversalConj L)) := by
  intro u v n hv
  change (affineUniversalRealStructure L).rho
    ((universal L.kA L.aNoncritical).smul u n v) ∈ I
  rw [(affineUniversalRealStructure L).map_smul]
  exact hI _ _ n hv

theorem affineUniversalConj_maxIdeal_stable :
    QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical) ≤
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).comap
        (affineUniversalConj L) := by
  let I := QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)
  have hproper : (universal L.kA L.aNoncritical).vacuum ∉
      I.comap (affineUniversalConj L) := by
    intro hv
    change (affineUniversalRealStructure L).rho
      (universal L.kA L.aNoncritical).vacuum ∈ I at hv
    rw [(affineUniversalRealStructure L).map_vacuum] at hv
    exact QuotVOA.vacuum_not_mem_maxGradedIdeal _
      (AffineSl2BoundaryMaximalIdeal.affineSl2_vacuum_ne_zero _ _) hv
  have hle : I.comap (affineUniversalConj L) ≤ I :=
    QuotVOA.le_maxGradedIdeal'
      (affineUniversalConj_comap_isIdeal L (QuotVOA.maxGradedIdeal_isIdeal _)) hproper
  intro x hx
  apply hle
  change affineUniversalConj L (affineUniversalConj L x) ∈ I
  simpa only [affineUniversalConj_sq] using hx

/-- The descended compact conjugation on the actual simple affine factor. -/
def affineConj : ASpace L →ₛₗ[starRingEnd ℂ] ASpace L :=
  (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mapQ
    (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical))
    (affineUniversalConj L) (affineUniversalConj_maxIdeal_stable L)

@[simp] theorem affineConj_mkQ (x : WakModule L.kA) :
    affineConj L ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
        (affineUniversalConj L x) := rfl

/-- The compact real structure on `L_{kA}(sl₂)`. -/
def affineRealStructure : RealStructure (AVOA L) where
  rho := (affineConj L).toAddMonoidHom
  antilinear := (affineConj L).map_smulₛₗ
  map_smul := by
    intro u n v
    obtain ⟨u, rfl⟩ :=
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective u
    obtain ⟨v, rfl⟩ :=
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective v
    change affineConj L ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
      ((universal L.kA L.aNoncritical).smul u n v)) =
        (AVOA L).smul
          (affineConj L ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ u)) n
          (affineConj L ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ v))
    rw [affineConj_mkQ, affineConj_mkQ, affineConj_mkQ,
      SimpleQuot.maxQuotientVOA_mkQ_smul]
    exact congrArg (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
      ((affineUniversalRealStructure L).map_smul u n v)
  map_vacuum := by
    change affineConj L ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
      (universal L.kA L.aNoncritical).vacuum) = _
    rw [affineConj_mkQ]
    exact congrArg (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
      (affineUniversalRealStructure L).map_vacuum
  map_omega := by
    change affineConj L ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
      (universal L.kA L.aNoncritical).conformalVector) = _
    rw [affineConj_mkQ]
    exact congrArg (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
      (affineUniversalRealStructure L).map_omega
  parity := fun _ => 1
  sq := by
    intro h v hv
    obtain ⟨v, rfl⟩ :=
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective v
    change affineConj L (affineConj L
      ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ v)) = _
    rw [affineConj_mkQ, affineConj_mkQ, affineUniversalConj_sq, one_smul]

/-! ### The auxiliary universal factor -/

abbrev auxiliaryForm : InvariantForm (UVOA L) := universalForm L.kU L.uNoncritical

abbrev auxiliaryRealStructure : RealStructure (UVOA L) :=
  compactRealStructure L.uReal L.uNoncritical

abbrev auxiliaryFlag : GradedFlag (UVOA L) := ordinaryFlag L.kU L.uNoncritical

/-- The auxiliary factor is graded unitary for every `L`, since `kU < -2`. -/
theorem auxiliaryGradedUnitary :
    GradedUnitary (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L) := by
  have h := universal_gradedUnitary_belowCritical_unconditional L.kUr L.kUr_lt
  dsimp only [compactRealFamily] at h
  have specialize : ∀ (k : ℂ) (hk : k + 2 ≠ 0)
      (hr : (starRingEnd ℂ) k = k), k = (L.kUr : ℂ) →
      GradedUnitary (universalForm k hk) (compactRealStructure hr hk)
        (ordinaryFlag k hk) := by
    intro k hk hr he
    subst k
    exact h
  exact specialize _ L.uNoncritical L.uReal L.kU_eq

/-! ### The target -/

/-- The partition-basis real structure on the simple Virasoro VOA `L(c)`. -/
def targetRealStructure : RealStructure (VirSimple.virasoroSimple L.c) :=
  virasoroSimpleRealStructure L.lam_spec (VirGradedUnitarity.boundaryBackgroundCharge_fixed L.m)

/-! ### Lee–Yang specialization, definitionally -/

theorem affineForm_leeYang :
    affineForm leeYangLevels = LeeYangTransferAssembly.affineForm := rfl

theorem affineFlag_leeYang :
    affineFlag leeYangLevels = LeeYangTransferAssembly.affineFlag := rfl

theorem affineRealStructure_leeYang :
    affineRealStructure leeYangLevels = LeeYangTransferAssembly.affineRealStructure := rfl

theorem auxiliaryForm_leeYang :
    auxiliaryForm leeYangLevels = LeeYangTransferAssembly.auxiliaryForm := rfl

theorem auxiliaryRealStructure_leeYang :
    auxiliaryRealStructure leeYangLevels = LeeYangTransferAssembly.auxiliaryRealStructure := rfl

theorem targetRealStructure_leeYang :
    targetRealStructure leeYangLevels = LeeYangTransferAssembly.leeYangRealStructure := rfl

end

end VOA.TwoSeries
