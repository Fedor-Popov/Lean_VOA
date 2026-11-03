/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesAffine
import VOA.Examples.Sl2CosetConcreteVOA

/-!
# The coset VOA `(L_{kA} ⊗ L_1) // L_{kA+1}` at central charge `c`, for any `CosetLevels`

The generalization of `Sl2CosetConcreteOmega`, the concrete tails of `Sl2CosetConcreteVertex`
and `Sl2CosetConcreteTensorConformal`, `Sl2CosetConcreteCohomology`, and `Sl2CosetConcreteVOA`.

* `cosetVOA L` — the conformal VOA on the actual diagonal commutant, with central charge
  `L.c`; the Virasoro relation is proved from `L.charge` (the arithmetic of `c(k)+1-c(k+1)`);
* `cosetToComplex L`, `cosetMapH0 L` — the actual map into the level-`L` BRST complex,
  closed, relative, and multiplicative.
-/

namespace VOA.TwoSeries

open Sl2SemiInfinite Sl2Coset VOA.Sl2CosetConcrete
open Module (End)
open scoped TensorProduct

noncomputable section

variable (L : CosetLevels)

theorem kAct_noncritical : L.kAct + 2 ≠ 0 := by
  rw [L.kAct_eq]; exact L.aNoncritical

/-! ### The coset conformal vector -/

theorem aAction_sugawara :
    sugawaraState (aAction L).toAffineSl2Action = (AVOA L).conformalVector := by
  change (2 * (L.kAct + 2))⁻¹ •
    quadraticState (simpleAction L.kA L.aNoncritical).toAffineSl2Action = _
  rw [L.kAct_eq]
  exact simpleAction_sugawara L.kA L.aNoncritical

def ambientConformal : ASpace L ⊗[ℂ] BSpace :=
  (AVOA L).conformalVector ⊗ₜ[ℂ] BSVA.vacuum + (ASVA L).vacuum ⊗ₜ[ℂ] BVOA.conformalVector

def diagonalSugawara : ASpace L ⊗[ℂ] BSpace :=
  sugawaraState (diagonalAction L).toAffineSl2Action

def cosetOmega : ASpace L ⊗[ℂ] BSpace := ambientConformal L - diagonalSugawara L

theorem ambientConformal_eq_tensorSugawara :
    ambientConformal L =
      tensorSugawaraState (aAction L).toAffineSl2Action bAction.toAffineSl2Action := by
  simp only [ambientConformal, tensorSugawaraState, aAction_sugawara, bAction_sugawara]

def cosetConformalData : CosetConformalData (diagonalAction L).toAffineSl2Action
    (ambientConformal L) (diagonalSugawara L) := by
  rw [ambientConformal_eq_tensorSugawara]
  exact tensorCosetConformalData (aAction L).toAffineSl2Action bAction.toAffineSl2Action
    (kAct_noncritical L) (by norm_num) L.diagNoncritical
    (aParityCompatible L) bParityCompatible (abTensorGrading L)

theorem cosetOmega_mem : cosetOmega L ∈ cosetSubspace (diagonalAction L).toAffineSl2Action :=
  (cosetConformalData L).mem_coset

def cosetOmegaState : cosetSubspace (diagonalAction L).toAffineSl2Action :=
  ⟨cosetOmega L, cosetOmega_mem L⟩

theorem cosetOmega_weight : cosetOmega L ∈ (abSVA L).grading 2 := by
  rw [cosetOmega, ambientConformal_eq_tensorSugawara]
  exact tensorCosetConformalState_weight (aAction L).toAffineSl2Action
    bAction.toAffineSl2Action (kAct_noncritical L) (by norm_num) L.diagNoncritical
    (aParityCompatible L) bParityCompatible (abTensorGrading L)

/-! ### The ordinary vertex algebra on the commutant -/

theorem abPurelyEven : (abSVA L).parity 0 = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul x y =>
      exact TensorVA.tmul_mem_tenParity (ASVA L) BSVA
        (show x ∈ (ASVA L).parity 0 from Submodule.mem_top)
        (show y ∈ BSVA.parity 0 from Submodule.mem_top)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem abVacuumGrade : (abSVA L).grading 0 = ℂ ∙ (abSVA L).vacuum := by
  have hA : (ASVA L).grading 0 = ℂ ∙ (ASVA L).vacuum := by
    change (AVOA L).toPreVertexAlgebra.gradingC 0 = _
    rw [← show ((0 : ℤ) : ℂ) = 0 by simp, PreVertexAlgebra.gradingC_intCast]
    exact (AVOA L).vacuum_grade
  have hB : BSVA.grading 0 = ℂ ∙ BSVA.vacuum := by
    change BVOA.toPreVertexAlgebra.gradingC 0 = _
    rw [← show ((0 : ℤ) : ℂ) = 0 by simp, PreVertexAlgebra.gradingC_intCast]
    exact BVOA.vacuum_grade
  change TensorVA.tenGrading (ASVA L) BSVA 0 = ℂ ∙ ((ASVA L).vacuum ⊗ₜ[ℂ] BSVA.vacuum)
  rw [tenGrading_zero_eq (ASVA L) BSVA (aNatSupported L) bNatSupported]
  apply le_antisymm
  · intro x hx
    refine TensorVA.tenSub_induction (Submodule.zero_mem _)
      (fun _ _ => Submodule.add_mem _) (fun c _ => Submodule.smul_mem _ c) ?_ hx
    intro x hx y hy
    rw [hA, Submodule.mem_span_singleton] at hx
    rw [hB, Submodule.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    rw [Submodule.mem_span_singleton]
    exact ⟨c * d, by simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      smul_smul, mul_comm]⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact TensorVA.tmul_mem_tenSub (ASVA L).vacuum_mem BSVA.vacuum_mem

def cosetVertexAlgebra : PreVertexAlgebra (cosetSubspace (diagonalAction L).toAffineSl2Action) :=
  cosetVertexAlgebraOf (diagonalAction L).toAffineSl2Action (diagonalAction L).translation
    (abPurelyEven L) (abNatSupported L)

theorem cosetVertexAlgebra_positivity (n : ℤ) (hn : n < 0) :
    (cosetVertexAlgebra L).grading n = ⊥ :=
  cosetVertexAlgebraOf_positivity _ _ (abPurelyEven L) (abNatSupported L) n hn

theorem cosetVertexAlgebra_vacuum_grade :
    (cosetVertexAlgebra L).grading 0 = ℂ ∙ (cosetVertexAlgebra L).vacuum :=
  cosetVertexAlgebraOf_vacuum_grade _ _ (abPurelyEven L) (abNatSupported L) (abVacuumGrade L)

/-! ### Conformal modes -/

theorem ambientConformal_eq_tensorConformal :
    ambientConformal L = tensorConformal (AVOA L) BVOA := rfl

theorem ambientConformal_zero_mode :
    mode ((abSVA L).Y (ambientConformal L)) 0 = (diagonalAction L).translation.T :=
  tensorConformal_zero_mode (AVOA L) BVOA

theorem cosetOmega_L0 (h : ℂ) (x : ASpace L ⊗[ℂ] BSpace)
    (hx : x ∈ (abSVA L).grading h)
    (hc : x ∈ cosetSubspace (diagonalAction L).toAffineSl2Action) :
    mode ((abSVA L).Y (cosetOmega L)) 1 x = h • x := by
  rw [cosetOmega, map_sub, mode_sub, LinearMap.sub_apply]
  have hz := sugawara_mode_coset (diagonalAction L).toAffineSl2Action
    (diagonalAction L).translation hc 1 (by norm_num)
  change mode ((abSVA L).Y (ambientConformal L)) 1 x -
    mode ((abSVA L).Y (sugawaraState (diagonalAction L).toAffineSl2Action)) 1 x = _
  rw [hz, sub_zero]
  exact tensorConformal_L0 (AVOA L) BVOA h x hx

theorem cosetOmega_zero_mode (x : ASpace L ⊗[ℂ] BSpace)
    (hc : x ∈ cosetSubspace (diagonalAction L).toAffineSl2Action) :
    mode ((abSVA L).Y (cosetOmega L)) 0 x = (diagonalAction L).translation.T x := by
  rw [cosetOmega, map_sub, mode_sub, LinearMap.sub_apply]
  have hz := sugawara_mode_coset (diagonalAction L).toAffineSl2Action
    (diagonalAction L).translation hc 0 (by norm_num)
  change mode ((abSVA L).Y (ambientConformal L)) 0 x -
    mode ((abSVA L).Y (sugawaraState (diagonalAction L).toAffineSl2Action)) 0 x = _
  rw [hz, sub_zero, ambientConformal_zero_mode]

theorem cosetOmega_translation (x : ASpace L ⊗[ℂ] BSpace)
    (hc : x ∈ cosetSubspace (diagonalAction L).toAffineSl2Action) :
    (abSVA L).Y (mode ((abSVA L).Y (cosetOmega L)) 0 x) = deriv ((abSVA L).Y x) := by
  rw [cosetOmega_zero_mode L x hc]
  exact translation_state (diagonalAction L).translation x

/-! ### Central charge and the coset VOA -/

theorem aCentralCharge : (AVOA L).centralCharge = 3 * L.kA / (L.kA + 2) := by
  change (AffineSl2GeneralRigidity.universal L.kA L.aNoncritical).centralCharge = _
  rw [AffineVOA.Inst.closed_centralCharge]

/-- The coset central charge is `L.c`. -/
theorem cosetCentralCharge :
    (AVOA L).centralCharge + BVOA.centralCharge -
      3 * (L.kAct + 1) / ((L.kAct + 1) + 2) = L.c := by
  rw [aCentralCharge, bCentralCharge]
  exact L.charge

theorem cosetOmega_virasoro (m n : ℤ) :
    ⁅mode ((abSVA L).Y (cosetOmega L)) (m + 1), mode ((abSVA L).Y (cosetOmega L)) (n + 1)⁆ =
      ((m : ℂ) - n) • mode ((abSVA L).Y (cosetOmega L)) (m + n + 1) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * L.c) •
        (1 : End ℂ (ASpace L ⊗[ℂ] BSpace)) else 0 := by
  let Lm : ℤ → End ℂ (ASpace L ⊗[ℂ] BSpace) :=
    fun n => mode ((abSVA L).Y (ambientConformal L)) (n + 1)
  let D : ℤ → End ℂ (ASpace L ⊗[ℂ] BSpace) :=
    fun n => mode ((abSVA L).Y (diagonalSugawara L)) (n + 1)
  have hL := tensorConformal_virasoro (AVOA L) BVOA
  have hD := sugawara_virasoro (diagonalAction L).toAffineSl2Action
    (diagonalAction L).translation L.diagNoncritical
  have hC : ∀ m n, D m * (Lm n - D n) = (Lm n - D n) * D m := by
    intro m n
    have hc := sugawara_mode_coset_mode_commute (diagonalAction L).toAffineSl2Action
      (diagonalAction L).translation (cosetOmega_mem L) (m + 1) (n + 1)
    simpa only [cosetOmega, map_sub, mode_sub] using hc
  have h := virasoro_difference_of_commute Lm D
    ((AVOA L).centralCharge + BVOA.centralCharge)
    (3 * (L.kAct + 1) / ((L.kAct + 1) + 2)) hL hD hC m n
  rw [cosetCentralCharge] at h
  simpa only [Lm, D, cosetOmega, map_sub, mode_sub] using h

theorem cosetOmegaState_weight : cosetOmegaState L ∈ (cosetVertexAlgebra L).grading 2 := by
  change cosetOmega L ∈ (abSVA L).grading ((2 : ℤ) : ℂ)
  norm_num only [Int.cast_ofNat]
  exact cosetOmega_weight L

abbrev CosetSpace := cosetSubspace (diagonalAction L).toAffineSl2Action

/-- The actual conformal coset VOA, with central charge `L.c`. -/
def cosetVOA : VertexOperatorAlgebra (CosetSpace L) where
  toPreVertexAlgebra := cosetVertexAlgebra L
  conformalVector := cosetOmegaState L
  conformal_mem := cosetOmegaState_weight L
  centralCharge := L.c
  virasoro := by
    intro m n
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : End ℂ (ASpace L ⊗[ℂ] BSpace) => f (x : ASpace L ⊗[ℂ] BSpace))
      (cosetOmega_virasoro L m n)
    simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul] at h ⊢
    by_cases hmn : m + n = 0
    · simpa only [if_pos hmn, LinearMap.smul_apply, Module.End.one_apply,
        Submodule.coe_smul, cosetY_mode_coe] using h
    · simpa only [if_neg hmn, LinearMap.zero_apply, Submodule.coe_zero,
        cosetY_mode_coe] using h
  L0_grading := by
    intro n x hx
    exact Subtype.ext (cosetOmega_L0 L (n : ℂ) x hx x.property)
  translation := by
    intro x
    funext j
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact congrArg (fun f : FormalDist (End ℂ (ASpace L ⊗[ℂ] BSpace)) => f j y)
      (cosetOmega_translation L x x.property)
  vacuum_grade := cosetVertexAlgebra_vacuum_grade L
  positivity := cosetVertexAlgebra_positivity L

@[simp] theorem cosetVOA_vacuum :
    (cosetVOA L).vacuum = cosetVacuum (diagonalAction L).toAffineSl2Action := rfl

@[simp] theorem cosetVOA_centralCharge : (cosetVOA L).centralCharge = L.c := rfl

/-! ### The coset map into the level-`L` BRST complex -/

def cosetToComplex : CosetSpace L →ₗ[ℂ] MatterSpace L ⊗[ℂ] Sl2GhostSpace :=
  auxiliaryCosetToComplex (diagonalAction L) (uAction L) (abParityCompatible L)
    (uParityCompatible L) (abuTensorGrading L) L.sum

theorem cosetToComplex_apply (x : CosetSpace L) :
    cosetToComplex L x = (x.val ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum := rfl

theorem cosetToComplex_closed (x : CosetSpace L) : (brstComplex L).Q (cosetToComplex L x) = 0 :=
  auxiliaryCosetToComplex_closed (diagonalAction L) (uAction L) (abParityCompatible L)
    (uParityCompatible L) (abuTensorGrading L) L.sum x

theorem cosetToComplex_relative (x : CosetSpace L) :
    cosetToComplex L x ∈ relativeCarrier (matterAction L).toAffineSl2Action :=
  auxiliaryCosetToComplex_relative (diagonalAction L) (uAction L) (abParityCompatible L)
    (uParityCompatible L) (abuTensorGrading L) L.sum x

set_option maxHeartbeats 1600000 in
/-- The map into ghost-number-zero cohomology of the actual level-`L` complex. -/
def cosetMapH0 : CosetSpace L →ₗ[ℂ] (brstComplex L).H0 :=
  auxiliaryCosetToH0 (diagonalAction L) (uAction L) (abParityCompatible L)
    (uParityCompatible L) (abuTensorGrading L) L.sum (matterGhostTensorGrading L)

set_option maxHeartbeats 1600000 in
theorem cosetToCohomology_mode (x y : CosetSpace L) (n : ℤ) :
    ((cosetMapH0 L ((cosetVOA L).smul x n y) : (brstComplex L).Coh)) =
      mode ((brstComplex L).cohomology.Y (cosetMapH0 L x)) n (cosetMapH0 L y) :=
  auxiliaryCosetToCohomology_mode (diagonalAction L) (uAction L) (abParityCompatible L)
    (uParityCompatible L) (abuTensorGrading L) L.sum (matterGhostTensorGrading L) x y n

theorem cosetToH0_vacuum :
    ((cosetMapH0 L (cosetVOA L).vacuum : (brstComplex L).Coh)) =
      (brstComplex L).cohomology.vacuum := rfl

end

end VOA.TwoSeries
