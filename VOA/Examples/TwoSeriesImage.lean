/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCoset
import VOA.Examples.LeeYangShortcutImage
import VOA.Examples.LeeYangShortcutRelative

/-!
# The Virasoro image in the level-`L` BRST cohomology, and its finite relative complexes

The generalization of `LeeYangShortcutVirasoro` (concrete part), `LeeYangShortcutImage`
(concrete part), `LeeYangTransferAssemblyComplex`, and the first half of
`LeeYangShortcutRelative`, from `c = -22/5` to `c = L.c`.

* `virasoroToH0 L` — the universal Virasoro VOA `V^c` maps to `H⁰` through the coset stress
  tensor; its kernel lies in the maximal ideal (`virasoroToH0_ker_le_maxIdeal`) because the
  vacuum class survives.  No coset simplicity or coset identification is used.
* `relativeWeight L n` — the actual finite relative BRST complex at conformal weight `n`.
* `universalWeightClass L n` — the class map from the universal weight-`n` space; relative
  exactness kills the simple projection (`universalWeightCycles_exact_zero`).
-/

namespace VOA.TwoSeries

open VirModule VirSimple VirGoodFil Sl2SemiInfinite VOA.Sl2CosetConcrete
open LeeYangShortcut LeeYangCosetTransfer GradedUnitaryCohomology
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

/-! ### The Virasoro map into cohomology -/

/-- The universal Virasoro VOA maps to the coset through the coset stress tensor. -/
def virasoroToCoset : VirUniv L.c →ₗ[ℂ] CosetSpace L :=
  conformalEval (cosetVOA L) rfl

theorem virasoroToCoset_hom : IsVOAHom (virasoroVOA L.c) (cosetVOA L) (virasoroToCoset L) :=
  conformalEval_hom (cosetVOA L) rfl

@[simp] theorem virasoroToCoset_vacuum :
    virasoroToCoset L (vacVec L.c) = (cosetVOA L).vacuum :=
  conformalEval_vacuum (cosetVOA L) rfl

def virasoroToH0 : VirUniv L.c →ₗ[ℂ] (brstComplex L).H0 :=
  (cosetMapH0 L).comp (virasoroToCoset L)

def virasoroToCoh : VirUniv L.c →ₗ[ℂ] (brstComplex L).Coh :=
  (brstComplex L).H0.subtype.comp (virasoroToH0 L)

theorem virasoroToCoh_vacuum :
    virasoroToCoh L (vacVec L.c) = (brstComplex L).cohomology.vacuum := by
  change ((cosetMapH0 L (virasoroToCoset L _)) : (brstComplex L).Coh) = _
  rw [virasoroToCoset_vacuum]
  exact cosetToH0_vacuum L

theorem virasoroToCoh_mode (x y : VirUniv L.c) (n : ℤ) :
    virasoroToCoh L ((virasoroVOA L.c).smul x n y) =
      mode ((brstComplex L).cohomology.Y (virasoroToCoh L x)) n (virasoroToCoh L y) := by
  change ((cosetMapH0 L (virasoroToCoset L _)) : (brstComplex L).Coh) = _
  rw [(virasoroToCoset_hom L).map_smul]
  exact cosetToCohomology_mode L (virasoroToCoset L x) (virasoroToCoset L y) n

theorem virasoroToH0_vacuum_ne_zero : virasoroToH0 L (vacVec L.c) ≠ 0 := by
  intro h
  apply brstComplex_cohomology_vacuum_ne_zero L
  rw [← virasoroToCoh_vacuum]
  exact congrArg Subtype.val h

theorem virasoroToH0_ker_isIdeal :
    (virasoroVOA L.c).IsIdeal (LinearMap.ker (virasoroToH0 L)) := by
  intro x y n hy
  rw [LinearMap.mem_ker] at hy ⊢
  apply Subtype.ext
  change virasoroToCoh L ((virasoroVOA L.c).smul x n y) = 0
  rw [virasoroToCoh_mode]
  have hy' : virasoroToCoh L y = 0 := congrArg Subtype.val hy
  rw [hy', map_zero]

/-- The kernel of the Virasoro image map lies in the maximal ideal. -/
theorem virasoroToH0_ker_le_maxIdeal : LinearMap.ker (virasoroToH0 L) ≤ maxIdealVir L.c :=
  le_maxIdealVir _ (virasoroToH0_ker_isIdeal L) (virasoroToH0_vacuum_ne_zero L)

/-! ### The finite relative complexes -/

abbrev BRSTSpace := MatterSpace L ⊗[ℂ] Sl2GhostSpace

/-- The actual relative BRST complex at conformal weight `n`. -/
def relativeWeight (n : ℤ) : Submodule ℂ (BRSTSpace L) :=
  relativeCarrier (matterAction L).toAffineSl2Action ⊓ (brstSVA L).grading (n : ℂ)

instance relativeWeight_finite (n : ℤ) : FiniteDimensional ℂ (relativeWeight L n) := by
  letI := (brstSVA L).finrank (n : ℂ)
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (show relativeWeight L n ≤ (brstSVA L).grading (n : ℂ) from
      inf_le_right))
    (fun x y h => Subtype.ext (congrArg (fun z : (brstSVA L).grading (n : ℂ) =>
      (z : BRSTSpace L)) h))

/-- Restriction of the actual BRST residue. -/
def relativeDifferential (n : ℤ) : relativeWeight L n →ₗ[ℂ] relativeWeight L n :=
  (brstComplex L).Q.restrict (fun x hx =>
    ⟨semiInfiniteQ_mem_relativeCarrier (matterAction L) (matterParityCompatible L)
      (matterGhostTensorGrading L) hx.1, (brstComplex L).Q_wt _ x hx.2⟩)

@[simp] theorem relativeDifferential_coe (n : ℤ) (x : relativeWeight L n) :
    (relativeDifferential L n x : BRSTSpace L) = (brstComplex L).Q x := rfl

def weightCyclesToAbsolute (n : ℤ) :
    LinearMap.ker (relativeDifferential L n) →ₗ[ℂ] (brstComplex L).kerQ :=
  ((relativeWeight L n).subtype.comp
    (LinearMap.ker (relativeDifferential L n)).subtype).codRestrict _
    (fun x => congrArg Subtype.val x.property)

theorem weightBoundary_toAbsolute (n : ℤ)
    (x : LinearMap.ker (relativeDifferential L n))
    (hx : x ∈ boundariesInCycles (K := relativeWeight L n) (relativeDifferential L n)) :
    (brstComplex L).prj (weightCyclesToAbsolute L n x) = 0 := by
  apply (brstComplex L).prj_eq_zero.mpr
  obtain ⟨y, hy⟩ := hx
  exact ⟨y.val, congrArg Subtype.val hy⟩

theorem cosetToComplex_mem_weight (n : ℤ) (x : CosetSpace L)
    (hx : x ∈ (cosetVOA L).grading n) :
    cosetToComplex L x ∈ (brstSVA L).grading (n : ℂ) := by
  rw [cosetToComplex_apply]
  change (x.val ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
    TensorVA.tenGrading (matterSVA L) sl2GhostSVA (n : ℂ)
  apply TensorVA.tmul_mem_tenGrading (matterSVA L) sl2GhostSVA (h₁ := (n : ℂ))
  · change x.val ⊗ₜ[ℂ] (USVA L).vacuum ∈ TensorVA.tenGrading (abSVA L) (USVA L) (n : ℂ)
    apply TensorVA.tmul_mem_tenGrading (abSVA L) (USVA L) (h₁ := (n : ℂ))
    · exact hx
    · simpa only [sub_self] using (USVA L).vacuum_mem
  · simpa only [sub_self] using sl2GhostSVA.vacuum_mem

/-! ### Universal weight spaces and their simple projections -/

abbrev UniversalWeight (n : ℤ) := (virasoroVOA L.c).grading n

abbrev TargetWeight (n : ℤ) := (virasoroSimple L.c).grading n

def universalPrefix (p : ℕ) (n : ℤ) : Submodule ℂ (UniversalWeight L n) :=
  (virFil L.c p n).comap (UniversalWeight L n).subtype

def simpleWeightProjection (n : ℤ) : UniversalWeight L n →ₗ[ℂ] TargetWeight L n :=
  ((maxIdealVir L.c).mkQ.comp (UniversalWeight L n).subtype).codRestrict _
    (fun x => show (maxIdealVir L.c).mkQ (x : VirUniv L.c) ∈
      ((virasoroVOA L.c).grading n).map (maxIdealVir L.c).mkQ from
        Submodule.mem_map.mpr ⟨(x : VirUniv L.c), x.2, rfl⟩)

theorem simpleWeightProjection_surjective (n : ℤ) :
    Function.Surjective (simpleWeightProjection L n) := by
  intro y
  have hy : (y : VirUniv L.c ⧸ maxIdealVir L.c) ∈
      ((virasoroVOA L.c).grading n).map (maxIdealVir L.c).mkQ := y.2
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem simpleWeightProjection_prefix (p : ℕ) (n : ℤ) :
    (universalPrefix L p n).map (simpleWeightProjection L n) =
      (virGradedFlag L.c).pieceIn p n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨⟨x, virFil_le_grading L.c p n hx⟩, hx, ?_⟩
    exact Subtype.ext hxy

theorem universalPrefix_exhaustive (n : ℤ) (x : UniversalWeight L n) :
    ∃ p, x ∈ universalPrefix L p n := by
  have hx : (x : VirUniv L.c) ∈ gradingVir L.c n := x.2
  rw [← iSup_virFil L.c n] at hx
  obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed (fun p => virFil L.c p n)
    (fun p q => ⟨max p q, virFil_mono L.c n (le_max_left p q),
      virFil_mono L.c n (le_max_right p q)⟩)).mp hx
  exact ⟨p, hp⟩

/-! ### Universal classes in the finite relative complexes -/

def universalWeightRepresentative (n : ℤ) : UniversalWeight L n →ₗ[ℂ] relativeWeight L n :=
  (((cosetToComplex L).comp (virasoroToCoset L)).comp (UniversalWeight L n).subtype).codRestrict
    _ (fun x => ⟨cosetToComplex_relative L _,
      cosetToComplex_mem_weight L n _ (conformalEval_grading (cosetVOA L) rfl x.2)⟩)

theorem universalWeightRepresentative_closed (n : ℤ) (x : UniversalWeight L n) :
    relativeDifferential L n (universalWeightRepresentative L n x) = 0 := by
  apply Subtype.ext
  exact cosetToComplex_closed L _

def universalWeightCycles (n : ℤ) :
    UniversalWeight L n →ₗ[ℂ] LinearMap.ker (relativeDifferential L n) :=
  (universalWeightRepresentative L n).codRestrict (LinearMap.ker (relativeDifferential L n))
    (universalWeightRepresentative_closed L n)

/-- Relative exactness kills the simple projection of the universal state. -/
theorem universalWeightCycles_exact_zero (n : ℤ) (x : UniversalWeight L n)
    (hb : universalWeightCycles L n x ∈
      boundariesInCycles (K := relativeWeight L n) (relativeDifferential L n)) :
    simpleWeightProjection L n x = 0 := by
  have ha := weightBoundary_toAbsolute L n (universalWeightCycles L n x) hb
  have hz : virasoroToH0 L x = 0 := Subtype.ext ha
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero (maxIdealVir L.c)).mpr
    (virasoroToH0_ker_le_maxIdeal L hz)

end

end VOA.TwoSeries
