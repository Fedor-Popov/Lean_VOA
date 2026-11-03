import VOA.Examples.LeeYangShortcutVirasoro
import VOA.Examples.VirasoroGoodFiltration

/-! # A canonical simple quotient of the actual cohomological Virasoro image

The proper-kernel argument is made directly in the absolute BRST cohomology.
It uses the proved survival of the vacuum and requires neither coset simplicity
nor an external identification of the coset. Every PBW prefix of the image
surjects onto the corresponding prefix of the simple Virasoro quotient.
-/
namespace VOA.LeeYangShortcut

open VirModule VirSimple Sl2CosetConcrete VirGoodFil

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-- The actual universal Virasoro map into ghost-degree-zero cohomology. -/
def virasoroToH0 : VirUniv LeeYang.leeYangC →ₗ[ℂ] leeYangBRSTComplex.H0 :=
  leeYangCosetToH0.comp virasoroToCoset

/-- Regard the same map in the complete absolute cohomology. -/
def virasoroToCoh : VirUniv LeeYang.leeYangC →ₗ[ℂ] leeYangBRSTComplex.Coh :=
  leeYangBRSTComplex.H0.subtype.comp virasoroToH0

@[simp] theorem virasoroToCoh_vacuum :
    virasoroToCoh (vacVec LeeYang.leeYangC) = leeYangBRSTComplex.cohomology.vacuum := by
  change (leeYangCosetToH0 (virasoroToCoset _)).val = _
  rw [virasoroToCoset_vacuum]
  rfl

/-- The composed map intertwines the actual cohomology vertex products. -/
theorem virasoroToCoh_mode (x y : VirUniv LeeYang.leeYangC) (n : ℤ) :
    virasoroToCoh ((virasoroVOA LeeYang.leeYangC).smul x n y) =
      mode (leeYangBRSTComplex.cohomology.Y (virasoroToCoh x)) n (virasoroToCoh y) := by
  change (leeYangCosetToH0 (virasoroToCoset _)).val = _
  rw [virasoroToCoset_hom.map_smul]
  exact Sl2Coset.auxiliaryCosetToCohomology_mode diagonalAction uAction
    abParityCompatible uParityCompatible abuTensorGrading Sl2SemiInfinite.leeYangMatter_level
    matterGhostTensorGrading (virasoroToCoset x) (virasoroToCoset y) n

/-- In particular, the image of the vacuum is nonzero. -/
theorem virasoroToH0_vacuum_ne_zero : virasoroToH0 (vacVec LeeYang.leeYangC) ≠ 0 := by
  intro h
  apply leeYangBRSTComplex_cohomology_vacuum_ne_zero
  rw [← virasoroToCoh_vacuum]
  exact congrArg Subtype.val h

/-- All universal vertex modes preserve the kernel in actual cohomology. -/
theorem virasoroToH0_ker_isIdeal :
    (virasoroVOA LeeYang.leeYangC).IsIdeal (LinearMap.ker virasoroToH0) := by
  intro x y n hy
  rw [LinearMap.mem_ker] at hy ⊢
  apply Subtype.ext
  change virasoroToCoh ((virasoroVOA LeeYang.leeYangC).smul x n y) = 0
  rw [virasoroToCoh_mode]
  have hy' : virasoroToCoh y = 0 := congrArg Subtype.val hy
  rw [hy', map_zero]

/-- The proper image kernel lies below the unique maximal Virasoro ideal. -/
theorem virasoroToH0_ker_le_maxIdeal :
    LinearMap.ker virasoroToH0 ≤ maxIdealVir LeeYang.leeYangC :=
  le_maxIdealVir _ virasoroToH0_ker_isIdeal virasoroToH0_vacuum_ne_zero

/-- The concrete cohomological Virasoro image. -/
abbrev VirasoroImage := LinearMap.range virasoroToH0

/-- The image is nonzero before applying any dimension comparison. -/
theorem virasoroImage_ne_bot : LinearMap.range virasoroToH0 ≠ ⊥ := by
  intro h
  apply virasoroToH0_vacuum_ne_zero
  have hv := LinearMap.mem_range_self virasoroToH0 (vacVec LeeYang.leeYangC)
  rwa [h, Submodule.mem_bot] at hv

/-- For any proper universal kernel, its image has a canonical simple quotient. -/
def imageToSimple {E : Type*} [AddCommGroup E] [Module ℂ E] {c : ℂ}
    (f : VirUniv c →ₗ[ℂ] E) (hk : LinearMap.ker f ≤ maxIdealVir c) :
    LinearMap.range f →ₗ[ℂ] (VirUniv c ⧸ maxIdealVir c) :=
  ((LinearMap.ker f).liftQ (maxIdealVir c).mkQ
    (by simpa only [Submodule.ker_mkQ] using hk)).comp
      (LinearMap.quotKerEquivRange f).symm.toLinearMap

@[simp] theorem imageToSimple_rangeRestrict {E : Type*} [AddCommGroup E] [Module ℂ E]
    {c : ℂ} (f : VirUniv c →ₗ[ℂ] E) (hk : LinearMap.ker f ≤ maxIdealVir c)
    (x : VirUniv c) : imageToSimple f hk (f.rangeRestrict x) = (maxIdealVir c).mkQ x := by
  change (LinearMap.ker f).liftQ (maxIdealVir c).mkQ
    (by simpa only [Submodule.ker_mkQ] using hk)
    (f.quotKerEquivRange.symm ⟨f x, _⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- The canonical quotient of the image is onto, not merely a filtered map. -/
theorem imageToSimple_surjective {E : Type*} [AddCommGroup E] [Module ℂ E] {c : ℂ}
    (f : VirUniv c →ₗ[ℂ] E) (hk : LinearMap.ker f ≤ maxIdealVir c) :
    Function.Surjective (imageToSimple f hk) := by
  intro y
  obtain ⟨x, rfl⟩ := (maxIdealVir c).mkQ_surjective y
  exact ⟨f.rangeRestrict x, imageToSimple_rangeRestrict f hk x⟩

/-- Every PBW prefix is mapped onto exactly the simple PBW prefix. -/
theorem imageToSimple_prefix {E : Type*} [AddCommGroup E] [Module ℂ E] {c : ℂ}
    (f : VirUniv c →ₗ[ℂ] E) (hk : LinearMap.ker f ≤ maxIdealVir c)
    (p : ℕ) (n : ℤ) :
    ((virFil c p n).map f.rangeRestrict).map (imageToSimple f hk) =
      (virGradedFlag c).piece p n := by
  rw [← Submodule.map_comp]
  have hh : (imageToSimple f hk).comp f.rangeRestrict = (maxIdealVir c).mkQ := by
    ext x
    exact imageToSimple_rangeRestrict f hk x
  rw [hh]
  rfl

/-- The desired quotient of the concrete cohomological image. -/
def virasoroImageToSimple : VirasoroImage →ₗ[ℂ] LeeYangTransferAssembly.LeeYangSpace :=
  imageToSimple virasoroToH0 virasoroToH0_ker_le_maxIdeal

theorem virasoroImageToSimple_surjective : Function.Surjective virasoroImageToSimple :=
  imageToSimple_surjective virasoroToH0 virasoroToH0_ker_le_maxIdeal

/-- The actual map already has strict PBW-prefix compatibility in its own image filtration. -/
theorem virasoroImageToSimple_prefix (p : ℕ) (n : ℤ) :
    ((virFil LeeYang.leeYangC p n).map virasoroToH0.rangeRestrict).map
        virasoroImageToSimple = (virGradedFlag LeeYang.leeYangC).piece p n :=
  imageToSimple_prefix virasoroToH0 virasoroToH0_ker_le_maxIdeal p n

end
end VOA.LeeYangShortcut
