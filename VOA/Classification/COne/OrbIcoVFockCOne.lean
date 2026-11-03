import VOA.Classification.COne.OrbIcoVFockFamily
import VOA.Classification.COne.FeiginFuchsLower

/-! At the central-charge-one parameter the actual Fock cyclic image
saturates its proved uniform dimension bound. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN VOA.VirasoroScreening InverseDS.VirasoroVerma
open scoped Classical

theorem chargedFockLevel_kernel_le_radical (ell p : ℂ) (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (chargedFockLevelMap ell p N)) ≤
      Module.finrank ℂ (vermaRadicalLevel (1-24*ell^2) (p^2-2*ell*p) N) := by
  let F := chargedFockLevelMap ell p N
  let A := sortedSpan (1-24*ell^2) (p^2-2*ell*p) N
  let K := (LinearMap.ker F).map A.subtype
  have hK : K ≤ vermaRadicalLevel (1-24*ell^2) (p^2-2*ell*p) N := by
    rintro x ⟨u,hu,rfl⟩
    refine ⟨u.property, chargedFockMap_kernel_radical ell p u ?_⟩
    exact congrArg Subtype.val hu
  have hd : Module.finrank ℂ (LinearMap.ker F) = Module.finrank ℂ K :=
    (Submodule.equivMapOfInjective A.subtype A.subtype_injective (LinearMap.ker F)).finrank_eq
  rw [hd]
  exact Submodule.finrank_mono hK

theorem chargedFockLevel_image_lower (ell p : ℂ) (N defect : ℕ)
    (hR : Module.finrank ℂ (vermaRadicalLevel (1-24*ell^2) (p^2-2*ell*p) N) ≤ defect) :
    Fintype.card (VermaPartitions N) ≤
      Module.finrank ℂ (LinearMap.range (chargedFockLevelMap ell p N)) + defect := by
  letI := (vermaLevelBasis (1-24*ell^2) (p^2-2*ell*p) N).finiteDimensional_of_finite
  have hker := (chargedFockLevel_kernel_le_radical ell p N).trans hR
  have hrank := (chargedFockLevelMap ell p N).finrank_range_add_finrank_ker
  rw [vermaLevel_finrank] at hrank
  omega

theorem family_fock_image_dimension_one (m : ℕ) :
    Module.finrank ℂ (LinearMap.range
      (chargedFockLevelMap (familyBackground 1) (familyMomentum 1) (13+m))) +
      Fintype.card (VermaPartitions m) = Fintype.card (VermaPartitions (13+m)) := by
  apply Nat.le_antisymm (family_fock_image_bound 1 one_ne_zero m)
  apply chargedFockLevel_image_lower
  have hrad (c h : ℂ) (hc : c=1) (hh : h=36) :
      Module.finrank ℂ (vermaRadicalLevel c h (13+m)) ≤ Fintype.card (VermaPartitions m) := by
    subst c
    subst h
    convert FFLower.radical_bound 6 m using 1 <;> norm_num
  apply hrad
  · norm_num [familyBackground]
  · norm_num [familyBackground, familyMomentum]

end VOA.Classification.COne.OrbIcoV
