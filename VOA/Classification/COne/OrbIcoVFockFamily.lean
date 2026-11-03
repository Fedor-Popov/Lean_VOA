import VOA.Classification.COne.OrbIcoVFockKernel
import VOA.Classification.COne.OrbIcoVFockRank

/-! Actual all-parameter Fock image bounds for the two symbol channels. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.VirasoroScreening
  InverseDS.LeeYangFockVirasoro InverseDS.VirasoroVerma VirModule

/-- The self-channel Fock family has the first-row partition bound at
all nonzero parameters; no genericity or determinant hypothesis enters. -/
theorem family_fock_image_bound (s : ℂ) (hs : s ≠ 0) (m : ℕ) :
    Module.finrank ℂ (LinearMap.range
      (chargedFockLevelMap (familyBackground s) (familyMomentum s) (13+m))) +
      Fintype.card (VermaPartitions m) ≤ Fintype.card (VermaPartitions (13+m)) := by
  have hpos : vermaMode (familyCharge s) (familyWeight s) 1
      (vermaBSASource (familyCharge s) (familyWeight s) (s^2) 13 13) = 0 ∧
      vermaMode (familyCharge s) (familyWeight s) 2
      (vermaBSASource (familyCharge s) (familyWeight s) (s^2) 13 13) = 0 := by
    unfold familyCharge familyWeight
    rw [family_charge s hs, family_weight s hs]
    exact vermaBSASource_one_two_all (s^2) 13 (pow_ne_zero _ hs) (by norm_num)
  exact chargedFockLevel_image_bound (familyBackground s) (familyMomentum s) 13 m
    (vermaBSASource (familyCharge s) (familyWeight s) (s^2) 13 13)
    (vermaBSASource_mem_level _ _ _ _ _) (vermaBSASource_ne_zero _ _ _ _
      (pow_ne_zero _ hs) (by norm_num)) hpos.1 hpos.2 (family_fock_s13_zero s hs)

/-- The translation singular vector is killed in every background Fock
vacuum, by the actual negative-mode formula. -/
theorem vacuum_fock_translation_zero (ell : ℂ) :
    chargedFockMap ell 0 (vermaMode _ _ (-1) (highestVector _ _)) = 0 := by
  rw [chargedFockMap_mode, chargedFockMap, universalMap_highestVector]
  simpa [vacuumN] using sector_negative_vacuum ell 0 1 (by norm_num)

/-- The vacuum Fock family has the vacuum partition bound at every
background parameter. -/
theorem vacuum_fock_image_bound (ell : ℂ) (m : ℕ) :
    Module.finrank ℂ (LinearMap.range (chargedFockLevelMap ell 0 (1+m))) +
      Fintype.card (VermaPartitions m) ≤ Fintype.card (VermaPartitions (1+m)) := by
  let c := 1-24*ell^2
  let h : ℂ := (0:ℂ)^2-2*ell*0
  let v : Verma c h := vermaMode c h (-1) (highestVector c h)
  have hlev : v ∈ sortedSpan c h 1 := by
    simpa [v, vermaBSASource] using vermaBSASource_mem_level c h (1:ℂ) 1 1
  have hne : v ≠ 0 := by
    simpa [v, vermaBSASource] using vermaBSASource_ne_zero c h (1:ℂ) 1 one_ne_zero
      (by norm_num)
  have haux (a : ℂ) (ha : a=0) :
      vermaMode c a 1 (vermaMode c a (-1) (highestVector c a)) = 0 ∧
      vermaMode c a 2 (vermaMode c a (-1) (highestVector c a)) = 0 := by
    subst a
    exact ⟨(translation_highest c).pos_annihilate 1 (by norm_num),
      (translation_highest c).pos_annihilate 2 (by norm_num)⟩
  have hpos : vermaMode c h 1 v=0 ∧ vermaMode c h 2 v=0 :=
    haux h (by dsimp [h]; ring)
  exact chargedFockLevel_image_bound ell 0 1 m v hlev hne hpos.1 hpos.2
    (vacuum_fock_translation_zero ell)

end VOA.Classification.COne.OrbIcoV
