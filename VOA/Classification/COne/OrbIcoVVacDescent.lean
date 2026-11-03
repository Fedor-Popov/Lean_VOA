import VOA.Classification.COne.OrbIcoVVacKernel

/-! The universal C2 scalar functional descends to the genuine vacuum
Fock family near c=1, because the proved translation kernel exhausts it. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma VOA.VirasoroScreening HeisenbergN Filter Topology
  VirModule
open scoped Classical

def vacTranslationSeed (s : ℂ) : Verma (familyCharge s) (vacFamilyWeight s) :=
  vermaBSASource (familyCharge s) (vacFamilyWeight s) (s^2) 1 1

theorem vacTranslationSeed_level (s : ℂ) : vacTranslationSeed s ∈ sortedSpan _ _ 1 :=
  vermaBSASource_mem_level _ _ _ _ _

theorem vacTranslationSeed_ne_zero (s : ℂ) (hs : s ≠ 0) : vacTranslationSeed s ≠ 0 :=
  vermaBSASource_ne_zero _ _ _ _ (pow_ne_zero _ hs) (by norm_num)

theorem vacTranslationSeed_positive (s : ℂ) (hs : s ≠ 0) :
    vermaMode _ _ 1 (vacTranslationSeed s)=0 ∧
      vermaMode _ _ 2 (vacTranslationSeed s)=0 := by
  have transfer (c h : ℂ) (hh : h=0) (t : ℂ) :
      vermaMode c h 1 (vermaBSASource c h t 1 1)=0 ∧
        vermaMode c h 2 (vermaBSASource c h t 1 1)=0 := by
    subst h
    simpa only [vermaBSASource,Fin.sum_univ_one,Fin.val_zero,Nat.cast_zero,
      Nat.cast_one,zero_sub,vermaBSAState_zero] using
      (show vermaMode c 0 1 (vermaMode c 0 (-1) (highestVector c 0))=0 ∧
        vermaMode c 0 2 (vermaMode c 0 (-1) (highestVector c 0))=0 from
        ⟨(translation_highest c).pos_annihilate 1 (by norm_num),
         (translation_highest c).pos_annihilate 2 (by norm_num)⟩)
  exact transfer _ _ (by norm_num [vacFamilyWeight,vacFamilyMomentum]) _

theorem vac_fock_source_one_zero (s : ℂ) (hs : s ≠ 0) :
    vacFamilyMap s (vacTranslationSeed s)=0 := by
  simpa only [vacTranslationSeed,vermaBSASource,Fin.sum_univ_one,Fin.val_zero,
    Nat.cast_zero,Nat.cast_one,zero_sub,vermaBSAState_zero] using
    vacuum_fock_translation_zero (familyBackground s)

abbrev vacSingularMap (s : ℂ) (hs : s ≠ 0) :=
  vermaSingularMap _ _ 1 (vacTranslationSeed s) (vacTranslationSeed_level s)
    (vacTranslationSeed_positive s hs).1 (vacTranslationSeed_positive s hs).2

def vacSingularLevel (s : ℂ) (hs : s ≠ 0) (m : ℕ) :
    Submodule ℂ (Verma (familyCharge s) (vacFamilyWeight s)) :=
  (sortedSpan (familyCharge s) (vacFamilyWeight s+((1:ℕ):ℂ)) m).map (vacSingularMap s hs)

theorem vacSingularLevel_finrank (s : ℂ) (hs : s ≠ 0) (m : ℕ) :
    Module.finrank ℂ (vacSingularLevel s hs m) = Fintype.card (VermaPartitions m) :=
  vermaSingularMap_level_finrank _ _ 1 m _ (vacTranslationSeed_level s)
    (vacTranslationSeed_ne_zero s hs) (vacTranslationSeed_positive s hs).1 (vacTranslationSeed_positive s hs).2

theorem vacSingularLevel_le_kernel (s : ℂ) (hs : s ≠ 0) (m : ℕ) :
    vacSingularLevel s hs m ≤ sortedSpan (familyCharge s) (vacFamilyWeight s) (1+m) ⊓
      LinearMap.ker (vacFamilyMap s) := by
  rintro x ⟨u,hu,rfl⟩
  refine ⟨(vermaSingularMap_mem_level_iff _ _ 1 m _ (vacTranslationSeed_level s)
    (vacTranslationSeed_ne_zero s hs) (vacTranslationSeed_positive s hs).1
    (vacTranslationSeed_positive s hs).2 u).mpr hu, ?_⟩
  exact LinearMap.congr_fun (chargedFockMap_singularMap_zero (familyBackground s)
    (vacFamilyMomentum s) 1 (vacTranslationSeed s) (vacTranslationSeed_level s)
    (vacTranslationSeed_positive s hs).1 (vacTranslationSeed_positive s hs).2
    (vac_fock_source_one_zero s hs)) u

theorem vacSingularLevel_probe_zero (s : ℂ) (hs : s ≠ 0) (m : ℕ)
    (v : Verma (familyCharge s) (vacFamilyWeight s))
    (hv : v ∈ vacSingularLevel s hs m) : uniformProbe _ _ v=0 := by
  obtain ⟨u,hu,rfl⟩ := hv
  exact LinearMap.congr_fun (uniformProbe_singularMap_zero _ _ 1 (vacTranslationSeed s)
    (vacTranslationSeed_level s) (vacTranslationSeed_positive s hs).1 (vacTranslationSeed_positive s hs).2
    (uniformProbe_odd_level _ _ 1 (by norm_num) _ (vermaBSASource_mem_level _ _ _ _ _))) u

theorem vac_uniformProbe_kills_kernel_near (m : ℕ) :
    ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
      ∀ v : Verma (familyCharge s.val) (vacFamilyWeight s.val),
        v ∈ sortedSpan _ _ (1+m) → vacFamilyMap s.val v=0 → uniformProbe _ _ v=0 := by
  obtain ⟨a,ha⟩ := exists_local_vac_first_row_basis m
  filter_upwards [ha] with s hs
  have hF : Module.finrank ℂ (LinearMap.range (chargedFockLevelMap
      (familyBackground s.val) (vacFamilyMomentum s.val) (1+m))) = vacFirstRowBasisSize m := by
    rw [← vacCoordinateImage_finrank, ← hs.2, finrank_span_eq_card hs.1]
    simp
  let K := sortedSpan (familyCharge s.val) (vacFamilyWeight s.val) (1+m) ⊓
    LinearMap.ker (vacFamilyMap s.val)
  have hK : Module.finrank ℂ K = Fintype.card (VermaPartitions m) := by
    have hn := (chargedFockLevelMap (familyBackground s.val) (vacFamilyMomentum s.val)
      (1+m)).finrank_range_add_finrank_ker
    rw [vermaLevel_finrank, hF, ← chargedFockLevel_kernel_finrank] at hn
    have hc := vacFirstRowBasisSize_partition m
    change vacFirstRowBasisSize m + Module.finrank ℂ K = _ at hn
    omega
  have hEq : vacSingularLevel s.val s.property m = K :=
    Submodule.eq_of_le_of_finrank_eq (vacSingularLevel_le_kernel s.val s.property m)
      ((vacSingularLevel_finrank s.val s.property m).trans hK.symm)
  intro v hv hz
  apply vacSingularLevel_probe_zero s.val s.property m v
  rw [hEq]
  exact ⟨hv,hz⟩


end VOA.Classification.COne.OrbIcoV
