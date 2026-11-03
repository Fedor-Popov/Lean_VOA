import VOA.Classification.COne.OrbIcoVUniformProbe

/-! The actual uniform C2 probe kills the entire first-row singular
submodule. Equal proved kernel dimensions then make it descend to the
actual local Fock image. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma VOA.VirasoroScreening HeisenbergN Filter Topology
open scoped Classical

theorem uniformProbe_descendant (c h : ℂ) (v : Verma c h) (w : List ℕ) :
    uniformProbe c h (vermaDescendant c h w v) = wordProbe w * uniformProbe c h v := by
  induction w with
  | nil => simp [wordProbe, vermaDescendant]
  | cons i w ih =>
    change uniformProbe c h (vermaMode c h (-(i:ℤ)-1) _) = _
    rw [uniformProbe_creation, ih]
    change _ = ((if i=1 then (1/2:ℂ) else 0)*wordProbe w)*uniformProbe c h v
    ring

theorem uniformProbe_singularMap_zero (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n)
    (h₁ : vermaMode c h 1 v=0) (h₂ : vermaMode c h 2 v=0)
    (hz : uniformProbe c h v=0) :
    (uniformProbe c h).comp (vermaSingularMap c h n v hv h₁ h₂) = 0 := by
  apply (vermaSortedBasis c (h+(n:ℂ))).ext
  intro w
  rw [LinearMap.comp_apply, vermaSortedBasis_apply, vermaSingularMap,
    verma_universalMap_word, LinearMap.zero_apply, uniformProbe_descendant, hz, mul_zero]

def familyBSASeed (s : ℂ) : Verma (familyCharge s) (familyWeight s) :=
  vermaBSASource (familyCharge s) (familyWeight s) (s^2) 13 13

theorem familyBSASeed_level (s : ℂ) : familyBSASeed s ∈ sortedSpan _ _ 13 :=
  vermaBSASource_mem_level _ _ _ _ _

theorem familyBSASeed_ne_zero (s : ℂ) (hs : s ≠ 0) : familyBSASeed s ≠ 0 :=
  vermaBSASource_ne_zero _ _ _ _ (pow_ne_zero _ hs) (by norm_num)

theorem familyBSASeed_positive (s : ℂ) (hs : s ≠ 0) :
    vermaMode _ _ 1 (familyBSASeed s)=0 ∧ vermaMode _ _ 2 (familyBSASeed s)=0 := by
  unfold familyBSASeed familyCharge familyWeight
  rw [family_charge s hs, family_weight s hs]
  exact vermaBSASource_one_two_all (s^2) 13 (pow_ne_zero _ hs) (by norm_num)

def familySingularMap (s : ℂ) (hs : s ≠ 0) :
    Verma (familyCharge s) (familyWeight s+13) →ₗ[ℂ]
      Verma (familyCharge s) (familyWeight s) :=
  vermaSingularMap _ _ 13 (familyBSASeed s) (familyBSASeed_level s)
    (familyBSASeed_positive s hs).1 (familyBSASeed_positive s hs).2

def familySingularLevel (s : ℂ) (hs : s ≠ 0) (m : ℕ) :
    Submodule ℂ (Verma (familyCharge s) (familyWeight s)) :=
  (sortedSpan (familyCharge s) (familyWeight s+13) m).map (familySingularMap s hs)

theorem familySingularLevel_finrank (s : ℂ) (hs : s ≠ 0) (m : ℕ) :
    Module.finrank ℂ (familySingularLevel s hs m) = Fintype.card (VermaPartitions m) :=
  vermaSingularMap_level_finrank _ _ 13 m _ (familyBSASeed_level s)
    (familyBSASeed_ne_zero s hs) (familyBSASeed_positive s hs).1 (familyBSASeed_positive s hs).2

theorem familySingularLevel_le_kernel (s : ℂ) (hs : s ≠ 0) (m : ℕ) :
    familySingularLevel s hs m ≤ sortedSpan (familyCharge s) (familyWeight s) (13+m) ⊓
      LinearMap.ker (familyMap s) := by
  rintro x ⟨u,hu,rfl⟩
  refine ⟨(vermaSingularMap_mem_level_iff _ _ 13 m _ (familyBSASeed_level s)
    (familyBSASeed_ne_zero s hs) (familyBSASeed_positive s hs).1
    (familyBSASeed_positive s hs).2 u).mpr hu, ?_⟩
  exact LinearMap.congr_fun (chargedFockMap_singularMap_zero (familyBackground s)
    (familyMomentum s) 13 (familyBSASeed s) (familyBSASeed_level s)
    (familyBSASeed_positive s hs).1 (familyBSASeed_positive s hs).2
    (family_fock_s13_zero s hs)) u

theorem familySingularLevel_probe_zero (s : ℂ) (hs : s ≠ 0) (m : ℕ)
    (v : Verma (familyCharge s) (familyWeight s))
    (hv : v ∈ familySingularLevel s hs m) : uniformProbe _ _ v=0 := by
  obtain ⟨u,hu,rfl⟩ := hv
  exact LinearMap.congr_fun (uniformProbe_singularMap_zero _ _ 13 (familyBSASeed s)
    (familyBSASeed_level s) (familyBSASeed_positive s hs).1 (familyBSASeed_positive s hs).2
    (uniformProbe_s13_zero _ _ _)) u

theorem chargedFockLevel_kernel_finrank (ell p : ℂ) (N : ℕ) :
    Module.finrank ℂ ((sortedSpan (1-24*ell^2) (p^2-2*ell*p) N ⊓
      LinearMap.ker (chargedFockMap ell p)) : Submodule ℂ (Verma (1-24*ell^2) (p^2-2*ell*p))) =
      Module.finrank ℂ (LinearMap.ker (chargedFockLevelMap ell p N)) := by
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  unfold chargedFockLevelMap
  rw [LinearMap.ker_codRestrict, LinearMap.ker_comp]

theorem family_uniformProbe_kills_kernel_near (m : ℕ) :
    ∀ᶠ s : NonzeroParameter in 𝓝 parameterOne,
      ∀ v : Verma (familyCharge s.val) (familyWeight s.val),
        v ∈ sortedSpan _ _ (13+m) → familyMap s.val v=0 → uniformProbe _ _ v=0 := by
  obtain ⟨a,ha⟩ := exists_local_first_row_basis m
  filter_upwards [ha] with s hs
  have hF : Module.finrank ℂ (LinearMap.range (chargedFockLevelMap
      (familyBackground s.val) (familyMomentum s.val) (13+m))) = firstRowBasisSize m := by
    rw [← familyCoordinateImage_finrank, ← hs.2, finrank_span_eq_card hs.1]
    simp
  let K := sortedSpan (familyCharge s.val) (familyWeight s.val) (13+m) ⊓
    LinearMap.ker (familyMap s.val)
  have hK : Module.finrank ℂ K = Fintype.card (VermaPartitions m) := by
    have hn := (chargedFockLevelMap (familyBackground s.val) (familyMomentum s.val)
      (13+m)).finrank_range_add_finrank_ker
    rw [vermaLevel_finrank, hF, ← chargedFockLevel_kernel_finrank] at hn
    have hc := firstRowBasisSize_partition m
    change firstRowBasisSize m + Module.finrank ℂ K = _ at hn
    omega
  have hEq : familySingularLevel s.val s.property m = K :=
    Submodule.eq_of_le_of_finrank_eq (familySingularLevel_le_kernel s.val s.property m)
      ((familySingularLevel_finrank s.val s.property m).trans hK.symm)
  intro v hv hz
  apply familySingularLevel_probe_zero s.val s.property m v
  rw [hEq]
  exact ⟨hv,hz⟩

end VOA.Classification.COne.OrbIcoV
