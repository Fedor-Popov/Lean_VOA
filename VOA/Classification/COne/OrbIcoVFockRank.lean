import VOA.Examples.VirasoroFockGramTransfer

/-! A killed nonzero singular vector supplies an actual bound for the
image dimension of every charged Fock level. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA.VirasoroScreening VOA.InverseDS.VirasoroVerma
open scoped Classical

def fockSingularLevelMap (ell p : ℂ) (n m : ℕ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p))
    (hv : v ∈ sortedSpan _ _ n) (hne : v ≠ 0)
    (h1 : vermaMode _ _ 1 v=0) (h2 : vermaMode _ _ 2 v=0) :
    sortedSpan (1-24*ell^2) ((p^2-2*ell*p)+(n:ℂ)) m →ₗ[ℂ]
      sortedSpan (1-24*ell^2) (p^2-2*ell*p) (n+m) :=
  ((vermaSingularMap _ _ n v hv h1 h2).comp (sortedSpan _ _ m).subtype).codRestrict _
    (fun u => (vermaSingularMap_mem_level_iff _ _ n m v hv hne h1 h2 u).mpr u.property)

theorem fockSingularLevelMap_injective (ell p : ℂ) (n m : ℕ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p))
    (hv : v ∈ sortedSpan _ _ n) (hne : v ≠ 0)
    (h1 : vermaMode _ _ 1 v=0) (h2 : vermaMode _ _ 2 v=0) :
    Function.Injective (fockSingularLevelMap ell p n m v hv hne h1 h2) := by
  intro x y h
  apply Subtype.ext
  exact vermaSingularMap_injective _ _ n v hv hne h1 h2 (congrArg Subtype.val h)

theorem chargedFockMap_descendant_zero (ell p : ℂ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p))
    (hz : chargedFockMap ell p v = 0) (w : List ℕ) :
    chargedFockMap ell p (vermaDescendant _ _ w v) = 0 := by
  induction w with
  | nil => exact hz
  | cons i w ih =>
    change chargedFockMap ell p (vermaMode _ _ (-(i:ℤ)-1) _) = 0
    rw [chargedFockMap_mode, ih, map_zero]

theorem chargedFockMap_singularMap_zero (ell p : ℂ) (n : ℕ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p))
    (hv : v ∈ sortedSpan _ _ n)
    (h1 : vermaMode _ _ 1 v=0) (h2 : vermaMode _ _ 2 v=0)
    (hz : chargedFockMap ell p v=0) :
    (chargedFockMap ell p).comp (vermaSingularMap _ _ n v hv h1 h2) = 0 := by
  apply (vermaSortedBasis _ _).ext
  intro w
  rw [LinearMap.comp_apply, vermaSortedBasis_apply, vermaSingularMap,
    verma_universalMap_word, LinearMap.zero_apply]
  exact chargedFockMap_descendant_zero ell p v hz w.val

theorem chargedFockLevel_image_bound (ell p : ℂ) (n m : ℕ)
    (v : Verma (1-24*ell^2) (p^2-2*ell*p))
    (hv : v ∈ sortedSpan _ _ n) (hne : v ≠ 0)
    (h1 : vermaMode _ _ 1 v=0) (h2 : vermaMode _ _ 2 v=0)
    (hz : chargedFockMap ell p v=0) :
    Module.finrank ℂ (LinearMap.range (chargedFockLevelMap ell p (n+m))) +
      Fintype.card (VermaPartitions m) ≤ Fintype.card (VermaPartitions (n+m)) := by
  let S := fockSingularLevelMap ell p n m v hv hne h1 h2
  let F := chargedFockLevelMap ell p (n+m)
  letI := (vermaLevelBasis (1-24*ell^2) (p^2-2*ell*p) (n+m)).finiteDimensional_of_finite
  letI := (vermaLevelBasis (1-24*ell^2) ((p^2-2*ell*p)+(n:ℂ)) m).finiteDimensional_of_finite
  have hi := fockSingularLevelMap_injective ell p n m v hv hne h1 h2
  have hS : Module.finrank ℂ (LinearMap.range S) = Fintype.card (VermaPartitions m) := by
    rw [LinearMap.finrank_range_of_inj hi]
    exact vermaLevel_finrank _ _ _
  have hle : LinearMap.range S ≤ LinearMap.ker F := by
    rintro x ⟨u,rfl⟩
    apply Subtype.ext
    change chargedFockMap ell p (vermaSingularMap _ _ n v hv h1 h2 u) = 0
    exact LinearMap.congr_fun (chargedFockMap_singularMap_zero ell p n v hv h1 h2 hz) u
  have hker := Submodule.finrank_mono hle
  have hrank := F.finrank_range_add_finrank_ker
  rw [hS] at hker
  rw [vermaLevel_finrank _ _ _] at hrank
  change Module.finrank ℂ (LinearMap.range F) + _ ≤ _
  omega


end VOA.Classification.COne.OrbIcoV
