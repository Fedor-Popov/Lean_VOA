import VOA.Moonshine.MoonshineCNSectorVirasoroComparison
import VOA.Moonshine.MoonshineCNMonsterGrading
import VOA.Moonshine.MoonshineCNVnatNoGhost
import VOA.Moonshine.MoonshineCNVnatZeroQuotient

/-! Physical and global-spurious transfer through the actual momentum projections. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster
open scoped TensorProduct

def moonshineMatterSectorRetract (x y : ℤ) :
    moonshineMatterSpace →ₗ[ℂ] (Vnat ⊗[ℂ] hypFock) :=
  (moonshineMatterSectorInverse ![x, y]).comp (matterMomentumComponent ![x, y])

theorem moonshineMatterSectorRetract_map (x y : ℤ) (u : moonshineMatterSpace) :
    moonshineMatterSectorMap ![x, y] (moonshineMatterSectorRetract x y u) =
      matterMomentumComponent ![x, y] u :=
  moonshineMatterSector_rightInverse _ _ (matterMomentumComponent_mem _ _)

theorem moonshineMatterSectorRetract_leftInverse (x y : ℤ) (u : Vnat ⊗[ℂ] hypFock) :
    moonshineMatterSectorRetract x y (moonshineMatterSectorMap ![x, y] u) = u := by
  change moonshineMatterSectorInverse ![x, y]
    (matterMomentumComponent ![x, y] (moonshineMatterSectorMap ![x, y] u)) = u
  rw [matterMomentumComponent_of_mem _ _ (moonshineMatterSectorMap_mem _ _),
    moonshineMatterSector_leftInverse]

theorem moonshineMatterSectorRetract_virasoro (x y n : ℤ) (u : moonshineMatterSpace) :
    moonshineMatterSectorRetract x y (moonshineMatterNearVOA.L n u) =
      vnatHypMode x y n (moonshineMatterSectorRetract x y u) := by
  apply moonshineMatterSectorMap_injective ![x, y]
  rw [moonshineMatterSectorMap_virasoro, moonshineMatterSectorRetract_map,
    moonshineMatterSectorRetract_map, matterMomentumComponent_virasoro]

theorem moonshineMatterSectorMap_spurious (x y : ℤ) (a : Fin 2)
    (u : Vnat ⊗[ℂ] hypFock) (hu : u ∈ (vnatStringModule x y a).spurious) :
    moonshineMatterSectorMap ![x, y] u ∈ moonshineMatterNearVOA.spurious := by
  refine Submodule.iSup_induction
    (fun n : ℕ => LinearMap.range (vnatHypMode x y (-(n + 1 : ℤ))))
    (motive := fun u => moonshineMatterSectorMap ![x, y] u ∈ moonshineMatterNearVOA.spurious)
    hu ?_ ?_ ?_
  · intro n v hv
    obtain ⟨w, rfl⟩ := hv
    rw [moonshineMatterSectorMap_virasoro]
    exact moonshineMatterNearVOA.negativeVirasoro_mem_spurious n _
  · change moonshineMatterSectorMap ![x, y] 0 ∈ _
    rw [LinearMap.map_zero]; exact Submodule.zero_mem _
  · intro u v hu hv
    rw [LinearMap.map_add]; exact Submodule.add_mem _ hu hv

theorem moonshineMatterSectorRetract_spurious (x y : ℤ) (a : Fin 2)
    (u : moonshineMatterSpace) (hu : u ∈ moonshineMatterNearVOA.spurious) :
    moonshineMatterSectorRetract x y u ∈ (vnatStringModule x y a).spurious := by
  refine Submodule.iSup_induction
    (fun n : ℕ => LinearMap.range (moonshineMatterNearVOA.L (-(n + 1 : ℤ))))
    (motive := fun u => moonshineMatterSectorRetract x y u ∈ (vnatStringModule x y a).spurious)
    hu ?_ ?_ ?_
  · intro n v hv
    obtain ⟨w, rfl⟩ := hv
    rw [moonshineMatterSectorRetract_virasoro]
    exact (vnatStringModule x y a).negative_L_mem_spurious n _
  · change moonshineMatterSectorRetract x y 0 ∈ _
    rw [LinearMap.map_zero]; exact Submodule.zero_mem _
  · intro u v hu hv
    rw [LinearMap.map_add]; exact Submodule.add_mem _ hu hv

/-- Global negative descendants intersect a momentum sector in precisely its own descendants. -/
theorem moonshineMatterSector_spurious_iff (x y : ℤ) (a : Fin 2)
    (u : Vnat ⊗[ℂ] hypFock) :
    moonshineMatterSectorMap ![x, y] u ∈ moonshineMatterNearVOA.spurious ↔
      u ∈ (vnatStringModule x y a).spurious := by
  constructor
  · intro hu
    have h := moonshineMatterSectorRetract_spurious x y a _ hu
    rwa [moonshineMatterSectorRetract_leftInverse] at h
  · exact moonshineMatterSectorMap_spurious x y a u

theorem moonshineMatterSector_primary_iff (x y : ℤ) (a : Fin 2)
    (u : Vnat ⊗[ℂ] hypFock) :
    moonshineMatterSectorMap ![x, y] u ∈ moonshineMatterNearVOA.primaryWeightOne ↔
      u ∈ vnatSectorWeight x y 1 ∧ u ∈ (vnatStringModule x y a).physical := by
  constructor
  · rintro ⟨hw, hp⟩
    constructor
    · rw [vnatSectorWeight_eq_eigenspace, Module.End.mem_eigenspace_iff,
        Int.cast_one, one_smul]
      apply moonshineMatterSectorMap_injective ![x, y]
      rw [moonshineMatterSectorMap_virasoro]
      exact hw
    · apply (vnatStringModule x y a).mem_physical_iff u |>.mpr
      intro n
      change vnatHypMode x y (n + 1 : ℤ) u = 0
      apply moonshineMatterSectorMap_injective ![x, y]
      rw [moonshineMatterSectorMap_virasoro, LinearMap.map_zero]
      exact hp (n + 1) (by omega)
  · rintro ⟨hw, hp⟩
    constructor
    · rw [← moonshineMatterSectorMap_virasoro, vnatSectorWeight_energy x y 1 u hw,
        Int.cast_one, one_smul]
    · intro n hn
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
      rw [← moonshineMatterSectorMap_virasoro]
      have hz := ((vnatStringModule x y a).mem_physical_iff u).mp hp j
      change vnatHypMode x y (j + 1 : ℤ) u = 0 at hz
      rw [hz, LinearMap.map_zero]

theorem vnatPhysicalRadical_mem_iff (x y : ℤ) (a : Fin 2)
    (u : (vnatStringModule x y a).weightSlice (vnatStringModule x y a).physical 1) :
    u ∈ (vnatStringModule x y a).weightRadical (vnatStringModule x y a).physical 1 ↔
      (u.val.val : Vnat ⊗[ℂ] hypFock) ∈ (vnatStringModule x y a).spurious := by
  change u.val ∈ (vnatStringModule x y a).formRadicalIn
    (vnatStringModule x y a).physical 1 ↔ _
  rw [(vnatStringModule x y a).physicalOne_radical_eq]
  change (u.val.val ∈ (vnatStringModule x y a).physical ∧
    u.val.val ∈ (vnatStringModule x y a).spurious) ↔ _
  exact and_iff_right u.property

end VOA.Moonshine.ConwayNorton
