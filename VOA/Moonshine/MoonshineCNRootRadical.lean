import VOA.Moonshine.MoonshineCNRootSpaces

/-! The physical radical in each actual momentum sector, including the zero sector. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster Nondeg
open scoped TensorProduct

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup
attribute [local instance] monsterPhysicalAddCommGroup

/-- The physical spurious intersection is precisely the radical of the reversed sector form. -/
theorem moonshineMatterSector_physical_radical (x y : ℤ) (u : moonshineMatterSpace)
    (hup : u ∈ moonshineMatterNearVOA.primaryWeightOne)
    (hum : u ∈ moonshineMatterMomentum ![x, y]) :
    u ∈ moonshineMatterNearVOA.spurious ↔
      ∀ v : moonshineMatterSpace, v ∈ moonshineMatterNearVOA.primaryWeightOne →
        v ∈ moonshineMatterMomentum ![x, y] →
          moonshineMatterForm (moonshineMatterReversal u) v = 0 := by
  obtain ⟨p, hp⟩ := (moonshineMatterSectorEquiv ![x, y]).surjective ⟨u, hum⟩
  have hpv : moonshineMatterSectorMap ![x, y] p = u := congrArg Subtype.val hp
  have hphys := (moonshineMatterSector_primary_iff x y 0 p).mp (hpv.symm ▸ hup)
  let pu : (vnatStringModule x y 0).weightSlice (vnatStringModule x y 0).physical 1 :=
    ⟨⟨p, hphys.1⟩, hphys.2⟩
  rw [← hpv, moonshineMatterSector_spurious_iff x y 0]
  constructor
  · intro hs v hv hm
    obtain ⟨q, hq⟩ := (moonshineMatterSectorEquiv ![x, y]).surjective ⟨v, hm⟩
    have hqv : moonshineMatterSectorMap ![x, y] q = v := congrArg Subtype.val hq
    have hqphys := (moonshineMatterSector_primary_iff x y 0 q).mp (hqv.symm ▸ hv)
    let qv : (vnatStringModule x y 0).weightSlice (vnatStringModule x y 0).physical 1 :=
      ⟨⟨q, hqphys.1⟩, hqphys.2⟩
    have hrad := (vnatPhysicalRadical_mem_iff x y 0 pu).mpr hs
    have hz := ((vnatStringModule x y 0).mem_weightRadical_iff _ _ pu).mp hrad qv
    change vnatHypForm p q = 0 at hz
    rw [← hqv]
    change moonshineMatterForm (moonshineMatterReversal (moonshineMatterSectorEquiv ![x, y] p))
      (moonshineMatterSectorEquiv ![x, y] q) = 0
    rw [moonshineMatterSector_form, hz, mul_zero]
  · intro hr
    apply (vnatPhysicalRadical_mem_iff x y 0 pu).mp
    apply ((vnatStringModule x y 0).mem_weightRadical_iff _ _ pu).mpr
    intro q
    have hz := hr (moonshineMatterSectorMap ![x, y] q.val.val)
      ((moonshineMatterSector_primary_iff x y 0 q.val.val).mpr ⟨q.val.property, q.property⟩)
      (moonshineMatterSectorMap_mem _ _)
    change moonshineMatterForm (moonshineMatterReversal (moonshineMatterSectorEquiv ![x, y] p))
      (moonshineMatterSectorEquiv ![x, y] q.val.val) = 0 at hz
    rw [moonshineMatterSector_form] at hz
    exact (mul_eq_zero.mp hz).resolve_left (chSign_ne_zero _ _)

end VOA.Moonshine.ConwayNorton
