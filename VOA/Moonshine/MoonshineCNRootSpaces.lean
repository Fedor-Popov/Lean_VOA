import VOA.Moonshine.MoonshineCNSectorPhysicalTransfer
import Mathlib.LinearAlgebra.Isomorphisms

/-! Root spaces of the actual Monster Lie algebra, via the physical-spurious quotient. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open AutMonster
open scoped TensorProduct

attribute [local instance] vnatStringWeightAddCommGroup vnatStringSliceAddCommGroup
attribute [local instance] monsterPhysicalAddCommGroup

def moonshineMatterPhysicalSectorMap (x y : ℤ) (a : Fin 2) :
    (vnatStringModule x y a).weightSlice (vnatStringModule x y a).physical 1 →ₗ[ℂ]
      moonshineMatterNearVOA.primaryWeightOne where
  toFun u := ⟨moonshineMatterSectorMap ![x, y] u.val.val,
    (moonshineMatterSector_primary_iff x y a u.val.val).mpr ⟨u.val.property, u.property⟩⟩
  map_add' u v := Subtype.ext (LinearMap.map_add _ _ _)
  map_smul' c u := Subtype.ext (LinearMap.map_smul _ _ _)

def monsterLieSectorProjection (x y : ℤ) (a : Fin 2) :
    (vnatStringModule x y a).weightSlice (vnatStringModule x y a).physical 1 →ₗ[ℂ]
      monsterLieMomentum ![x, y] :=
  (monsterLieProjection.comp (moonshineMatterPhysicalSectorMap x y a)).codRestrict
    (monsterLieMomentum ![x, y]) fun u =>
      ⟨moonshineMatterPhysicalSectorMap x y a u, moonshineMatterSectorMap_mem _ _, rfl⟩

theorem monsterLieSectorProjection_surjective (x y : ℤ) (a : Fin 2) :
    Function.Surjective (monsterLieSectorProjection x y a) := by
  intro u
  obtain ⟨v, hv, he⟩ := u.property
  obtain ⟨p, hp⟩ := (moonshineMatterSectorEquiv ![x, y]).surjective ⟨v, hv⟩
  have hpv : moonshineMatterSectorMap ![x, y] p = (v : moonshineMatterSpace) :=
    congrArg Subtype.val hp
  have hphys := (moonshineMatterSector_primary_iff x y a p).mp (hpv.symm ▸ v.property)
  refine ⟨⟨⟨p, hphys.1⟩, hphys.2⟩, ?_⟩
  apply Subtype.ext
  change monsterLieProjection (moonshineMatterPhysicalSectorMap x y a _) = u.val
  rw [← he]
  congr 1
  exact Subtype.ext hpv

theorem monsterLieSectorProjection_ker (x y : ℤ) (a : Fin 2) :
    LinearMap.ker (monsterLieSectorProjection x y a) =
      (vnatStringModule x y a).weightRadical (vnatStringModule x y a).physical 1 := by
  ext u
  rw [LinearMap.mem_ker, vnatPhysicalRadical_mem_iff]
  change (⟨monsterLieProjection (moonshineMatterPhysicalSectorMap x y a u), _⟩ :
    monsterLieMomentum ![x, y]) = 0 ↔ _
  rw [Subtype.ext_iff]
  change (Submodule.Quotient.mk (moonshineMatterPhysicalSectorMap x y a u) :
    monsterLieAlgebra) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact moonshineMatterSector_spurious_iff x y a u.val.val

/-- The concrete no-ghost radical quotient is the actual momentum piece. -/
def monsterLieSectorQuotientEquiv (x y : ℤ) (a : Fin 2) :
    (vnatStringModule x y a).weightRadicalQuotient (vnatStringModule x y a).physical 1 ≃ₗ[ℂ]
      monsterLieMomentum ![x, y] :=
  (Submodule.quotEquivOfEq _ _ (monsterLieSectorProjection_ker x y a).symm).trans
    ((monsterLieSectorProjection x y a).quotKerEquivOfSurjective
      (monsterLieSectorProjection_surjective x y a))

theorem monsterLieSectorQuotientEquiv_mk (x y : ℤ) (a : Fin 2)
    (u : (vnatStringModule x y a).weightSlice (vnatStringModule x y a).physical 1) :
    monsterLieSectorQuotientEquiv x y a (Submodule.Quotient.mk u) =
      monsterLieSectorProjection x y a u := rfl

/-- Nonzero root spaces, with exactly the half-norm shift of the actual lattice. -/
def monsterLieRootSpaceEquiv (x y : ℤ) (h : x ≠ 0 ∨ y ≠ 0) :
    monsterLieMomentum ![x, y] ≃ₗ[ℂ] VnatVOA.grading (1 - x * y) :=
  (monsterLieSectorQuotientEquiv x y (stringSectorFamily x y h)).symm.trans
    (stringSectorNoGhostEquiv x y h)

/-- Change only the spelling of the zero momentum; the underlying Lie vector is unchanged. -/
def monsterLieZeroMomentumTransport : monsterLieMomentum ![0, 0] ≃ₗ[ℂ] monsterLieMomentum 0 :=
  LinearEquiv.ofEq _ _ (congrArg monsterLieMomentum
    (show (![0, 0] : lorentzianLattice.carrier) = 0 by
      change (![0, 0] : Fin 2 → ℤ) = 0
      funext a; fin_cases a <;> rfl))

theorem monsterLieZeroMomentumTransport_coe (u : monsterLieMomentum ![0, 0]) :
    (monsterLieZeroMomentumTransport u : monsterLieAlgebra) = u :=
  LinearEquiv.coe_ofEq_apply _ u

/-- The zero-momentum part is the two-dimensional hyperbolic plane. -/
def monsterLieZeroMomentumEquiv : monsterLieMomentum 0 ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  monsterLieZeroMomentumTransport.symm.trans
    ((monsterLieSectorQuotientEquiv 0 0 0).symm.trans vnatZeroNoGhostEquiv)

end VOA.Moonshine.ConwayNorton
