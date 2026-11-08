import VOA.Moonshine.MoonshineCNMonsterLie
import Mathlib.Algebra.DirectSum.Decomposition

/-! The internal momentum grading descends through physical spurious states. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open IntegralLattice LatGen HeisenbergN
open scoped TensorProduct BigOperators

attribute [local instance] monsterPhysicalAddCommGroup
attribute [local instance] Classical.typeDecidableEq

theorem moonshineMatterConformal_momentum :
    moonshineMatterNearVOA.conformalVector ∈ moonshineMatterMomentum 0 := by
  rw [moonshineMatterNearVOA_conformalVector]
  apply Submodule.add_mem
  · exact moonshineMatterMomentum_tmul 0 _
      (latState_mem_momentum lorentzianLattice (vacuumN _) 0)
  · exact moonshineMatterMomentum_tmul 0 _
      (latState_mem_momentum lorentzianLattice (ωN _ 1) 0)

theorem moonshineMatterVirasoro_momentum (n : ℤ) (α : lorentzianLattice.carrier)
    (u : moonshineMatterSpace) (hu : u ∈ moonshineMatterMomentum α) :
    moonshineMatterNearVOA.L n u ∈ moonshineMatterMomentum α := by
  simpa only [zero_add] using moonshineMatterMomentum_mode 0 α
    moonshineMatterNearVOA.conformalVector u moonshineMatterConformal_momentum hu (n + 1)

instance matterMomentumDecomposition : DirectSum.Decomposition moonshineMatterMomentum :=
  moonshineMatterMomentum_isInternal.chooseDecomposition

def matterMomentumComponent (α : lorentzianLattice.carrier) :
    Module.End ℂ moonshineMatterSpace :=
  (moonshineMatterMomentum α).subtype.comp
    ((DirectSum.component ℂ _ (fun β => moonshineMatterMomentum β) α).comp
      (DirectSum.decomposeLinearEquiv moonshineMatterMomentum).toLinearMap)

theorem matterMomentumComponent_mem (α : lorentzianLattice.carrier)
    (u : moonshineMatterSpace) : matterMomentumComponent α u ∈ moonshineMatterMomentum α :=
  (DirectSum.decompose moonshineMatterMomentum u α).property

theorem matterMomentumComponent_of_mem (α : lorentzianLattice.carrier)
    (u : moonshineMatterSpace) (hu : u ∈ moonshineMatterMomentum α) :
    matterMomentumComponent α u = u :=
  DirectSum.decompose_of_mem_same moonshineMatterMomentum hu

theorem matterMomentumComponent_of_mem_ne (α β : lorentzianLattice.carrier)
    (u : moonshineMatterSpace) (hu : u ∈ moonshineMatterMomentum β) (hne : α ≠ β) :
    matterMomentumComponent α u = 0 :=
  DirectSum.decompose_of_mem_ne moonshineMatterMomentum hu hne.symm

theorem matterMomentumComponent_virasoro (α : lorentzianLattice.carrier)
    (n : ℤ) (u : moonshineMatterSpace) :
    matterMomentumComponent α (moonshineMatterNearVOA.L n u) =
      moonshineMatterNearVOA.L n (matterMomentumComponent α u) := by
  induction u using DirectSum.Decomposition.inductionOn moonshineMatterMomentum with
  | zero => simp only [LinearMap.map_zero]
  | homogeneous u =>
    rename_i β
    by_cases h : α = β
    · subst β
      rw [matterMomentumComponent_of_mem α _
        (moonshineMatterVirasoro_momentum n α u u.property),
        matterMomentumComponent_of_mem α u u.property]
    · rw [matterMomentumComponent_of_mem_ne α β _
        (moonshineMatterVirasoro_momentum n β u u.property) h,
        matterMomentumComponent_of_mem_ne α β u u.property h, LinearMap.map_zero]
  | add u v hu hv => simp only [LinearMap.map_add, hu, hv]

/-- Momentum projection on physical classes; spurious preservation follows from intertwining. -/
def monsterLieMomentumComponent (α : lorentzianLattice.carrier) :
    Module.End ℂ monsterLieAlgebra :=
  moonshineMatterNearVOA.primaryQuotientMap (matterMomentumComponent α)
    (matterMomentumComponent_virasoro α)

theorem monsterLieMomentumComponent_mem (α : lorentzianLattice.carrier)
    (u : monsterLieAlgebra) : monsterLieMomentumComponent α u ∈ monsterLieMomentum α := by
  induction u using Submodule.Quotient.induction_on with
  | _ v => exact ⟨_, matterMomentumComponent_mem α v, rfl⟩

theorem monsterLieMomentumComponent_of_mem (α : lorentzianLattice.carrier)
    (u : monsterLieAlgebra) (hu : u ∈ monsterLieMomentum α) :
    monsterLieMomentumComponent α u = u := by
  obtain ⟨v, hv, rfl⟩ := hu
  change monsterLieProjection _ = monsterLieProjection v
  congr 1
  exact Subtype.ext (matterMomentumComponent_of_mem α v hv)

theorem monsterLieMomentumComponent_of_mem_ne (α β : lorentzianLattice.carrier)
    (u : monsterLieAlgebra) (hu : u ∈ monsterLieMomentum β) (hne : α ≠ β) :
    monsterLieMomentumComponent α u = 0 := by
  obtain ⟨v, hv, rfl⟩ := hu
  change monsterLieProjection _ = monsterLieProjection 0
  congr 1
  exact Subtype.ext (matterMomentumComponent_of_mem_ne α β v hv hne)

/-- The quotient is the direct sum of its momentum subspaces, not merely their span. -/
theorem monsterLieMomentum_isInternal : DirectSum.IsInternal monsterLieMomentum := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero monsterLieMomentum).mpr
    intro s v hv hsum α hα
    have h := congrArg (monsterLieMomentumComponent α) hsum
    rw [map_sum, LinearMap.map_zero] at h
    rw [Finset.sum_eq_single α] at h
    · rwa [monsterLieMomentumComponent_of_mem α (v α) (hv α hα)] at h
    · intro β hβ hne
      exact monsterLieMomentumComponent_of_mem_ne α β (v β) (hv β hβ) hne.symm
    · exact fun hnot => (hnot hα).elim
  · apply eq_top_iff.mpr
    intro x _
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      let s := (DirectSum.decompose moonshineMatterMomentum (v : moonshineMatterSpace)).support
      have hs : (∑ α ∈ s,
          moonshineMatterNearVOA.primaryLinearMap (matterMomentumComponent α)
            (matterMomentumComponent_virasoro α) v) = v := by
        apply Subtype.ext
        simp only [Submodule.coe_sum]
        change (∑ α ∈ s, matterMomentumComponent α (v : moonshineMatterSpace)) = v
        exact DirectSum.sum_support_decompose moonshineMatterMomentum (v : moonshineMatterSpace)
      change monsterLieProjection v ∈ _
      rw [← hs, map_sum]
      apply Submodule.sum_mem
      intro α _
      exact Submodule.mem_iSup_of_mem α (monsterLieMomentumComponent_mem α (monsterLieProjection v))

end VOA.Moonshine.ConwayNorton
