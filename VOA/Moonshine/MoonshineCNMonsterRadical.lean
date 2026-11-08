import VOA.Moonshine.MoonshineCNMonsterPairing

/-! Global nondegeneracy and the full physical radical, from the momentum decomposition. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators

attribute [local instance] monsterPhysicalAddCommGroup

theorem monsterLieBilinearForm_component (α : lorentzianLattice.carrier)
    (u v : monsterLieAlgebra) (hv : v ∈ monsterLieMomentum (-α)) :
    monsterLieBilinearForm (monsterLieMomentumComponent α u) v =
      monsterLieBilinearForm u v := by
  classical
  letI : DirectSum.Decomposition monsterLieMomentum :=
    monsterLieMomentum_isInternal.chooseDecomposition
  induction u using DirectSum.Decomposition.inductionOn monsterLieMomentum with
  | zero => simp only [LinearMap.map_zero, LinearMap.zero_apply]
  | homogeneous u =>
    rename_i β
    by_cases h : α = β
    · subst β
      rw [monsterLieMomentumComponent_of_mem α u u.property]
    · rw [monsterLieMomentumComponent_of_mem_ne α β u u.property h,
        LinearMap.map_zero, LinearMap.zero_apply]
      exact (monsterLieBilinearForm_momentum_orthogonal β (-α)
        (by intro he; apply h; exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using he)).symm)
        u v u.property hv).symm
  | add u w hu hw => simp only [LinearMap.map_add, LinearMap.add_apply, hu, hw]

theorem monsterLieBilinearForm_nondegenerate : monsterLieBilinearForm.Nondegenerate := by
  classical
  letI : DirectSum.Decomposition moonshineMatterMomentum :=
    moonshineMatterMomentum_isInternal.chooseDecomposition
  have hleft (u : monsterLieAlgebra) (hB : ∀ v, monsterLieBilinearForm u v = 0) : u = 0 := by
    have hc (α : lorentzianLattice.carrier) : monsterLieMomentumComponent α u = 0 := by
      apply monsterLieBilinearForm_pairing_nondegenerate α _ (monsterLieMomentumComponent_mem α u)
      intro v hv
      rw [monsterLieBilinearForm_component α u v hv]
      exact hB v
    induction u using Submodule.Quotient.induction_on with
    | _ p =>
      let s := (DirectSum.decompose moonshineMatterMomentum (p : moonshineMatterSpace)).support
      have hs : (∑ α ∈ s,
          moonshineMatterNearVOA.primaryLinearMap (matterMomentumComponent α)
            (matterMomentumComponent_virasoro α) p) = p := by
        apply Subtype.ext
        simp only [Submodule.coe_sum]
        exact DirectSum.sum_support_decompose moonshineMatterMomentum (p : moonshineMatterSpace)
      change monsterLieProjection p = 0
      rw [← hs, map_sum monsterLieProjection]
      exact Finset.sum_eq_zero fun α _ => hc α
  exact ⟨hleft, fun u hu => hleft u fun v => by
    rw [monsterLieBilinearForm_symmetric]; exact hu v⟩

/-- The original vertex-space form has exactly the physical spurious radical. -/
theorem moonshineMatterPrimary_radical (u : moonshineMatterNearVOA.primaryWeightOne) :
    u ∈ moonshineMatterNearVOA.primarySpurious ↔
      ∀ v : moonshineMatterNearVOA.primaryWeightOne, moonshineMatterForm u v = 0 := by
  constructor
  · intro hu v
    exact moonshineMatterForm_spurious_primary u hu v
  · intro hu
    have hz : monsterLieProjection u = 0 := by
      apply monsterLieBilinearForm_nondegenerate.1
      intro v
      induction v using Submodule.Quotient.induction_on with | _ v =>
      change -moonshineMatterForm u v = 0
      rw [hu v, neg_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mp hz

end VOA.Moonshine.ConwayNorton
