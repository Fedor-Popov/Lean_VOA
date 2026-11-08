import VOA.Moonshine.MoonshineCNMonsterForm
import VOA.Moonshine.MoonshineCNSectorFormConvention

/-! Nondegenerate pairings between opposite root spaces of the actual Lie quotient. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

attribute [local instance] monsterPhysicalAddCommGroup

theorem monsterLieBilinearForm_momentum_orthogonal (α β : lorentzianLattice.carrier)
    (hαβ : α + β ≠ 0) (u v : monsterLieAlgebra)
    (hu : u ∈ monsterLieMomentum α) (hv : v ∈ monsterLieMomentum β) :
    monsterLieBilinearForm u v = 0 := by
  obtain ⟨p, hp, rfl⟩ := hu
  obtain ⟨q, hq, rfl⟩ := hv
  rw [monsterLieBilinearForm_mk,
    moonshineMatterForm_momentum_orthogonal α β hαβ p q hp hq, neg_zero]

/-- Every root space pairs nondegenerately with its opposite, including the zero root. -/
theorem monsterLieBilinearForm_pairing_nondegenerate (α : lorentzianLattice.carrier)
    (u : monsterLieAlgebra) (hu : u ∈ monsterLieMomentum α)
    (hB : ∀ v : monsterLieAlgebra, v ∈ monsterLieMomentum (-α) →
      monsterLieBilinearForm u v = 0) : u = 0 := by
  obtain ⟨p, hp, rfl⟩ := hu
  have hα : α = ![α 0, α 1] := by
    change (α : Fin 2 → ℤ) = ![α 0, α 1]
    funext a; fin_cases a <;> rfl
  change (Submodule.Quotient.mk p : monsterLieAlgebra) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (p : moonshineMatterSpace) ∈ moonshineMatterNearVOA.spurious
  apply (moonshineMatterSector_physical_radical (α 0) (α 1) p p.property
    (hα ▸ hp)).mpr
  intro v hv hm
  let q : moonshineMatterNearVOA.primaryWeightOne :=
    ⟨moonshineMatterReversal v, moonshineMatterReversal_primary v hv⟩
  have hq : monsterLieProjection q ∈ monsterLieMomentum (-α) :=
    ⟨q, moonshineMatterReversal_momentum α v (hα.symm ▸ hm), rfl⟩
  have hz := hB (monsterLieProjection q) hq
  change -moonshineMatterForm p (moonshineMatterReversal v) = 0 at hz
  rw [moonshineMatterReversal_selfAdjoint]
  exact neg_eq_zero.mp hz

/-- The remaining FHL input is precisely zero-mode skew-adjointness on primaries. -/
theorem monsterLieBilinearForm_invariant_of_primaryAdjoint
    (hAdj : ∀ a b c : moonshineMatterNearVOA.primaryWeightOne,
      moonshineMatterForm (moonshineMatterNearVOA.smul a 0 b) c =
        -moonshineMatterForm b (moonshineMatterNearVOA.smul a 0 c))
    (u v w : monsterLieAlgebra) :
    monsterLieBilinearForm ⁅u, v⁆ w = monsterLieBilinearForm u ⁅v, w⁆ := by
  have hskew (a b c : monsterLieAlgebra) :
      monsterLieBilinearForm ⁅a, b⁆ c = -monsterLieBilinearForm b ⁅a, c⁆ := by
    induction a using Submodule.Quotient.induction_on with | _ a =>
    induction b using Submodule.Quotient.induction_on with | _ b =>
    induction c using Submodule.Quotient.induction_on with | _ c =>
    exact congrArg Neg.neg (hAdj a b c)
  rw [← lie_skew u v, LinearMap.map_neg, LinearMap.neg_apply, hskew v u w, neg_neg]

end VOA.Moonshine.ConwayNorton
