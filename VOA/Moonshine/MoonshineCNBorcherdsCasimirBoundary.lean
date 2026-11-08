import VOA.Moonshine.MoonshineCNBorcherdsCasimirCommutator

/-! Root-support cancellation and the two boundary terms in the Casimir calculation. -/
noncomputable section
open scoped BigOperators
namespace VOA.Moonshine.ConwayNorton
open Module

theorem borcherdsSimpleRoot_positive_boundary {α β : ℤ × ℤ}
    (hα : borcherdsSimpleRoot α) (hβ : borcherdsRootSupport β)
    (hd : borcherdsRootSupport (α - β)) :
    borcherdsPositiveRoot β ↔ β = α ∨ borcherdsPositiveRoot (β - α) := by
  rcases hα with rfl | ⟨j, hj, rfl⟩ <;>
    simp only [borcherdsRootSupport, borcherdsPositiveRoot, borcherdsPositiveCone,
      borcherdsRealRoot, borcherdsImaginaryRoot, Prod.ext_iff, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero] at * <;>
    omega

theorem borcherdsSimpleRoot_negative_boundary {α β : ℤ × ℤ}
    (hα : borcherdsSimpleRoot α) (hβ : borcherdsRootSupport β)
    (hd : borcherdsRootSupport (-α - β)) :
    borcherdsPositiveRoot (β + α) ↔ β = 0 ∨ borcherdsPositiveRoot β := by
  rcases hα with rfl | ⟨j, hj, rfl⟩ <;>
    simp only [borcherdsRootSupport, borcherdsPositiveRoot, borcherdsPositiveCone,
      borcherdsRealRoot, borcherdsImaginaryRoot, Prod.ext_iff, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_zero, Prod.snd_zero] at * <;>
    omega

variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]
namespace BorcherdsData
variable (D : BorcherdsData g) (ρ : g →ₗ⁅ℂ⁆ End ℂ M)

theorem rootCasimirBoundaryTerm_unsupported (γ β : ℤ × ℤ) (z : g)
    (hz : z ∈ D.weightSpace γ)
    (hs : ¬ borcherdsRootSupport β ∨ ¬ borcherdsRootSupport (γ - β)) :
    D.rootCasimirBoundaryTerm ρ z β = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rcases hs with hs | hs
  · have he : (D.rootFiniteBasis β i : g) = 0 :=
      (show D.weightSpace β ≤ ⊥ from le_of_eq
        (D.weight_eq_bot_of_not_supported β hs)) (D.rootFiniteBasis β i).property
    rw [he, map_zero, zero_mul]
  · have hf := D.bracket_weight
      (D.rootOppositeBasis (D.rootFiniteBasis β) i).property hz
    have he : -β + γ = γ - β := by abel
    rw [he, D.weight_eq_bot_of_not_supported (γ - β) hs] at hf
    change ⁅(D.rootOppositeBasis (D.rootFiniteBasis β) i : g), z⁆ = 0 at hf
    rw [hf, map_zero, mul_zero]

theorem rootCasimirBoundaryTerm_self (α : ℤ × ℤ) (z : g)
    (hz : z ∈ D.weightSpace α) :
    D.rootCasimirBoundaryTerm ρ z α = -(ρ z * ρ (D.cartanMap (borcherdsWeightVector α))) := by
  classical
  let b := D.rootFiniteBasis α
  have hb (i) : ⁅(D.rootOppositeBasis b i : g), z⁆ =
      -(D.form z (D.rootOppositeBasis b i) • D.cartanMap (borcherdsWeightVector α)) := by
    rw [← lie_skew (D.rootOppositeBasis b i : g) z,
      D.bracket_eq_form_smul_cartan α z _ hz (D.rootOppositeBasis b i).property]
  ext v
  change (∑ i, ρ (b i) * ρ ⁅(D.rootOppositeBasis b i : g), z⁆) v = _
  simp only [LinearMap.sum_apply, Module.End.mul_apply, hb, map_neg, map_smul,
    LinearMap.neg_apply, LinearMap.smul_apply, Finset.sum_neg_distrib]
  have hexp := D.rootBasis_expansion b ⟨z, hz⟩
  change (∑ i, D.form z (D.rootOppositeBasis b i) • (b i : g)) = z at hexp
  have h := congrArg (fun x : g => ρ x (ρ (D.cartanMap (borcherdsWeightVector α)) v)) hexp
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] at h
  exact congrArg Neg.neg h

theorem cartan_bracket_eq_root_form (γ : ℤ × ℤ) (y z : g)
    (hy : y ∈ D.weightSpace 0) (hz : z ∈ D.weightSpace γ) :
    ⁅y, z⁆ = D.form (D.cartanMap (borcherdsWeightVector γ)) y • z := by
  rw [← D.cartan_range] at hy
  obtain ⟨ξ, rfl⟩ := hy
  rw [D.cartan_action ξ γ z hz, D.form_cartan]
  congr 1
  simp only [borcherdsCartanPairing]
  ring

theorem rootCasimirBoundaryTerm_zero (γ : ℤ × ℤ) (z : g)
    (hz : z ∈ D.weightSpace γ) :
    D.rootCasimirBoundaryTerm ρ z 0 =
      ρ (D.cartanMap (borcherdsWeightVector γ)) * ρ z := by
  classical
  let b := D.rootFiniteBasis 0
  let t := D.cartanMap (borcherdsWeightVector γ)
  have hb (i) : ⁅(D.rootOppositeBasis b i : g), z⁆ =
      D.form t (D.rootOppositeBasis b i) • z :=
    D.cartan_bracket_eq_root_form γ _ z
      (by simpa only [neg_zero] using (D.rootOppositeBasis b i).property) hz
  ext v
  change (∑ i, ρ (b i) * ρ ⁅(D.rootOppositeBasis b i : g), z⁆) v = _
  simp only [LinearMap.sum_apply, Module.End.mul_apply, hb, map_smul, LinearMap.smul_apply]
  have hexp := D.rootBasis_expansion b ⟨t, D.cartan_mem_weight_zero _⟩
  change (∑ i, D.form t (D.rootOppositeBasis b i) • (b i : g)) = t at hexp
  have h := congrArg (fun x : g => ρ x (ρ z v)) hexp
  simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] using h

end BorcherdsData
end VOA.Moonshine.ConwayNorton

