import VOA.Moonshine.MoonshineCNBorcherdsCasimirBoundary

/-! Finite-support reindexing of the root commutator and simple-root telescoping. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace VOA.Moonshine.ConwayNorton
open Module
variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]
namespace BorcherdsAdmissible
variable {D : BorcherdsData g} {ρ : g →ₗ⁅ℂ⁆ End ℂ M} (A : BorcherdsAdmissible D ρ)

theorem shiftedCasimirBoundary_finiteSupport {μ γ : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace γ) (δ : ℤ × ℤ) :
    Function.HasFiniteSupport (fun α => if borcherdsPositiveRoot α then
      D.rootCasimirBoundaryTerm ρ z (α + δ) v else 0) := by
  apply borcherdsRootTerms_finiteSupport
  refine ⟨borcherdsRootHeight (μ + γ) - A.lowerHeight - borcherdsRootHeight δ, ?_⟩
  intro α _ hh
  apply A.rootCasimirBoundaryTerm_height_vanishes hv hz
  simp only [borcherdsRootHeight, Prod.fst_add, Prod.snd_add] at *
  omega

/-- All four sums in this reindexing have proved finite support at the given vector. -/
theorem positiveCasimirOperator_commutator_finsum {μ γ : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace γ) :
    A.positiveCasimirOperator (ρ z v) - ρ z (A.positiveCasimirOperator v) =
      ∑ᶠ β, ((if borcherdsPositiveRoot β then D.rootCasimirBoundaryTerm ρ z β v else 0) -
        (if borcherdsPositiveRoot (β - γ) then D.rootCasimirBoundaryTerm ρ z β v else 0)) := by
  classical
  let B := D.rootCasimirBoundaryTerm ρ z
  have h₀ : Function.HasFiniteSupport (fun β =>
      if borcherdsPositiveRoot β then B β v else 0) := by
    simpa only [add_zero] using A.shiftedCasimirBoundary_finiteSupport hv hz 0
  have hshift := A.shiftedCasimirBoundary_finiteSupport hv hz γ
  have hpre : Function.HasFiniteSupport (fun β =>
      if borcherdsPositiveRoot (β - γ) then B β v else 0) := by
    have hinj : Function.Injective (fun β : ℤ × ℤ => β - γ) := by
      intro a b hab
      have hh := congrArg (fun β : ℤ × ℤ => β + γ) hab
      simpa only [sub_add_cancel] using hh
    simpa only [sub_add_cancel] using
      Function.HasFiniteSupport.fun_comp_of_injective hinj hshift
  have hreindex : (∑ᶠ α, if borcherdsPositiveRoot α then B (α + γ) v else 0) =
      ∑ᶠ β, if borcherdsPositiveRoot (β - γ) then B β v else 0 :=
    finsum_eq_of_bijective (fun α : ℤ × ℤ => α + γ) (Equiv.addRight γ).bijective
      (fun α => by simp only [add_sub_cancel_right])
  change (∑ᶠ α, if borcherdsPositiveRoot α then D.rootCasimirTerm ρ α (ρ z v) else 0) -
    ρ z (∑ᶠ α, if borcherdsPositiveRoot α then D.rootCasimirTerm ρ α v else 0) = _
  rw [map_finsum (ρ z) (A.rootCasimirTerms_finiteSupport v)]
  have hmapped : Function.HasFiniteSupport (fun α =>
      ρ z (if borcherdsPositiveRoot α then D.rootCasimirTerm ρ α v else 0)) :=
    (A.rootCasimirTerms_finiteSupport v).fun_comp (map_zero (ρ z))
  rw [← finsum_sub_distrib (A.rootCasimirTerms_finiteSupport (ρ z v))
    hmapped]
  calc
    _ = ∑ᶠ α, ((if borcherdsPositiveRoot α then B α v else 0) -
        (if borcherdsPositiveRoot α then B (α + γ) v else 0)) := by
      apply finsum_congr
      intro α
      by_cases hp : borcherdsPositiveRoot α
      · simp only [if_pos hp]
        exact LinearMap.congr_fun (D.rootCasimirTerm_commutator ρ α γ z hz) v
      · simp only [if_neg hp, map_zero, sub_self]
    _ = _ := by
      rw [finsum_sub_distrib h₀ hshift, hreindex, finsum_sub_distrib h₀ hpre]

theorem positiveCasimirOperator_commutator_positive_simple {μ α : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace α)
    (hα : borcherdsSimpleRoot α) :
    A.positiveCasimirOperator (ρ z v) - ρ z (A.positiveCasimirOperator v) =
      -(ρ z (ρ (D.cartanMap (borcherdsWeightVector α)) v)) := by
  have hpos : borcherdsPositiveRoot α := by
    rcases hα with rfl | ⟨j, hj, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by norm_num [borcherdsImaginaryRoot], hj⟩
  have hzero : ¬ borcherdsPositiveRoot 0 := by
    norm_num [borcherdsPositiveRoot, borcherdsPositiveCone, borcherdsRealRoot, Prod.ext_iff]
  rw [A.positiveCasimirOperator_commutator_finsum hv hz]
  rw [finsum_eq_single _ α]
  · simp only [sub_self, if_pos hpos, if_neg hzero, sub_zero,
      D.rootCasimirBoundaryTerm_self ρ α z hz, LinearMap.neg_apply, Module.End.mul_apply]
  · intro β hβ
    by_cases hs : borcherdsRootSupport β ∧ borcherdsRootSupport (α - β)
    · have hp := borcherdsSimpleRoot_positive_boundary hα hs.1 hs.2
      simp only [hβ, false_or] at hp
      simp only [hp, sub_self]
    · have hb := D.rootCasimirBoundaryTerm_unsupported ρ α β z hz (not_and_or.mp hs)
      simp only [hb, LinearMap.zero_apply, ite_self, sub_self]

theorem positiveCasimirOperator_commutator_negative_simple {μ α : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace (-α))
    (hα : borcherdsSimpleRoot α) :
    A.positiveCasimirOperator (ρ z v) - ρ z (A.positiveCasimirOperator v) =
      ρ (D.cartanMap (borcherdsWeightVector α)) (ρ z v) := by
  have hpos : borcherdsPositiveRoot α := by
    rcases hα with rfl | ⟨j, hj, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by norm_num [borcherdsImaginaryRoot], hj⟩
  have hzero : ¬ borcherdsPositiveRoot 0 := by
    norm_num [borcherdsPositiveRoot, borcherdsPositiveCone, borcherdsRealRoot, Prod.ext_iff]
  have hweight : borcherdsWeightVector (-α) = -borcherdsWeightVector α := by
    ext <;> simp [borcherdsWeightVector]
  rw [A.positiveCasimirOperator_commutator_finsum hv hz]
  rw [finsum_eq_single _ 0]
  · simp only [zero_sub, neg_neg, if_neg hzero, if_pos hpos, zero_sub,
      D.rootCasimirBoundaryTerm_zero ρ (-α) z hz, Module.End.mul_apply, hweight,
      map_neg, LinearMap.neg_apply, neg_neg]
  · intro β hβ
    by_cases hs : borcherdsRootSupport β ∧ borcherdsRootSupport (-α - β)
    · have hp := borcherdsSimpleRoot_negative_boundary hα hs.1 hs.2
      simp only [hβ, false_or] at hp
      simp only [sub_neg_eq_add, hp, sub_self]
    · have hb := D.rootCasimirBoundaryTerm_unsupported ρ (-α) β z hz (not_and_or.mp hs)
      simp only [hb, LinearMap.zero_apply, ite_self, sub_self]

end BorcherdsAdmissible
end VOA.Moonshine.ConwayNorton

