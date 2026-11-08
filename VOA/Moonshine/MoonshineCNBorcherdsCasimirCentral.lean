import VOA.Moonshine.MoonshineCNBorcherdsCasimirTelescoping

/-! Centrality of the locally finite Casimir on every admissible Borcherds module. -/
noncomputable section
namespace VOA.Moonshine.ConwayNorton
open Module

theorem borcherdsCasimirScalar_positive_simple_step (μ α : ℤ × ℤ)
    (hα : borcherdsSimpleRoot α) :
    borcherdsCasimirScalar (μ + α) = borcherdsCasimirScalar μ +
      2 * borcherdsCartanPairing (borcherdsWeightVector α) (borcherdsWeightVector μ) := by
  have hfirst : α.1 = 1 := by
    rcases hα with rfl | ⟨j, _, rfl⟩ <;> rfl
  simp only [borcherdsCasimirScalar_eq, borcherdsCartanPairing, borcherdsWeightVector,
    Prod.fst_add, Prod.snd_add, Int.cast_add, hfirst, Int.cast_one]
  ring

theorem borcherdsCasimirScalar_negative_simple_step (μ α : ℤ × ℤ)
    (hα : borcherdsSimpleRoot α) :
    borcherdsCasimirScalar (μ + -α) = borcherdsCasimirScalar μ -
      2 * borcherdsCartanPairing (borcherdsWeightVector α)
        (borcherdsWeightVector (μ + -α)) := by
  have hfirst : α.1 = 1 := by
    rcases hα with rfl | ⟨j, _, rfl⟩ <;> rfl
  simp only [borcherdsCasimirScalar_eq, borcherdsCartanPairing, borcherdsWeightVector,
    Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Int.cast_add, Int.cast_neg,
    hfirst, Int.cast_one]
  ring

variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]
namespace BorcherdsAdmissible
variable {D : BorcherdsData g} {ρ : g →ₗ⁅ℂ⁆ End ℂ M} (A : BorcherdsAdmissible D ρ)

theorem casimirOperator_commutes_positive_simple_weight {μ α : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace α)
    (hα : borcherdsSimpleRoot α) :
    A.casimirOperator (ρ z v) = ρ z (A.casimirOperator v) := by
  have hc := A.positiveCasimirOperator_commutator_positive_simple hv hz hα
  rw [A.cartan_action (borcherdsWeightVector α) hv, map_smul] at hc
  have he := sub_eq_iff_eq_add.mp hc
  change D.cartanCasimirOperator ρ (ρ z v) +
    (2 : ℂ) • A.positiveCasimirOperator (ρ z v) =
      ρ z (D.cartanCasimirOperator ρ v + (2 : ℂ) • A.positiveCasimirOperator v)
  rw [A.cartanCasimirOperator_on_weight (A.action_weight hz hv),
    A.cartanCasimirOperator_on_weight hv, map_add, map_smul, map_smul,
    borcherdsCasimirScalar_positive_simple_step μ α hα, he]
  module

theorem casimirOperator_commutes_negative_simple_weight {μ α : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace (-α))
    (hα : borcherdsSimpleRoot α) :
    A.casimirOperator (ρ z v) = ρ z (A.casimirOperator v) := by
  have hc := A.positiveCasimirOperator_commutator_negative_simple hv hz hα
  rw [A.cartan_action (borcherdsWeightVector α) (A.action_weight hz hv)] at hc
  have he := sub_eq_iff_eq_add.mp hc
  change D.cartanCasimirOperator ρ (ρ z v) +
    (2 : ℂ) • A.positiveCasimirOperator (ρ z v) =
      ρ z (D.cartanCasimirOperator ρ v + (2 : ℂ) • A.positiveCasimirOperator v)
  rw [A.cartanCasimirOperator_on_weight (A.action_weight hz hv),
    A.cartanCasimirOperator_on_weight hv, map_add, map_smul, map_smul,
    borcherdsCasimirScalar_negative_simple_step μ α hα, he]
  module

theorem casimirOperator_commutes_simple (α : ℤ × ℤ) (z : g)
    (hz : z ∈ D.weightSpace α ∨ z ∈ D.weightSpace (-α))
    (hα : borcherdsSimpleRoot α) (v : M) :
    A.casimirOperator (ρ z v) = ρ z (A.casimirOperator v) := by
  have hv : v ∈ ⨆ μ, A.weightSpace μ := by
    rw [A.weight_internal.submodule_iSup_eq_top]
    trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
      rcases hz with hz | hz
      · exact A.casimirOperator_commutes_positive_simple_weight hv hz hα
      · exact A.casimirOperator_commutes_negative_simple_weight hv hz hα
  | zero => simp
  | add v w _ _ hv hw => simp only [map_add, hv, hw]

/-- BD5 generation extends the checked Cartan and simple-root commutators to all of g. -/
theorem casimirOperator_commutes (z : g) (v : M) :
    A.casimirOperator (ρ z v) = ρ z (A.casimirOperator v) := by
  have hz : z ∈ LieSubalgebra.lieSpan ℂ g (borcherdsSimpleGenerators D.weightSpace) := by
    rw [D.generated]
    trivial
  revert v
  induction hz using LieSubalgebra.lieSpan_induction with
  | mem z hz =>
      rcases hz with hz | ⟨α, hα, hz⟩
      · rw [← D.cartan_range] at hz
        obtain ⟨ξ, rfl⟩ := hz
        exact A.casimirOperator_commutes_cartan ξ
      · exact A.casimirOperator_commutes_simple α z hz hα
  | zero => intro v; simp
  | add z w _ _ hz hw =>
      intro v
      simp only [map_add, LinearMap.add_apply, hz, hw]
  | smul c z _ hz =>
      intro v
      simp only [map_smul, LinearMap.smul_apply, hz]
  | lie z w _ _ hz hw =>
      intro v
      rw [ρ.map_lie]
      simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, map_sub, hz, hw]

end BorcherdsAdmissible
end VOA.Moonshine.ConwayNorton

