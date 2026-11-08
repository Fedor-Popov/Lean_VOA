import VOA.Moonshine.MoonshineCNBorcherdsRoots
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! Abstract Borcherds data (BD1--BD6), with no vertex-algebra assumptions or instance. -/

namespace VOA.Moonshine.ConwayNorton

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g]

def borcherdsSimpleGenerators (wt : ℤ × ℤ → Submodule ℂ g) : Set g :=
  {x | x ∈ wt 0 ∨ ∃ α, borcherdsSimpleRoot α ∧ (x ∈ wt α ∨ x ∈ wt (-α))}

/-- The exact abstract hypotheses for the rank-two Lie-theoretic argument.
Generation is an input here; no assertion is made that the Monster Lie algebra has it. -/
structure BorcherdsData (g : Type*) [LieRing g] [LieAlgebra ℂ g] where
  weightSpace : ℤ × ℤ → Submodule ℂ g
  weight_internal : DirectSum.IsInternal weightSpace
  weight_finite : ∀ γ, FiniteDimensional ℂ (weightSpace γ)
  bracket_weight : ∀ {γ δ} {x y : g},
    x ∈ weightSpace γ → y ∈ weightSpace δ → ⁅x, y⁆ ∈ weightSpace (γ + δ)
  cartanMap : (ℂ × ℂ) →ₗ[ℂ] g
  cartan_injective : Function.Injective cartanMap
  cartan_range : LinearMap.range cartanMap = weightSpace 0
  cartan_action : ∀ (ξ : ℂ × ℂ) (γ : ℤ × ℤ) (x : g), x ∈ weightSpace γ →
    ⁅cartanMap ξ, x⁆ = borcherdsCartanPairing ξ (borcherdsWeightVector γ) • x
  form : LinearMap.BilinForm ℂ g
  form_symmetric : ∀ x y, form x y = form y x
  form_invariant : ∀ x y z, form ⁅x, y⁆ z = form x ⁅y, z⁆
  form_orthogonal : ∀ γ δ, γ + δ ≠ 0 → ∀ x ∈ weightSpace γ,
    ∀ y ∈ weightSpace δ, form x y = 0
  form_cartan : ∀ ξ μ, form (cartanMap ξ) (cartanMap μ) = borcherdsCartanPairing ξ μ
  form_nondegenerate : ∀ γ, ∀ x ∈ weightSpace γ,
    (∀ y ∈ weightSpace (-γ), form x y = 0) → x = 0
  root_support : ∀ γ, weightSpace γ ≠ ⊥ → borcherdsRootSupport γ
  real_dimension : Module.finrank ℂ (weightSpace borcherdsRealRoot) = 1 ∧
    Module.finrank ℂ (weightSpace (-borcherdsRealRoot)) = 1
  generated : LieSubalgebra.lieSpan ℂ g (borcherdsSimpleGenerators weightSpace) = ⊤

namespace BorcherdsData

variable (D : BorcherdsData g)

/-- The optional equivariance input (a group acting by graded, form-preserving Lie algebra
automorphisms), separate from the Lie-theoretic data. -/
structure GAction (G : Type*) [Group G] where
  action : G →* (g ≃ₗ[ℂ] g)
  preserves_lie : ∀ σ x y, action σ ⁅x, y⁆ = ⁅action σ x, action σ y⁆
  graded : ∀ σ γ x, x ∈ D.weightSpace γ → action σ x ∈ D.weightSpace γ
  preserves_form : ∀ σ x y, D.form (action σ x) (action σ y) = D.form x y
  fixes_cartan : ∀ σ x, x ∈ D.weightSpace 0 → action σ x = x
  fixes_real : ∀ σ x,
    x ∈ D.weightSpace borcherdsRealRoot ∨ x ∈ D.weightSpace (-borcherdsRealRoot) →
      action σ x = x

theorem weight_eq_bot_of_not_supported (γ : ℤ × ℤ) (hγ : ¬ borcherdsRootSupport γ) :
    D.weightSpace γ = ⊥ := by
  by_contra h
  exact hγ (D.root_support γ h)

theorem cartan_mem_weight_zero (ξ : ℂ × ℂ) : D.cartanMap ξ ∈ D.weightSpace 0 := by
  rw [← D.cartan_range]
  exact ⟨ξ, rfl⟩

/-- Bracketing opposite homogeneous components is determined by the invariant form. -/
theorem bracket_eq_form_smul_cartan (γ : ℤ × ℤ) (x y : g)
    (hx : x ∈ D.weightSpace γ) (hy : y ∈ D.weightSpace (-γ)) :
    ⁅x, y⁆ = D.form x y • D.cartanMap (borcherdsWeightVector γ) := by
  apply sub_eq_zero.mp
  apply D.form_nondegenerate 0
  · apply Submodule.sub_mem
    · simpa only [add_neg_cancel] using D.bracket_weight hx hy
    · exact Submodule.smul_mem _ _ (D.cartan_mem_weight_zero _)
  · intro z hz
    rw [neg_zero, ← D.cartan_range] at hz
    obtain ⟨ξ, rfl⟩ := hz
    rw [map_sub, LinearMap.sub_apply, D.form_invariant, ← lie_skew y (D.cartanMap ξ),
      D.cartan_action ξ (-γ) y hy]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, map_neg, D.form_cartan,
      borcherdsCartanPairing, borcherdsWeightVector, Prod.fst_neg, Prod.snd_neg,
      Int.cast_neg]
    ring

/-- Real root spaces have a normalized dual pair; no choice of such a pair is an extra input. -/
theorem exists_normalized_real_pair : ∃ e f : g,
    e ∈ D.weightSpace borcherdsRealRoot ∧ f ∈ D.weightSpace (-borcherdsRealRoot) ∧
      D.form e f = 1 := by
  classical
  letI : Nontrivial (D.weightSpace borcherdsRealRoot) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [D.real_dimension.1]; norm_num)
  obtain ⟨e, he⟩ := exists_ne (0 : D.weightSpace borcherdsRealRoot)
  have he0 : (e : g) ≠ 0 := fun h => he (Subtype.ext h)
  have hp : ∃ f ∈ D.weightSpace (-borcherdsRealRoot), D.form e f ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact he0 (D.form_nondegenerate borcherdsRealRoot e e.property hn)
  obtain ⟨f, hf, hef⟩ := hp
  refine ⟨e, (D.form e f)⁻¹ • f, e.property, Submodule.smul_mem _ _ hf, ?_⟩
  simp [map_smul, smul_eq_mul, hef]

/-- A normalized pair in the real root spaces gives the three sl2 commutators. -/
theorem real_sl2_relations (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    ⁅e, f⁆ = D.cartanMap (1, -1) ∧
      ⁅D.cartanMap (1, -1), e⁆ = (2 : ℂ) • e ∧
      ⁅D.cartanMap (1, -1), f⁆ = (-2 : ℂ) • f := by
  constructor
  · simpa [hef, borcherdsRealRoot, borcherdsWeightVector] using
      D.bracket_eq_form_smul_cartan borcherdsRealRoot e f he hf
  constructor
  · convert D.cartan_action (1, -1) borcherdsRealRoot e he using 1 <;>
      norm_num [borcherdsCartanPairing, borcherdsWeightVector, borcherdsRealRoot]
  · convert D.cartan_action (1, -1) (-borcherdsRealRoot) f hf using 1 <;>
      norm_num [borcherdsCartanPairing, borcherdsWeightVector, borcherdsRealRoot]

/-- The real lowering operator kills every positive imaginary simple root space. -/
theorem simple_lowering_vanishes (j : ℤ) (hj : 1 ≤ j) (f v : g)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot))
    (hv : v ∈ D.weightSpace (borcherdsImaginaryRoot j)) : ⁅f, v⁆ = 0 := by
  have h := D.bracket_weight hf hv
  rw [D.weight_eq_bot_of_not_supported (-borcherdsRealRoot + borcherdsImaginaryRoot j)] at h
  · exact h
  · simp only [borcherdsRootSupport, borcherdsPositiveRoot, borcherdsPositiveCone,
      borcherdsRealRoot, borcherdsImaginaryRoot, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg]
    omega

end BorcherdsData
end VOA.Moonshine.ConwayNorton
