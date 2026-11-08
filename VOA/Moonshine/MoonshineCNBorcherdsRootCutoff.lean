import VOA.Moonshine.MoonshineCNBorcherdsData
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Finprod

/-! Bounded-height support for the locally finite root sums used by the Casimir. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace VOA.Moonshine.ConwayNorton

theorem borcherdsPositiveRoot_boundedHeight_finite (h : ℤ) :
    {α : ℤ × ℤ | borcherdsPositiveRoot α ∧ borcherdsRootHeight α ≤ h}.Finite := by
  apply ((Set.finite_singleton borcherdsRealRoot).union
    (Set.finite_Icc (1, 1) (h, h))).subset
  rintro α ⟨hα, hh⟩
  rcases hα with rfl | hα
  · exact Or.inl rfl
  · right
    change (1 ≤ α.1 ∧ 1 ≤ α.2) ∧ α.1 ≤ h ∧ α.2 ≤ h
    simp only [borcherdsPositiveCone, borcherdsRootHeight] at *
    omega

def borcherdsRootCutoff (h : ℤ) : Finset (ℤ × ℤ) :=
  (borcherdsPositiveRoot_boundedHeight_finite h).toFinset

@[simp] theorem mem_borcherdsRootCutoff (α : ℤ × ℤ) (h : ℤ) :
    α ∈ borcherdsRootCutoff h ↔
      borcherdsPositiveRoot α ∧ borcherdsRootHeight α ≤ h :=
  Set.Finite.mem_toFinset _

theorem borcherdsRootCutoff_mono {h k : ℤ} (hh : h ≤ k) :
    borcherdsRootCutoff h ⊆ borcherdsRootCutoff k := by
  intro α hα
  rw [mem_borcherdsRootCutoff] at *
  exact ⟨hα.1, hα.2.trans hh⟩

variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]

/-- A graded representation bounded below in total height. No finite-dimensional
module-slice assumption is included or inferred from these fields. -/
structure BorcherdsAdmissible (D : BorcherdsData g)
    (ρ : g →ₗ⁅ℂ⁆ Module.End ℂ M) where
  weightSpace : ℤ × ℤ → Submodule ℂ M
  weight_internal : DirectSum.IsInternal weightSpace
  action_weight : ∀ {α μ} {x : g} {v : M},
    x ∈ D.weightSpace α → v ∈ weightSpace μ → ρ x v ∈ weightSpace (μ + α)
  cartan_action : ∀ (ξ : ℂ × ℂ) {μ} {v : M}, v ∈ weightSpace μ →
    ρ (D.cartanMap ξ) v = borcherdsCartanPairing ξ (borcherdsWeightVector μ) • v
  lowerHeight : ℤ
  below_eq_bot : ∀ μ, borcherdsRootHeight μ < lowerHeight → weightSpace μ = ⊥

namespace BorcherdsAdmissible
variable {D : BorcherdsData g} {ρ : g →ₗ⁅ℂ⁆ Module.End ℂ M}
variable (A : BorcherdsAdmissible D ρ)

theorem lowering_eq_zero_of_height {μ α : ℤ × ℤ} {v : M} {x : g}
    (hv : v ∈ A.weightSpace μ) (hx : x ∈ D.weightSpace (-α))
    (hh : borcherdsRootHeight μ - A.lowerHeight < borcherdsRootHeight α) :
    ρ x v = 0 := by
  have hm := A.action_weight hx hv
  rw [A.below_eq_bot (μ + -α)] at hm
  · exact hm
  · simp only [borcherdsRootHeight, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg] at *
    omega

include A in
/-- Every vector, including an inhomogeneous one, has a uniform lowering cutoff. -/
theorem exists_lowering_height_bound (v : M) :
    ∃ h : ℤ, ∀ (α : ℤ × ℤ) (x : g), x ∈ D.weightSpace (-α) →
      h < borcherdsRootHeight α → ρ x v = 0 := by
  have hv : v ∈ ⨆ μ, A.weightSpace μ := by
    rw [A.weight_internal.submodule_iSup_eq_top]
    trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
      exact ⟨borcherdsRootHeight μ - A.lowerHeight,
        fun α x hx hh => A.lowering_eq_zero_of_height hv hx hh⟩
  | zero => exact ⟨0, by simp⟩
  | add v w _ _ hv hw =>
      obtain ⟨a, ha⟩ := hv
      obtain ⟨b, hb⟩ := hw
      exact ⟨max a b, fun α x hx hh => by
        rw [map_add, ha α x hx (lt_of_le_of_lt (le_max_left _ _) hh),
          hb α x hx (lt_of_le_of_lt (le_max_right _ _) hh), add_zero]⟩

/-- The simultaneous bound needed before expanding a commutator. -/
theorem lowering_common_height_bound {μ γ : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace γ)
    {h : ℤ} (hμ : borcherdsRootHeight μ - A.lowerHeight ≤ h)
    (hγ : borcherdsRootHeight (μ + γ) - A.lowerHeight ≤ h)
    {α : ℤ × ℤ} {x : g} (hx : x ∈ D.weightSpace (-α))
    (hh : h < borcherdsRootHeight α) :
    ρ x v = 0 ∧ ρ x (ρ z v) = 0 :=
  ⟨A.lowering_eq_zero_of_height hv hx (lt_of_le_of_lt hμ hh),
    A.lowering_eq_zero_of_height (A.action_weight hz hv) hx (lt_of_le_of_lt hγ hh)⟩

end BorcherdsAdmissible

variable (T : (ℤ × ℤ) → Module.End ℂ M)

/-- Finite support follows from a height bound; the height-zero real root is retained. -/
theorem borcherdsRootTerms_finiteSupport (v : M)
    (hT : ∃ h : ℤ, ∀ α, borcherdsPositiveRoot α →
      h < borcherdsRootHeight α → T α v = 0) :
    Function.HasFiniteSupport (fun α => if borcherdsPositiveRoot α then T α v else 0) := by
  classical
  obtain ⟨h, hh⟩ := hT
  apply (borcherdsPositiveRoot_boundedHeight_finite h).subset
  intro α hα
  simp only [Function.mem_support] at hα
  by_cases hp : borcherdsPositiveRoot α
  · refine ⟨hp, ?_⟩
    by_contra hn
    exact hα (by simp [hp, hh α hp (lt_of_not_ge hn)])
  · exact (hα (by simp [hp])).elim

/-- A root sum is evaluated at a vector before summing over roots. -/
def borcherdsLocallyFiniteRootSum
    (hT : ∀ v, Function.HasFiniteSupport
      (fun α => if borcherdsPositiveRoot α then T α v else 0)) : Module.End ℂ M where
  toFun v := ∑ᶠ α, if borcherdsPositiveRoot α then T α v else 0
  map_add' v w := by
    classical
    simp only [map_add, ite_add_zero]
    exact finsum_add_distrib (hT v) (hT w)
  map_smul' c v := by
    classical
    simp only [map_smul, RingHom.id_apply]
    rw [smul_finsum' c (hT v)]
    apply finsum_congr
    intro α
    split_ifs <;> simp

theorem borcherdsLocallyFiniteRootSum_eq_cutoff
    (hT : ∀ v, Function.HasFiniteSupport
      (fun α => if borcherdsPositiveRoot α then T α v else 0))
    (v : M) (h : ℤ)
    (hh : ∀ α, borcherdsPositiveRoot α → h < borcherdsRootHeight α → T α v = 0) :
    borcherdsLocallyFiniteRootSum T hT v = ∑ α ∈ borcherdsRootCutoff h, T α v := by
  classical
  change (∑ᶠ α, if borcherdsPositiveRoot α then T α v else 0) = _
  rw [finsum_eq_sum_of_support_subset _ (s := borcherdsRootCutoff h)]
  · apply Finset.sum_congr rfl
    intro α hα
    simp [(mem_borcherdsRootCutoff α h).mp hα |>.1]
  · intro α hα
    change α ∈ borcherdsRootCutoff h
    rw [mem_borcherdsRootCutoff]
    simp only [Function.mem_support] at hα
    by_cases hp : borcherdsPositiveRoot α
    · refine ⟨hp, ?_⟩
      by_contra hn
      exact hα (by simp [hp, hh α hp (lt_of_not_ge hn)])
    · exact (hα (by simp [hp])).elim

end VOA.Moonshine.ConwayNorton

