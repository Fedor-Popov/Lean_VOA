import VOA.Modularity.ZhuAlgebraFinite
import VOA.Classification.COne.PlusSplitZhuCharacters

/-! The dimension part of Zhu's filtration argument. A basis of the C₂ quotient
can be selected from homogeneous classes. Its homogeneous lifts span the Zhu
quotient by weight induction. No inclusion C₂(V) ≤ O(V) is used. -/

noncomputable section
namespace VOA

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- Homogeneous representatives of a C₂ basis, with exactly dim R(V) entries. -/
theorem exists_homogeneous_c2_basis_lifts (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) :
    ∃ x : Fin (Module.finrank ℂ (A₂ W)) → 𝒱,
      (∀ i, IsHomog W (x i)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range x) ⊔ O₂ W := by
  classical
  letI : FiniteDimensional ℂ (A₂ W) := hC2
  let S : Set (A₂ W) := mk₂ W '' {v | IsHomog W v}
  have hS : Submodule.span ℂ S = ⊤ := by
    rw [show S = mk₂ W '' {v | IsHomog W v} from rfl,
      ← Submodule.map_span, span_homog_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (O₂ W).mkQ_surjective
  let b := Module.Basis.ofSpan hS.ge
  letI := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card ((linearIndepOn_empty ℂ id).extend (Set.empty_subset S)) =
      Module.finrank ℂ (A₂ W) := (Module.finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hc
  let b' := b.reindex e
  have hb' (i : Fin (Module.finrank ℂ (A₂ W))) : b' i ∈ S := by
    exact Module.Basis.ofSpan_subset hS.ge ⟨e.symm i, by simp [b', b]⟩
  choose x hx hxq using hb'
  refine ⟨x, hx, ?_⟩
  have himg : mk₂ W '' Set.range x = Set.range b' := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hxq i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hxq i⟩
  have hmap : (Submodule.span ℂ (Set.range x)).map (O₂ W).mkQ = ⊤ := by
    rw [Submodule.map_span]
    change Submodule.span ℂ (mk₂ W '' Set.range x) = ⊤
    rw [himg, b'.span_eq]
  have := congrArg (Submodule.comap (O₂ W).mkQ) hmap
  simpa only [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] using this.symm

/-- Zhu's weight-filtration dimension inequality, for any C₂-cofinite VOA. -/
theorem finrank_zhu_le_finrank_c2Quotient (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) :
    Module.finrank ℂ (A W) ≤ Module.finrank ℂ (A₂ W) := by
  classical
  obtain ⟨x, hx, hspan⟩ := exists_homogeneous_c2_basis_lifts W hC2
  have hO := span_sup_O_eq_top W (Set.range x) (by
    rintro _ ⟨i, rfl⟩; exact hx i) hspan
  have hfin : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ ((Finset.univ.image x : Finset 𝒱) : Set 𝒱) ⊔ O W := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hO
  exact (finiteDimensional_and_finrank_quot_le_of_span_sup _ hfin).2.trans
    (Finset.card_image_le.trans (by simp))

end VOA

namespace VOA.Classification.COne

/-- The general filtration bound specialized to the plus lattice VOA. -/
theorem V2mPlus_finrank_zhu_le_finrank_c2Quotient (m : ℕ) (hm : 1 ≤ m) :
    Module.finrank ℂ (VOA.A (V2mPlus m hm)) ≤
      Module.finrank ℂ (VOA.A₂ (V2mPlus m hm)) :=
  finrank_zhu_le_finrank_c2Quotient _ (V2mPlus_c2Cofinite m hm)

/-- A sharp C₂ count, if supplied, implies the original Zhu dimension target.
No sharp C₂ count is asserted here. -/
theorem zhuDimensionBound_of_c2DimensionBound
    (h : ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m →
      Module.finrank ℂ (VOA.A₂ (V2mPlus m hm)) ≤ m + 7) :
    V2mPlusZhuDimensionBound := by
  intro m hm hm2
  exact (V2mPlus_finrank_zhu_le_finrank_c2Quotient m hm).trans (h m hm hm2)

end VOA.Classification.COne
