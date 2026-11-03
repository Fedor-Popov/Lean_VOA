import VOA.Classification.COne.OrbIcoConj
import VOA.Classification.COne.OrbXuRelations

/-! # OrbIco: B4 headlines

* `icosaPrimaryReduction_holds`: for every `G ≤ Aut V₂` with `G ≅ A₅` there is a state `X` of
  weight `36` in `V₂^G` with `PrimaryC2Reduction (V₂^G) {𝟙, X}` (no hypotheses).
* `icosa_twoTowers_holds`: hence `A₂(V₂^G)` is spanned by the two conformal towers of `𝟙` and
  `X` (Xu's two-tower span).
* `xuIcosahedralPoissonRelations_of_symbols`: B4 (`XuIcosahedralPoissonRelations`) follows from
  `IcoSymbolRelations`, the two weight-74/76 symbol relations for the single explicit state
  `Xico = T(J₆)` of the single explicit orbifold `V₂^{ico}`. This is a sharp reduction: the
  primary half of `XuIcosahedralPrimaryAndSymbols` is proved, and conjugacy transports the rest.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VertexOperatorAlgebra OrbSpan OrbC2b OrbPrim OrbXu

local notation "V1" => VOA.LatGen.latticeVOAGen (VOA.LatGen.Triplet.latP 1)
  (VOA.LatGen.Triplet.latP_even 1) (VOA.LatGen.Triplet.latP_posDef 1 le_rfl)

theorem map_conj_inv_eq {G : Subgroup (Aut V1)} {g : Aut V1}
    (hg : G.map (MulAut.conj g).toMonoidHom = ico) :
    G = ico.map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [← hg, Subgroup.map_map]
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
    ext x; simp [MulAut.conj_apply, mul_assoc]
  rw [hid, Subgroup.map_id]

theorem conjMap_vacuum (h : Aut V1) (H : Subgroup (Aut V1)) :
    conjMap h H (orbifoldVOA H).vacuum =
      (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)).vacuum := by
  apply Subtype.ext
  rw [conjMap_val]
  exact h.map_vacuum

/-- **B4, primary half**: the primary reduction for every icosahedral orbifold of `V₂`. -/
theorem icosaPrimaryReduction_holds :
    ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 5)) →
      ∃ X : (orbifold G).carrier, X ∈ (orbifoldVOA G).grading 36 ∧
        PrimaryC2Reduction (orbifoldVOA G) {(orbifoldVOA G).vacuum, X} := by
  intro G hG
  obtain ⟨g, hg⟩ := icosahedralConjugacy G hG
  have hGeq := map_conj_inv_eq hg
  subst hGeq
  refine ⟨conjMap g⁻¹ ico Xico, conjMap_grading g⁻¹ ico Xico_grading, ?_⟩
  have h := primaryC2Reduction_conj g⁻¹ ico _ icoPrimaryReduction_std
  rwa [Set.image_pair, conjMap_vacuum] at h

/-- **Xu's two-tower span** for every icosahedral orbifold. -/
theorem icosa_twoTowers_holds :
    ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 5)) →
      ∃ X : (orbifold G).carrier, X ∈ (orbifoldVOA G).grading 36 ∧
        twoTowers (orbifoldVOA G) X = ⊤ := by
  intro G hG
  obtain ⟨X, hX, hP⟩ := icosaPrimaryReduction_holds G hG
  exact ⟨X, hX, orbifold_twoTowers_of_primary G X hP⟩

/-! ## The remaining symbol relations -/

/-- The two weight-74/76 symbol relations of Xu, for the explicit state `Xico = T(J₆)` of the
explicit orbifold `V₂^{ico}`. OPEN. -/
def IcoSymbolRelations : Prop :=
  ∃ c₀ c₆ : ℂ, c₀ ≠ 0 ∧ c₆ ≠ 0 ∧
    modeSymbol Wi Xico (-3) 37 19 (c₀ * (xuU37 : ℂ)) (c₆ * (xuV19 : ℂ)) ∈ O₂ Wi ∧
    modeSymbol Wi Xico (-5) 38 20 (c₀ * (xuU38 : ℂ)) (c₆ * (xuV20 : ℂ)) ∈ O₂ Wi

theorem conjMap_L_pow (h : Aut V1) (H : Subgroup (Aut V1)) (n : ℤ) (k : ℕ)
    (x : (orbifold H).carrier) :
    conjMap h H (((orbifoldVOA H).L n ^ k) x) =
      ((orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)).L n ^ k) (conjMap h H x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, conjMap_L, ih, pow_succ',
      Module.End.mul_apply]

theorem conjMap_modeSymbol (h : Aut V1) (H : Subgroup (Aut V1)) (x : (orbifold H).carrier)
    (m : ℤ) (p q : ℕ) (a b : ℂ) :
    conjMap h H (modeSymbol (orbifoldVOA H) x m p q a b) =
      modeSymbol (orbifoldVOA (H.map (MulAut.conj h).toMonoidHom)) (conjMap h H x) m p q a b := by
  simp only [modeSymbol, map_sub, map_smul, conjMap_smul, conjMap_L_pow, conjMap_vacuum]

/-- **B4 reduced to the two explicit symbol relations.** -/
theorem xuIcosahedralPrimaryAndSymbols_of_symbols (hS : IcoSymbolRelations) :
    XuIcosahedralPrimaryAndSymbols := by
  intro G hG
  obtain ⟨c₀, c₆, hc₀, hc₆, h74, h76⟩ := hS
  obtain ⟨g, hg⟩ := icosahedralConjugacy G hG
  have hGeq := map_conj_inv_eq hg
  subst hGeq
  refine ⟨conjMap g⁻¹ ico Xico, c₀, c₆, conjMap_grading g⁻¹ ico Xico_grading, hc₀, hc₆, ?_, ?_, ?_⟩
  · have h := primaryC2Reduction_conj g⁻¹ ico _ icoPrimaryReduction_std
    rwa [Set.image_pair, conjMap_vacuum] at h
  · have := conjMap_O₂ g⁻¹ ico h74
    rw [conjMap_modeSymbol] at this
    exact this
  · have := conjMap_O₂ g⁻¹ ico h76
    rw [conjMap_modeSymbol] at this
    exact this

/-- `XuIcosahedralPoissonRelations` (B4) from the two explicit symbol relations. -/
theorem xuIcosahedralPoissonRelations_of_symbols (hS : IcoSymbolRelations) :
    XuIcosahedralPoissonRelations :=
  xuIcosahedralPoissonRelations_iff_primaryAndSymbols.mpr
    (xuIcosahedralPrimaryAndSymbols_of_symbols hS)

/-- `C₂`-cofiniteness of every icosahedral orbifold from the two explicit symbol relations. -/
theorem icosa_c2_of_symbols (hS : IcoSymbolRelations) (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hG : Nonempty (G ≃* alternatingGroup (Fin 5))) :
    C2Cofinite (orbifoldVOA G) ∧ Module.finrank ℂ (A₂ (orbifoldVOA G)) ≤ 58 :=
  icosa_c2_of_primaryAndSymbols (xuIcosahedralPrimaryAndSymbols_of_symbols hS) G hG

end VOA.Classification.COne.OrbIco
