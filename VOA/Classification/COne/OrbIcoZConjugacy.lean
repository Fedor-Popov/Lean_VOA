import VOA.Classification.COne.OrbIcoMain
import VOA.Classification.COne.LatticeNice

/-! Conformal transport of positivity from the standard icosahedral orbifold.
The isomorphism is constructed from the proved conjugacy theorem. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbIco

local notation "V1" => V2m 1 le_rfl

/-- Conjugation gives an actual homomorphism on all orbifold modes. -/
theorem conjMap_isVOAHom (g : Aut V1) (H : Subgroup (Aut V1)) :
    IsVOAHom (orbifoldVOA H)
      (orbifoldVOA (H.map (MulAut.conj g).toMonoidHom)) (conjMap g H).toLinearMap where
  map_vacuum := conjMap_vacuum g H
  map_smul := conjMap_smul g H

/-- The actual conjugation map preserves the conformal vector. -/
theorem conjMap_conformal (g : Aut V1) (H : Subgroup (Aut V1)) :
    conjMap g H (orbifoldVOA H).conformalVector =
      (orbifoldVOA (H.map (MulAut.conj g).toMonoidHom)).conformalVector := by
  apply Subtype.ext
  exact g.map_omega

/-- Every actual A5 orbifold is conformally isomorphic to the standard model. -/
theorem icosahedral_standardIso (G : Subgroup (Aut V1))
    (hG : Nonempty (G ≃* alternatingGroup (Fin 5))) :
    ∃ e : (orbifold G).carrier ≃ₗ[ℂ] (orbifold ico).carrier,
      IsVOAHom (orbifoldVOA G) Wi e.toLinearMap ∧
        e (orbifoldVOA G).conformalVector = Wi.conformalVector := by
  obtain ⟨g,hg⟩ := icosahedralConjugacy G hG
  have hGeq := map_conj_inv_eq hg
  subst hGeq
  let e := conjMap g⁻¹ ico
  exact ⟨e.symm,isVOAHom_symm' e (conjMap_isVOAHom g⁻¹ ico),
    symm_conformal e (conjMap_conformal g⁻¹ ico)⟩

/-- Positivity of the standard model transports to every actual A5 orbifold. -/
theorem icosahedral_pseudoUnitary_of_standard (hstd : PseudoUnitary Wi) :
    ∀ G : Subgroup (Aut V1), Nonempty (G ≃* alternatingGroup (Fin 5)) →
      PseudoUnitary (orbifoldVOA G) := by
  intro G hG
  obtain ⟨e,he,hω⟩ := icosahedral_standardIso G hG
  exact pseudoUnitary_of_iso e he hω hstd

end VOA.Classification.COne.OrbIcoZ
