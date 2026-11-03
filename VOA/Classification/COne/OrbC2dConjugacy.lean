import VOA.Classification.COne.OrbC2cResidual
import VOA.Classification.COne.AutV2Bridge

/-! # Conjugacy of dihedral subgroups in the actual automorphism group

This includes arbitrary embedded Klein four groups, not just the standard
integral model. The proof uses the existing torus-normalizer classification.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2d
open VOA OrbC2b

/-- Every embedded dihedral group of order `2*n`, `n ≥ 2`, is conjugate
to the standard lattice embedding. -/
theorem dihedral_conjugacy (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (G : Subgroup (Aut (V2m 1 le_rfl))) (e : G ≃* DihedralGroup n) :
    ∃ g : Aut (V2m 1 le_rfl),
      G.map (MulAut.conj g).toMonoidHom = (dihHom 1 le_rfl n).range := by
  letI : Finite G := Finite.of_equiv (DihedralGroup n) e.symm.toEquiv
  obtain ⟨g, hg⟩ := @inNormalizer_conj_of_dihedral G ‹Finite G› n hn e
  let H := G.map (MulAut.conj g).toMonoidHom
  let eg : G ≃* H := G.equivMapOfInjective _ (MulAut.conj g).injective
  letI : Finite H := Finite.of_equiv G eg.toEquiv
  obtain ⟨k, hk, _, hcyc | ⟨w, hw⟩⟩ := finite_subgroup_structure 1 le_rfl H hg
  · have ecyc : Multiplicative (ZMod k) ≃* H :=
      (MonoidHom.ofInjective (cycHom_injective 1 le_rfl)).trans (MulEquiv.subgroupCongr hcyc.symm)
    haveI : IsCyclic (DihedralGroup n) :=
      isCyclic_of_surjective (ecyc.trans (eg.symm.trans e))
        (ecyc.trans (eg.symm.trans e)).surjective
    exact (DihedralGroup.not_isCyclic (by omega : n ≠ 1) inferInstance).elim
  · let ew := H.equivMapOfInjective (MulAut.conj (charU 1 le_rfl w)).toMonoidHom
        (MulAut.conj (charU 1 le_rfl w)).injective
    have ec : DihedralGroup n ≃* DihedralGroup k :=
      e.symm.trans (eg.trans (ew.trans ((MulEquiv.subgroupCongr hw).trans
        (MonoidHom.ofInjective (dihHom_injective 1 le_rfl)).symm)))
    have hnk : n = k := by
      have hc := Nat.card_congr ec.toEquiv
      simp only [DihedralGroup.nat_card] at hc
      omega
    subst k
    refine ⟨charU 1 le_rfl w * g, ?_⟩
    have he : (MulAut.conj (charU 1 le_rfl w * g)).toMonoidHom =
        (MulAut.conj (charU 1 le_rfl w)).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    exact (congrArg (fun f => G.map f) he).trans ((Subgroup.map_map _ _ _).symm.trans hw)

/-- Unconditional conjugacy of arbitrary Klein four subgroups. -/
theorem klein_conjugacy (G : Subgroup (Aut (V2m 1 le_rfl)))
    (e : G ≃* DihedralGroup 2) :
    ∃ g : Aut (V2m 1 le_rfl), G.map (MulAut.conj g).toMonoidHom = klein :=
  dihedral_conjugacy 2 (by omega) G e

end VOA.Classification.COne.OrbC2d
