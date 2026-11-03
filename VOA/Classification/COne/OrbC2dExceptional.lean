import VOA.Classification.COne.OrbC2dNormalizer

/-! # The two exceptional conjugacy inputs, from the Klein normalizer -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2d
open VOA OrbC2b OrbC2c Equiv Equiv.Perm
local notation "V1" => LatGen.latticeVOAGen (LatGen.Triplet.latP 1)
  (LatGen.Triplet.latP_even 1) (LatGen.Triplet.latP_posDef 1 le_rfl)

/-- Conjugating a normal Klein four subgroup puts the whole group in S₄. -/
theorem conjugate_into_octa_of_normal_klein {H : Type*} [Group H]
    (f : H →* Aut V1) (hf : Function.Injective f)
    (k : DihedralGroup 2 →* H) (hk : Function.Injective k)
    (hN : ∀ x : H, ∀ d : DihedralGroup 2,
      ∃ e : DihedralGroup 2, x * k d * x⁻¹ = k e) :
    ∃ g : Aut V1, f.range.map (MulAut.conj g).toMonoidHom ≤ octa := by
  let K := (f.comp k).range
  let ek : DihedralGroup 2 ≃* K :=
    MonoidHom.ofInjective (f := f.comp k) (hf.comp hk)
  have hc : ∃ g : Aut V1, K.map (MulAut.conj g).toMonoidHom = klein :=
    klein_conjugacy K ek.symm
  obtain ⟨g, hg⟩ := hc
  have hle : f.range ≤ Subgroup.normalizer K := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨d, rfl⟩
    obtain ⟨e, he⟩ := hN x d
    exact ⟨e, by simpa only [MonoidHom.comp_apply, map_mul, map_inv] using
      (congrArg f he).symm⟩
  refine ⟨g, ?_⟩
  have hm := (Subgroup.map_mono hle (f := (MulAut.conj g).toMonoidHom)).trans
    (Subgroup.le_normalizer_map (H := K) (MulAut.conj g).toMonoidHom)
  have hg' : K.map (MulAut.conj g).toMonoidHom = klein := hg
  exact hm.trans (by rw [hg', normalizer_klein_eq_octa])

def kleinAlt : DihedralGroup 2 →* alternatingGroup (Fin 4) :=
  kleinPerm.codRestrict _ kleinPerm_even

theorem kleinAlt_injective : Function.Injective kleinAlt := by
  intro a b h
  exact kleinPerm_injective (congrArg Subtype.val h)

theorem kleinAlt_normal (x : alternatingGroup (Fin 4)) (d : DihedralGroup 2) :
    ∃ e : DihedralGroup 2, x * kleinAlt d * x⁻¹ = kleinAlt e := by
  obtain ⟨e, he⟩ := kleinPerm_normal x.val d
  exact ⟨e, Subtype.ext he⟩

/-- No homomorphism from A₄ to S₄ can send an element to an odd permutation. -/
theorem alternating_hom_even (f : alternatingGroup (Fin 4) →* Perm (Fin 4))
    (x : alternatingGroup (Fin 4)) : f x ∈ alternatingGroup (Fin 4) := by
  have hc (a : alternatingGroup (Fin 4)) (ha : a ^ 3 = 1) : (f a).sign = 1 := by
    have he : (f a).sign ^ 3 = 1 := by rw [← map_pow, ← map_pow, ha, map_one, map_one]
    rcases Int.units_eq_one_or (f a).sign with h | h
    · exact h
    · rw [h] at he
      norm_num at he
  obtain ⟨a, b, ha, hb, rfl⟩ := even_cube_factorization x
  rw [mem_alternatingGroup, map_mul, map_mul, hc a ha, hc b hb, mul_one]

/-- Inside the standard S₄, every embedded A₄ is the standard A₄. -/
theorem tetra_eq_of_le_octa (G : Subgroup (Aut V1))
    (e : G ≃* alternatingGroup (Fin 4)) (hG : G ≤ octa) : G = tetra := by
  let eo : Perm (Fin 4) ≃* octa := MonoidHom.ofInjective octHom_injective
  let f : alternatingGroup (Fin 4) →* Perm (Fin 4) :=
    eo.symm.toMonoidHom.comp ((Subgroup.inclusion hG).comp e.symm.toMonoidHom)
  have hle : G ≤ tetra := by
    intro x hx
    refine ⟨f (e ⟨x, hx⟩), alternating_hom_even f _, ?_⟩
    change ((eo (eo.symm ((Subgroup.inclusion hG) (e.symm (e ⟨x, hx⟩))))) : Aut V1) = x
    simp only [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
    rfl
  letI : Finite tetra := Finite.of_equiv (alternatingGroup (Fin 4))
    tetra_group.some.symm.toEquiv
  apply @Subgroup.eq_of_le_of_card_ge _ _ G tetra ‹Finite tetra› hle
  exact (Nat.card_congr tetra_group.some.toEquiv).trans (Nat.card_congr e.toEquiv).symm |>.le

/-- The first geometric input, unconditionally. -/
theorem tetrahedralConjugacy : TetrahedralConjugacy := by
  change ∀ G : Subgroup (Aut V1), Nonempty (G ≃* alternatingGroup (Fin 4)) →
    ∃ g : Aut V1, G.map (MulAut.conj g).toMonoidHom = tetra
  intro G ⟨e⟩
  let f : alternatingGroup (Fin 4) →* Aut V1 := G.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := G.subtype_injective.comp e.symm.injective
  obtain ⟨g, hg⟩ := conjugate_into_octa_of_normal_klein f hf kleinAlt
    kleinAlt_injective kleinAlt_normal
  have hr : f.range = G := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact (e.symm a).property
    · intro hx; exact ⟨e ⟨x, hx⟩, by
        change ((e.symm (e ⟨x, hx⟩)) : Aut V1) = x
        rw [MulEquiv.symm_apply_apply]⟩
  rw [hr] at hg
  refine ⟨g, tetra_eq_of_le_octa _ ?_ hg⟩
  exact (G.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e

/-- The second geometric input, unconditionally. -/
theorem octahedralConjugacy : OctahedralConjugacy := by
  change ∀ G : Subgroup (Aut V1), Nonempty (G ≃* Perm (Fin 4)) →
    ∃ g : Aut V1, G.map (MulAut.conj g).toMonoidHom = octa
  intro G ⟨e⟩
  let f : Perm (Fin 4) →* Aut V1 := G.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := G.subtype_injective.comp e.symm.injective
  obtain ⟨g, hg⟩ := conjugate_into_octa_of_normal_klein f hf kleinPerm
    kleinPerm_injective kleinPerm_normal
  have hr : f.range = G := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact (e.symm a).property
    · intro hx; exact ⟨e ⟨x, hx⟩, by
        change ((e.symm (e ⟨x, hx⟩)) : Aut V1) = x
        rw [MulEquiv.symm_apply_apply]⟩
  rw [hr] at hg
  refine ⟨g, ?_⟩
  letI : Finite octa := Finite.of_equiv (Perm (Fin 4)) octa_group.some.symm.toEquiv
  apply Subgroup.eq_of_le_of_card_ge hg
  have ec := (G.equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e
  exact (Nat.card_congr octa_group.some.toEquiv).trans (Nat.card_congr ec.toEquiv).symm |>.le

/-- B2 from the three state-theoretic inputs only. -/
theorem solvableExceptionalOrbifoldC2Fact_of_three_inputs
    (hs : TetrahedralVirasoroSpan) (hr : TetrahedralModeDecomposition)
    (hI : InvolutionMovingPairSpan) : SolvableExceptionalOrbifoldC2Fact :=
  solvableExceptionalOrbifoldC2Fact_of_state_inputs
    tetrahedralConjugacy octahedralConjugacy hs hr hI

end VOA.Classification.COne.OrbC2d
