import VOA.Classification.COne.OrbPos9Free

/-! # Extracting an irreducible untwisted ambient module

A nonzero map to the restriction of any ordinary V₂-module suffices for the
untwisted DRX alternative. Finite semisimplicity of V₂ extracts a nonzero
simple component, and source irreducibility turns that map into an embedding.
This does not say that every orbifold module has an untwisted lift.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos9
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat CategoryTheory CategoryTheory.Limits
open VOA.Huang.TensorCat.RepPackaging
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Ordinary restriction as an actual functor on module maps. -/
def restrictionFunctor (S : VOASubalgebra W) : Ordinary W ⥤ Ordinary S.toVOA where
  obj X := Ordinary.of (S.restrictOrdVModule X.isMod)
  map f := ⟨f.val, fun v k x => f.property v.1 k x⟩

instance restrictionFunctor_additive (S : VOASubalgebra W) :
    (restrictionFunctor S).Additive where
  map_add := rfl

/-- A nonzero map from an irreducible subalgebra module to an ordinary ambient
module has a nonzero irreducible ambient component. -/
theorem irreducible_untwisted_component (hW : StronglyRational W) (S : VOASubalgebra W)
    (X : Ordinary S.toVOA) (hX : X.isMod.IsIrreducible) (P : Ordinary W)
    (f : X ⟶ (restrictionFunctor S).obj P) (hf : f ≠ 0) :
    ∃ Q : Ordinary W, Q.isMod.IsIrreducible ∧
      ∃ g : X ⟶ (restrictionFunctor S).obj Q, Function.Injective g.val := by
  classical
  obtain ⟨n, R, hR, ⟨e⟩⟩ := semisimple_lw_pbw hW P
  let B : Fin n → Ordinary W := fun j => Ordinary.of (R j).isMod
  let E := restrictionFunctor S
  have hsum : ∑ j : Fin n, (e.hom ≫ biproduct.π B j) ≫
      (biproduct.ι B j ≫ e.inv) = 𝟙 P := by
    calc
      _ = e.hom ≫ (∑ j : Fin n, biproduct.π B j ≫ biproduct.ι B j) ≫ e.inv := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 P := by rw [biproduct.total, Category.id_comp]; exact e.hom_inv_id
  have hex : ∃ j : Fin n, f ≫ E.map (e.hom ≫ biproduct.π B j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    calc
      f = f ≫ E.map (𝟙 P) := by rw [E.map_id]; rfl
      _ = f ≫ E.map (∑ j : Fin n, (e.hom ≫ biproduct.π B j) ≫
          (biproduct.ι B j ≫ e.inv)) := by rw [hsum]
      _ = 0 := by
        rw [Functor.map_sum, Preadditive.comp_sum]
        apply Finset.sum_eq_zero
        intro j _
        rw [E.map_comp, ← Category.assoc, h j, zero_comp]
  obtain ⟨j, hj⟩ := hex
  exact ⟨B j, hR j, f ≫ E.map (e.hom ≫ biproduct.π B j),
    injective_of_irreducible_source hX _ hj⟩

/-- The exact first DRX alternative, assuming only a nonzero map to an arbitrary
ordinary ambient V₂-module. The target need not initially be irreducible. -/
theorem exceptional_untwisted_of_nonzero_map
    (G : Subgroup (Aut (V2m 1 le_rfl)))
    {M T : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    (N : OrdVModule (orbifoldVOA G) M) (hN : N.IsIrreducible)
    (P : OrdVModule (V2m 1 le_rfl) T)
    (f : M →ₗ[ℂ] T) (hf : f ∈ homSpace N ((orbifold G).restrictOrdVModule P))
    (hne : f ≠ 0) :
    ∃ (T' : Type) (_ : AddCommGroup T') (_ : Module ℂ T')
      (Q : OrdVModule (V2m 1 le_rfl) T'), Q.IsIrreducible ∧
      ∃ g : M →ₗ[ℂ] T',
        g ∈ homSpace N ((orbifold G).restrictOrdVModule Q) ∧ Function.Injective g := by
  obtain ⟨Q, hQ, g, hg⟩ := irreducible_untwisted_component
    (V2m_stronglyRational 1 le_rfl) (orbifold G) (Ordinary.of N) hN (Ordinary.of P)
    ⟨f, hf⟩ (fun h => hne (congrArg Subtype.val h))
  exact ⟨Q.carrier, Q.addCommGroup, Q.module, Q.isMod, hQ, g.val, g.property, hg⟩

end VOA.Classification.COne.OrbPos9
