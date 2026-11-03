import VOA.Classification.COne.OrbPos10Monodromy
import VOA.Classification.COne.OrbPos9Regular

/-! # A nonzero test case for the monodromy equation

The regular simple extension action satisfies categorical twistedness for the
identity element. This verifies the equation on the actual multiplication;
it does not assert that every simple action is local.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos10
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat VOA.Huang.HKLRational
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.BraidingSkew
open CategoryTheory MonoidalCategory OrbPos9
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Double braiding disappears after the ambient multiplication because its
vertex operator has integral mode support. -/
theorem ambientMultiplication_monodromy (G : Subgroup (Aut W))
    (F : FusionChoice (orbifoldVOA G)) :
    (braiding F (ambient G) (ambient G)).hom ≫
      (braiding F (ambient G) (ambient G)).hom ≫ ambientMultiplication G F =
        ambientMultiplication G F := by
  apply tensor_hom_ext F
  intro n a b
  rw [← Category.assoc, Ordinary.comp_apply,
    braidingP_monodromy Phase.upper F (ambient G) (ambient G) n a b]
  erw [map_smul]
  rw [ambientMultiplication_intertwiner]
  by_cases hn : ∃ k : ℤ, n = (k : ℂ)
  · obtain ⟨k, rfl⟩ := hn
    have hp : Phase.upper.c (k : ℂ) * Phase.upper.c (k : ℂ) = 1 := by
      change omegaPhase (k : ℂ) * omegaPhase (k : ℂ) = 1
      rw [omegaPhase_sq]
      have harg : -(2 * Real.pi * Complex.I) * ((k : ℂ) + 1) =
          (2 * Real.pi * Complex.I) * ((-(k + 1) : ℤ) : ℂ) := by push_cast; ring
      rw [harg]
      exact tw_int (-(k + 1))
    rw [hp, one_smul]
  · have hz : moduleModes (adjointModule W) n a b = 0 := by
      have hn' : ¬ ∃ k : ℤ, (k : ℂ) = n := fun h =>
        hn (h.imp fun _ hk => hk.symm)
      simp [moduleModes, hn']
    rw [hz]
    change (Phase.upper.c n * Phase.upper.c n) • (0 : V) = 0
    exact smul_zero _

/-- The regular simple action has the identity monodromy label. -/
theorem regularSimpleAction_monodromy
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (E : CanonicalExtensionAlgebra G hSR) :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := E.monoid
    ActionMonodromyThrough G hSR (regularSimpleAction G hSR E).obj
      (regularSimpleAction G hSR E).act 1 := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  have hg : (ambientSymmetry G 1).hom = 𝟙 (ambient G) := by
    apply Ordinary.hom_ext
    intro x
    rfl
  change (braiding _ _ _).hom ≫ (braiding _ _ _).hom ≫
    tensorHom _ (ambientSymmetry G 1).hom (𝟙 (ambient G)) ≫ MonObj.mul = MonObj.mul
  rw [hg, VOA.Huang.TensorCat.tensorHom_id, Category.id_comp, E.mul_eq]
  exact ambientMultiplication_monodromy G _

end VOA.Classification.COne.OrbPos10
