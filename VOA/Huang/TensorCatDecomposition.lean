import VOA.Huang.TensorCatTransport

/-! # Finite channel decomposition of represented intertwiners

An ordinary intermediate fusion object has a finite split presentation by
simple LW modules. This presents every represented intertwiner as a finite
sum of actual channels. Thus transport is not restricted to a single channel.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.AssocConverse
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W) {P₁ P₂ P₃ P₄ : LWModule W}

/-- Factoring a postcomposition returns the original module map. -/
theorem lift_postcompose {X Y T : Ordinary W} (f : tensorObj F X Y ⟶ T) :
    (F X Y).lift T.isMod (postcompose (F X Y).intertwiner T.isMod f) = f := by
  apply ((F X Y).universal T.carrier T.isMod).1
  exact (F X Y).lift_spec _ _

variable {ι : Type u} (R : ι → LWModule W) (iR : ∀ i, (R i).IsIrreducibleLW)
include iR

theorem iterateSpace_finite_channels
    (hN : FiniteTarget R (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).isMod)
    (I : IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod)) :
    ∃ (r : ℕ) (C : Fin r → IterateChannel P₁ P₂ P₃ P₄),
      I = ∑ j, representedIterate F (C j).outer (C j).inner := by
  classical
  obtain ⟨r, lab, inc, proj, ht⟩ := hN
  let C (j : Fin r) : IterateChannel P₁ P₂ P₃ P₄ :=
    ⟨R (lab j), iR (lab j), restrictInputs (inc j) (𝟙 (Ordinary.of P₃.isMod)) I,
      postcompose (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).intertwiner
        (R (lab j)).isMod (proj j)⟩
  refine ⟨r, C, ?_⟩
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
  have hj (j : Fin r) : (representedIterate F (C j).outer (C j).inner).val n x z =
      I.val n ((inc j).val ((proj j).val x)) z := by
    change I.val n ((inc j).val (((F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).lift
      (R (lab j)).isMod (postcompose _ _ (proj j))).val x)) z = _
    erw [lift_postcompose F (X := Ordinary.of P₁.isMod) (Y := Ordinary.of P₂.isMod)
      (T := Ordinary.of (R (lab j)).isMod)]
  simp_rw [hj]
  rw [← LinearMap.sum_apply, ← map_sum, ht]

theorem productSpace_finite_channels
    (hN : FiniteTarget R (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).isMod)
    (I : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod)) :
    ∃ (r : ℕ) (C : Fin r → ProductChannel P₁ P₂ P₃ P₄),
      I = ∑ j, representedProduct F (C j).left (C j).right := by
  classical
  obtain ⟨r, lab, inc, proj, ht⟩ := hN
  let C (j : Fin r) : ProductChannel P₁ P₂ P₃ P₄ :=
    ⟨R (lab j), iR (lab j), restrictInputs (𝟙 (Ordinary.of P₁.isMod)) (inc j) I,
      postcompose (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).intertwiner
        (R (lab j)).isMod (proj j)⟩
  refine ⟨r, C, ?_⟩
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
  have hj (j : Fin r) : (representedProduct F (C j).left (C j).right).val n x z =
      I.val n x ((inc j).val ((proj j).val z)) := by
    change I.val n x ((inc j).val (((F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).lift
      (R (lab j)).isMod (postcompose _ _ (proj j))).val z)) = _
    erw [lift_postcompose F (X := Ordinary.of P₂.isMod) (Y := Ordinary.of P₃.isMod)
      (T := Ordinary.of (R (lab j)).isMod)]
  simp_rw [hj]
  rw [← map_sum, ht]

end VOA.Huang.TensorCat
