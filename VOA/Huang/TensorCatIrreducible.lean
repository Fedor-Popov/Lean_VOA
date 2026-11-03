import VOA.Huang.TensorCatDecomposition

/-! # Four-point convergence and range equality for irreducible external modules

All represented intertwiners are covered, including an arbitrary ordinary
intermediate fusion object. Faithfulness and extension to reducible external
modules remain separate obligations of `OrdinaryFourPointInput`.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.AssocConverse VOA.Huang.AssocTarget
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W) (hV : StronglyRational W)
variable {ι : Type u} (R : ι → LWModule W) (iR : ∀ i, (R i).IsIrreducibleLW)
    (hR : FiniteTargets R)
variable {P₁ P₂ P₃ P₄ : LWModule W}
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
include hV iR hR i₁ i₂ i₃ i₄

theorem iterateSpace_summable
    (I : IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod)) (d : TestData P₁ P₂ P₃ P₄) :
    Summable (iterateWeightTerm F I (ordinaryTest d)) := by
  obtain ⟨r, C, rfl⟩ := iterateSpace_finite_channels F R iR (hR _ _) I
  change Summable (fun w => iterateWeightTerm F (∑ j, representedIterate F
    (C j).outer (C j).inner) (ordinaryTest d) w)
  simp_rw [iterateWeightTerm_sum]
  exact summable_sum (fun j _ => representedIterate_summable F hV i₁ i₂ i₃ i₄ _ _ d)

theorem productSpace_summable
    (I : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod)) (d : TestData P₁ P₂ P₃ P₄) :
    Summable (productWeightTerm F I (ordinaryTest d)) := by
  obtain ⟨r, C, rfl⟩ := productSpace_finite_channels F R iR (hR _ _) I
  change Summable (fun w => productWeightTerm F (∑ j, representedProduct F
    (C j).left (C j).right) (ordinaryTest d) w)
  simp_rw [productWeightTerm_sum]
  exact summable_sum (fun j _ => representedProduct_summable F hV i₁ i₂ i₃ i₄ _ _ d)

/-- Transport of every represented iterate, not just a single simple channel. -/
theorem productSpace_of_iterateSpace (ha : AssociativityBoth W)
    (I : IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod)) :
    ∃ J : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod),
      productEvaluation F J = iterateEvaluation F I := by
  classical
  obtain ⟨r, C, rfl⟩ := iterateSpace_finite_channels F R iR (hR _ _) I
  choose J hs he using fun j => representedProduct_of_iterateChannel F hV ha i₁ i₂ i₃ i₄ (C j)
  refine ⟨∑ j, J j, ?_⟩
  funext d
  obtain ⟨d, rfl⟩ := ordinaryTest_surjective d
  rw [productEvaluation_sum F J _ (fun j => hs j d),
    iterateEvaluation_sum F _ _ (fun j => representedIterate_summable F hV i₁ i₂ i₃ i₄ _ _ d)]
  exact Finset.sum_congr rfl (fun j _ => he j d)

/-- Transport of every represented product in the reverse direction. -/
theorem iterateSpace_of_productSpace (ha : AssociativityBoth W)
    (I : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod)) :
    ∃ J : IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod),
      iterateEvaluation F J = productEvaluation F I := by
  classical
  obtain ⟨r, C, rfl⟩ := productSpace_finite_channels F R iR (hR _ _) I
  choose J hs he using fun j => representedIterate_of_productChannel F hV ha i₁ i₂ i₃ i₄ (C j)
  refine ⟨∑ j, J j, ?_⟩
  funext d
  obtain ⟨d, rfl⟩ := ordinaryTest_surjective d
  rw [iterateEvaluation_sum F J _ (fun j => hs j d),
    productEvaluation_sum F _ _ (fun j => representedProduct_summable F hV i₁ i₂ i₃ i₄ _ _ d)]
  exact Finset.sum_congr rfl (fun j _ => he j d)

/-- Equality of ranges on every scalar test, with arbitrary ordinary intermediate objects. -/
theorem irreducible_fourPoint_range_eq (ha : AssociativityBoth W) :
    Set.range (iterateEvaluation F (X := Ordinary.of P₁.isMod) (Y := Ordinary.of P₂.isMod)
      (Z := Ordinary.of P₃.isMod) (T := Ordinary.of P₄.isMod)) =
    Set.range (productEvaluation F (X := Ordinary.of P₁.isMod) (Y := Ordinary.of P₂.isMod)
      (Z := Ordinary.of P₃.isMod) (T := Ordinary.of P₄.isMod)) := by
  ext f
  constructor
  · rintro ⟨I, rfl⟩
    exact productSpace_of_iterateSpace F hV R iR hR i₁ i₂ i₃ i₄ ha I
  · rintro ⟨I, rfl⟩
    exact iterateSpace_of_productSpace F hV R iR hR i₁ i₂ i₃ i₄ ha I

omit iR hR in
/-- The proved strong-rationality specialization. It uses the theorem `VOA.pbw`; no project
axiom. -/
theorem irreducible_fourPoint_convergence_range_pbw :
    (∀ (d : FourPointTest (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
        (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod)),
      (∀ I : IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
          (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod), Summable (iterateWeightTerm F I d)) ∧
      (∀ I : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
          (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod), Summable (productWeightTerm F I d))) ∧
    Set.range (iterateEvaluation F (X := Ordinary.of P₁.isMod) (Y := Ordinary.of P₂.isMod)
      (Z := Ordinary.of P₃.isMod) (T := Ordinary.of P₄.isMod)) =
    Set.range (productEvaluation F (X := Ordinary.of P₁.isMod) (Y := Ordinary.of P₂.isMod)
      (Z := Ordinary.of P₃.isMod) (T := Ordinary.of P₄.isMod)) := by
  have hΦ := PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV
  obtain ⟨n, R, iR, hc, _⟩ := exists_completeIrredundantFamily hΦ
  let S : ULift.{u} (Fin n) → LWModule W := fun j => R j.down
  have iS : ∀ j, (S j).IsIrreducibleLW := fun j => iR j.down
  have hcS : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (S j) := by
    intro Q iQ
    obtain ⟨j, hj⟩ := hc Q iQ
    exact ⟨⟨j⟩, hj⟩
  have hS := finiteTargets_of_stronglyRational hV hΦ S hcS
  refine ⟨?_, irreducible_fourPoint_range_eq F hV S iS hS i₁ i₂ i₃ i₄
    (associativityBoth_of_stronglyRational_pbw hV)⟩
  intro d
  obtain ⟨d, rfl⟩ := ordinaryTest_surjective d
  exact ⟨fun I => iterateSpace_summable F hV S iS hS i₁ i₂ i₃ i₄ I d,
    fun I => productSpace_summable F hV S iS hS i₁ i₂ i₃ i₄ I d⟩

end VOA.Huang.TensorCat
