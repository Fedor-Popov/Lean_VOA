import VOA.Huang.TensorCatReducible
import VOA.Huang.TensorCatCoefficient

/-! # Faithfulness of the actual ordinary four-point evaluations

Finite channel decomposition, analytic coefficient uniqueness, and universal
mode spanning prove faithfulness for simple external modules. Finite split
presentations then transfer it to every ordinary external module.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.AssocConverse
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W) (hV : StronglyRational W)
variable {ι : Type u} (R : ι → LWModule W) (iR : ∀ i, (R i).IsIrreducibleLW)
variable {P₁ P₂ P₃ P₄ : LWModule W}
  (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)

include hV iR i₁ i₂ i₃ i₄

/-- Zero analytic product implies zero represented intertwiner. -/
theorem irreducible_productEvaluation_eq_zero
    (hN : FiniteTarget R (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).isMod)
    (I : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod))
    (hI : productEvaluation F I = 0) : I = 0 := by
  classical
  obtain ⟨r, C, rfl⟩ := productSpace_finite_channels F R iR hN I
  have hv (d : TestData P₁ P₂ P₃ P₄) :
      ∑ j, productValue (C j).left (C j).right d = 0 := by
    have hh := congrFun hI (ordinaryTest d)
    rw [productEvaluation_sum F _ _ (fun j =>
      representedProduct_summable F hV i₁ i₂ i₃ i₄ _ _ d)] at hh
    simpa only [representedProduct_evaluation, Pi.zero_apply] using hh
  have hf := formal_products_zero_of_values_zero hV i₁ i₂ i₃ i₄
    (fun j => (C j).Q) (fun j => (C j).left) (fun j => (C j).right) hv
  apply Subtype.ext
  funext p
  apply LinearMap.ext
  intro x
  apply tensor_linear_ext (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod))
  intro q y z
  simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
  have he (j : Fin r) : (representedProduct F (C j).left (C j).right).val p x
      ((F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).intertwiner.val q y z) =
      (C j).left.val p x ((C j).right.val q y z) := by
    have hh := congrArg (fun J => J.val q y z)
      ((F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).lift_spec _ (C j).right)
    exact congrArg ((C j).left.val p x) hh
  simp_rw [he]
  exact hf p q x y z

/-- Zero analytic iterate implies zero represented intertwiner. -/
theorem irreducible_iterateEvaluation_eq_zero
    (hN : FiniteTarget R (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).isMod)
    (I : IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod))
    (hI : iterateEvaluation F I = 0) : I = 0 := by
  classical
  obtain ⟨r, C, rfl⟩ := iterateSpace_finite_channels F R iR hN I
  have hv (d : TestData P₁ P₂ P₃ P₄) :
      ∑ j, iterateValue (C j).outer (C j).inner d = 0 := by
    have hh := congrFun hI (ordinaryTest d)
    rw [iterateEvaluation_sum F _ _ (fun j =>
      representedIterate_summable F hV i₁ i₂ i₃ i₄ _ _ d)] at hh
    simpa only [representedIterate_evaluation, Pi.zero_apply] using hh
  have hf := formal_iterates_zero_of_values_zero hV i₁ i₂ i₃ i₄
    (fun j => (C j).Q) (fun j => (C j).outer) (fun j => (C j).inner) hv
  apply Subtype.ext
  funext q
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro z
  let J := ∑ j, representedIterate F (C j).outer (C j).inner
  have hz : (J.val q).flip z = 0 := by
    apply tensor_linear_ext (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod))
    intro p x y
    change J.val q ((F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).intertwiner.val p x y) z = 0
    dsimp only [J]
    simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
    have he (j : Fin r) : (representedIterate F (C j).outer (C j).inner).val q
        ((F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).intertwiner.val p x y) z =
        (C j).outer.val q ((C j).inner.val p x y) z := by
      have hh := congrArg (fun J => J.val p x y)
        ((F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).lift_spec _ (C j).inner)
      exact congrArg (fun w => (C j).outer.val q w z) hh
    simp_rw [he]
    exact hf p q x y z
  exact congrArg (fun k : (F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)).carrier →ₗ[ℂ]
    P₄.carrier => k v) hz

/-- The irreducible evaluation maps are injective; the intermediate modules
are arbitrary ordinary fusion objects. -/
theorem irreducible_fourPoint_faithful (hs : OrdinaryFourPointSummability F)
    (hR : FiniteTargets R) :
    Function.Injective (iterateEvaluation F (X := Ordinary.of P₁.isMod)
      (Y := Ordinary.of P₂.isMod) (Z := Ordinary.of P₃.isMod) (T := Ordinary.of P₄.isMod)) ∧
    Function.Injective (productEvaluation F (X := Ordinary.of P₁.isMod)
      (Y := Ordinary.of P₂.isMod) (Z := Ordinary.of P₃.isMod) (T := Ordinary.of P₄.isMod)) := by
  constructor
  · change Function.Injective (iterateEvaluationLinear F hs _ _ _ _)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun I hI => irreducible_iterateEvaluation_eq_zero F hV R iR i₁ i₂ i₃ i₄ (hR _ _) I hI
  · change Function.Injective (productEvaluationLinear F hs _ _ _ _)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun I hI => irreducible_productEvaluation_eq_zero F hV R iR i₁ i₂ i₃ i₄ (hR _ _) I hI

omit iR i₁ i₂ i₃ i₄

variable {X Y Z T : Ordinary W}
  (A : SimplePresentation X) (B : SimplePresentation Y)
  (C : SimplePresentation Z) (D : SimplePresentation T)

omit hV in
/-- Faithfulness transfers through the actual finite external presentations. -/
theorem fourPoint_faithful_of_presentations
    (H : ∀ j : ExternalIndex A B C D,
      Function.Injective (iterateEvaluation F (X := Ordinary.of (A.part j.1).isMod)
        (Y := Ordinary.of (B.part j.2.1).isMod) (Z := Ordinary.of (C.part j.2.2.1).isMod)
        (T := Ordinary.of (D.part j.2.2.2).isMod)) ∧
      Function.Injective (productEvaluation F (X := Ordinary.of (A.part j.1).isMod)
        (Y := Ordinary.of (B.part j.2.1).isMod) (Z := Ordinary.of (C.part j.2.2.1).isMod)
        (T := Ordinary.of (D.part j.2.2.2).isMod))) :
    Function.Injective (iterateEvaluation F (X := X) (Y := Y) (Z := Z) (T := T)) ∧
    Function.Injective (productEvaluation F (X := X) (Y := Y) (Z := Z) (T := T)) := by
  constructor
  · intro I J hIJ
    have he (j : ExternalIndex A B C D) :
        iterateComponent F A B C D I j = iterateComponent F A B C D J j := by
      apply (H j).1
      funext d
      simp only [iterateComponent, iterateEvaluation_map]
      exact congrFun hIJ _
    rw [← iterate_reassemble F A B C D I, ← iterate_reassemble F A B C D J]
    simp_rw [he]
  · intro I J hIJ
    have he (j : ExternalIndex A B C D) :
        productComponent F A B C D I j = productComponent F A B C D J j := by
      apply (H j).2
      funext d
      simp only [productComponent, productEvaluation_map]
      exact congrFun hIJ _
    rw [← product_reassemble F A B C D I, ← product_reassemble F A B C D J]
    simp_rw [he]

/-- Strong rationality proves ordinary four-point faithfulness, relative to PBW. -/
theorem ordinaryFourPointFaithfulness_pbw : OrdinaryFourPointFaithfulness F := by
  have hΦ := PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV
  obtain ⟨n, R, iR, hc, _⟩ := exists_completeIrredundantFamily hΦ
  let S : ULift.{u} (Fin n) → LWModule W := fun j => R j.down
  have hcS : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (S j) := by
    intro Q iQ
    obtain ⟨j, hj⟩ := hc Q iQ
    exact ⟨⟨j⟩, hj⟩
  have hS := finiteTargets_of_stronglyRational hV hΦ S hcS
  intro X Y Z T
  obtain ⟨A⟩ := simplePresentation_nonempty hV hΦ X
  obtain ⟨B⟩ := simplePresentation_nonempty hV hΦ Y
  obtain ⟨C⟩ := simplePresentation_nonempty hV hΦ Z
  obtain ⟨D⟩ := simplePresentation_nonempty hV hΦ T
  apply fourPoint_faithful_of_presentations F A B C D
  intro j
  exact irreducible_fourPoint_faithful F hV S (fun j => iR j.down)
    (A.irreducible j.1) (B.irreducible j.2.1) (C.irreducible j.2.2.1)
    (D.irreducible j.2.2.2) (ordinaryFourPointSummability_pbw F hV) hS

/-- All three fields of the ordinary four-point input are proved. -/
theorem ordinaryFourPointInput_pbw : OrdinaryFourPointInput F :=
  ordinaryFourPointInput_of_faithfulness_pbw F hV (ordinaryFourPointFaithfulness_pbw F hV)

/-- Actual ordinary-module reassociation follows, with no analytic input left. -/
theorem reassociationInput_of_stronglyRational_pbw : ReassociationInput F :=
  reassociationInput_of_evaluation F (ordinaryFourPointInput_pbw F hV)

end VOA.Huang.TensorCat
