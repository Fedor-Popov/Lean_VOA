import VOA.Huang.TensorCatExternal

/-! # Four-point convergence and range equality for all ordinary modules

Finite reconstruction in the external variables extends the irreducible
four-point theorem without assuming faithfulness or choosing an associator.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- Convergence and equality of ranges at fixed external modules.
Injectivity is deliberately separate. -/
structure FourPointConvergenceRange (X Y Z T : Ordinary W) : Prop where
  iterate_summable (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    Summable (iterateWeightTerm F I d)
  product_summable (I : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) :
    Summable (productWeightTerm F I d)
  range_eq : Set.range (iterateEvaluation F (X := X) (Y := Y) (Z := Z) (T := T)) =
    Set.range (productEvaluation F (X := X) (Y := Y) (Z := Z) (T := T))

variable {X Y Z T : Ordinary W}
  (A : SimplePresentation X) (B : SimplePresentation Y)
  (C : SimplePresentation Z) (D : SimplePresentation T)
  (H : ∀ j : ExternalIndex A B C D,
    FourPointConvergenceRange F (Ordinary.of (A.part j.1).isMod)
      (Ordinary.of (B.part j.2.1).isMod) (Ordinary.of (C.part j.2.2.1).isMod)
      (Ordinary.of (D.part j.2.2.2).isMod))
include H

/-- Absolute convergence is stable under finite external decomposition. -/
theorem iterate_summable_of_presentations (I : IterateSpace F X Y Z T)
    (d : FourPointTest X Y Z T) : Summable (iterateWeightTerm F I d) := by
  rw [← iterate_reassemble F A B C D I]
  change Summable (fun w => iterateWeightTerm F (∑ j : ExternalIndex A B C D,
    iterateMap F (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1) (D.inc j.2.2.2)
      (iterateComponent F A B C D I j)) d w)
  simp_rw [iterateWeightTerm_sum]
  apply summable_sum
  intro j _
  exact ((H j).iterate_summable
    (iterateComponent F A B C D I j) ((d.inputs (A.proj j.1) (B.proj j.2.1)
      (C.proj j.2.2.1)).output (D.inc j.2.2.2))).congr
        (fun w => (iterateWeightTerm_map F _ _ _ _ _ d w).symm)


theorem product_summable_of_presentations (I : ProductSpace F X Y Z T)
    (d : FourPointTest X Y Z T) : Summable (productWeightTerm F I d) := by
  rw [← product_reassemble F A B C D I]
  change Summable (fun w => productWeightTerm F (∑ j : ExternalIndex A B C D,
    productMap F (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1) (D.inc j.2.2.2)
      (productComponent F A B C D I j)) d w)
  simp_rw [productWeightTerm_sum]
  apply summable_sum
  intro j _
  exact ((H j).product_summable
    (productComponent F A B C D I j) ((d.inputs (A.proj j.1) (B.proj j.2.1)
      (C.proj j.2.2.1)).output (D.inc j.2.2.2))).congr
        (fun w => (productWeightTerm_map F _ _ _ _ _ d w).symm)


/-- Simultaneous transport on all scalar tests survives finite external sums. -/
theorem product_of_iterate_presentations (I : IterateSpace F X Y Z T) :
    ∃ J : ProductSpace F X Y Z T, productEvaluation F J = iterateEvaluation F I := by
  classical
  have hc (j : ExternalIndex A B C D) : ∃ J,
      productEvaluation F J = iterateEvaluation F (iterateComponent F A B C D I j) := by
    have hm : iterateEvaluation F (iterateComponent F A B C D I j) ∈
        Set.range (iterateEvaluation F) := ⟨_, rfl⟩
    rw [(H j).range_eq] at hm
    exact hm
  choose J hJ using hc
  let K (j : ExternalIndex A B C D) :=
    productMap F (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1) (D.inc j.2.2.2) (J j)
  refine ⟨∑ j, K j, ?_⟩
  funext d
  have hK (j : ExternalIndex A B C D) : Summable (productWeightTerm F (K j) d) := by
    exact ((H j).product_summable (J j)
      ((d.inputs (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1)).output
        (D.inc j.2.2.2))).congr (fun w => (productWeightTerm_map F _ _ _ _ _ d w).symm)
  rw [productEvaluation_sum F K d hK]
  conv_rhs => rw [← iterate_reassemble F A B C D I]
  rw [iterateEvaluation_sum F _ d (fun j => by
    exact ((H j).iterate_summable (iterateComponent F A B C D I j)
      ((d.inputs (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1)).output
        (D.inc j.2.2.2))).congr (fun w => (iterateWeightTerm_map F _ _ _ _ _ d w).symm))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [K, productEvaluation_map, iterateEvaluation_map]
  exact congrFun (hJ j) _

theorem iterate_of_product_presentations (I : ProductSpace F X Y Z T) :
    ∃ J : IterateSpace F X Y Z T, iterateEvaluation F J = productEvaluation F I := by
  classical
  have hc (j : ExternalIndex A B C D) : ∃ J,
      iterateEvaluation F J = productEvaluation F (productComponent F A B C D I j) := by
    have hm : productEvaluation F (productComponent F A B C D I j) ∈
        Set.range (productEvaluation F) := ⟨_, rfl⟩
    rw [← (H j).range_eq] at hm
    exact hm
  choose J hJ using hc
  let K (j : ExternalIndex A B C D) :=
    iterateMap F (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1) (D.inc j.2.2.2) (J j)
  refine ⟨∑ j, K j, ?_⟩
  funext d
  have hK (j : ExternalIndex A B C D) : Summable (iterateWeightTerm F (K j) d) := by
    exact ((H j).iterate_summable (J j)
      ((d.inputs (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1)).output
        (D.inc j.2.2.2))).congr (fun w => (iterateWeightTerm_map F _ _ _ _ _ d w).symm)
  rw [iterateEvaluation_sum F K d hK]
  conv_rhs => rw [← product_reassemble F A B C D I]
  rw [productEvaluation_sum F _ d (fun j => by
    exact ((H j).product_summable (productComponent F A B C D I j)
      ((d.inputs (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1)).output
        (D.inc j.2.2.2))).congr (fun w => (productWeightTerm_map F _ _ _ _ _ d w).symm))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [K, productEvaluation_map, iterateEvaluation_map]
  exact congrFun (hJ j) _

/-- Finite external decomposition discharges both convergence and range equality. -/
theorem fourPointConvergenceRange_of_presentations : FourPointConvergenceRange F X Y Z T where
  iterate_summable := iterate_summable_of_presentations F A B C D H
  product_summable := product_summable_of_presentations F A B C D H
  range_eq := by
    ext f
    constructor
    · rintro ⟨I, rfl⟩
      exact product_of_iterate_presentations F A B C D H I
    · rintro ⟨I, rfl⟩
      exact iterate_of_product_presentations F A B C D H I

omit H in
/-- Strong rationality supplies all external presentations and all simple-channel
analytic inputs. This extends the irreducible case to arbitrary ordinary modules. -/
theorem ordinary_fourPoint_convergence_range_pbw (hV : StronglyRational W)
    (X Y Z T : Ordinary W) : FourPointConvergenceRange F X Y Z T := by
  have hΦ := PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV
  obtain ⟨A⟩ := simplePresentation_nonempty hV hΦ X
  obtain ⟨B⟩ := simplePresentation_nonempty hV hΦ Y
  obtain ⟨C⟩ := simplePresentation_nonempty hV hΦ Z
  obtain ⟨D⟩ := simplePresentation_nonempty hV hΦ T
  apply fourPointConvergenceRange_of_presentations F A B C D
  intro j
  obtain ⟨hs, he⟩ := irreducible_fourPoint_convergence_range_pbw F hV
    (A.irreducible j.1) (B.irreducible j.2.1)
    (C.irreducible j.2.2.1) (D.irreducible j.2.2.2)
  exact ⟨fun I d => (hs d).1 I, fun I d => (hs d).2 I, he⟩

omit H in
theorem ordinaryFourPointSummability_pbw (hV : StronglyRational W) :
    OrdinaryFourPointSummability F := by
  intro X Y Z T d
  have h := ordinary_fourPoint_convergence_range_pbw F hV X Y Z T
  exact ⟨fun I => h.iterate_summable I d, fun I => h.product_summable I d⟩

omit H in
theorem ordinaryFourPointRangeEquality_pbw (hV : StronglyRational W) :
    OrdinaryFourPointRangeEquality F :=
  fun X Y Z T => (ordinary_fourPoint_convergence_range_pbw F hV X Y Z T).range_eq

omit H in
/-- Faithfulness is the sole remaining field of the ordinary four-point input. -/
theorem ordinaryFourPointInput_of_faithfulness_pbw (hV : StronglyRational W)
    (hf : OrdinaryFourPointFaithfulness F) : OrdinaryFourPointInput F :=
  ⟨ordinaryFourPointSummability_pbw F hV, hf, ordinaryFourPointRangeEquality_pbw F hV⟩

end VOA.Huang.TensorCat
