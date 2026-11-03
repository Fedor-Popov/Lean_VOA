import VOA.Huang.TensorCatChannels

/-! # Analytic four-point transport of represented channels

The proved `fourPointEquiv_pbw` produces actual represented intertwiner data
on the other side, preserving every simultaneous scalar test. Summability
of the finite sum is proved. This is channelwise transport; extending it
to every intertwiner on arbitrary reducible external modules, and proving
faithfulness there, remains the ordinary representability obligation.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.AssocConverse VOA.Huang.AssocTarget
open scoped BigOperators
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W) {X Y Z T : Ordinary W} {ι : Type v} [Fintype ι]

theorem iterateWeightTerm_sum (I : ι → IterateSpace F X Y Z T)
    (d : FourPointTest X Y Z T) (w : ℂ) :
    iterateWeightTerm F (∑ j, I j) d w = ∑ j, iterateWeightTerm F (I j) d w := by
  classical
  simp [iterateWeightTerm, Finset.sum_apply, map_sum, Finset.sum_mul]

theorem productWeightTerm_sum (I : ι → ProductSpace F X Y Z T)
    (d : FourPointTest X Y Z T) (w : ℂ) :
    productWeightTerm F (∑ j, I j) d w = ∑ j, productWeightTerm F (I j) d w := by
  classical
  simp [productWeightTerm, Finset.sum_apply, map_sum, Finset.sum_mul]

theorem iterateEvaluation_sum (I : ι → IterateSpace F X Y Z T)
    (d : FourPointTest X Y Z T) (hs : ∀ j, Summable (iterateWeightTerm F (I j) d)) :
    iterateEvaluation F (∑ j, I j) d = ∑ j, iterateEvaluation F (I j) d := by
  simp only [iterateEvaluation, iterateWeightTerm_sum]
  exact Summable.tsum_finsetSum (fun j _ => hs j)

theorem productEvaluation_sum (I : ι → ProductSpace F X Y Z T)
    (d : FourPointTest X Y Z T) (hs : ∀ j, Summable (productWeightTerm F (I j) d)) :
    productEvaluation F (∑ j, I j) d = ∑ j, productEvaluation F (I j) d := by
  simp only [productEvaluation, productWeightTerm_sum]
  exact Summable.tsum_finsetSum (fun j _ => hs j)

variable {P₁ P₂ P₃ P₄ : LWModule W}

/-- Both proved associativity directions transport an actual iterate channel
through the universal property. The target is a single actual intertwiner,
not merely membership in a numerical fusion space. -/
theorem representedProduct_of_iterateChannel (hV : StronglyRational W)
    (ha : AssociativityBoth W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (C : IterateChannel P₁ P₂ P₃ P₄) :
    ∃ J : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
        (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod),
      (∀ d, Summable (productWeightTerm F J (ordinaryTest d))) ∧
      ∀ d, productEvaluation F J (ordinaryTest d) =
        iterateEvaluation F (representedIterate F C.outer C.inner) (ordinaryTest d) := by
  classical
  let v : iterateSpan P₁ P₂ P₃ P₄ := ⟨C.eval, Submodule.subset_span ⟨C, rfl⟩⟩
  obtain ⟨r, cs, heq⟩ := (mem_productSpan_iff _).mp
    (fourPointEquiv ha i₁ i₂ i₃ i₄ v).property
  change C.eval = ∑ j, (cs j).eval at heq
  let J : Fin r → ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod) :=
    fun j => representedProduct F (cs j).left (cs j).right
  have hs (j : Fin r) (d : TestData P₁ P₂ P₃ P₄) :
      Summable (productWeightTerm F (J j) (ordinaryTest d)) :=
    representedProduct_summable F hV i₁ i₂ i₃ i₄ _ _ d
  refine ⟨∑ j, J j, ?_, ?_⟩
  · intro d
    change Summable (fun w => productWeightTerm F (∑ j, J j) (ordinaryTest d) w)
    simp_rw [productWeightTerm_sum]
    exact summable_sum (fun j _ => hs j d)
  · intro d
    rw [productEvaluation_sum F J _ (fun j => hs j d), representedIterate_evaluation]
    simp only [J, representedProduct_evaluation]
    simpa only [Finset.sum_apply] using (congrFun heq d).symm

/-- The channelwise transport using exactly the existing PBW-relative
four-point theorem. No additional analytic input is present here. -/
theorem representedProduct_of_iterateChannel_pbw (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (C : IterateChannel P₁ P₂ P₃ P₄) :
    ∃ J : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
        (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod),
      (∀ d, Summable (productWeightTerm F J (ordinaryTest d))) ∧
      ∀ d, productEvaluation F J (ordinaryTest d) =
        iterateEvaluation F (representedIterate F C.outer C.inner) (ordinaryTest d) :=
  representedProduct_of_iterateChannel F hV
    (associativityBoth_of_stronglyRational_pbw hV) i₁ i₂ i₃ i₄ C

/-- The other direction of represented channel transport, with the same
simultaneous tests and actual summability. -/
theorem representedIterate_of_productChannel (hV : StronglyRational W)
    (ha : AssociativityBoth W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (C : ProductChannel P₁ P₂ P₃ P₄) :
    ∃ J : IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
        (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod),
      (∀ d, Summable (iterateWeightTerm F J (ordinaryTest d))) ∧
      ∀ d, iterateEvaluation F J (ordinaryTest d) =
        productEvaluation F (representedProduct F C.left C.right) (ordinaryTest d) := by
  classical
  have hv : C.eval ∈ productSpan P₁ P₂ P₃ P₄ := Submodule.subset_span ⟨C, rfl⟩
  rw [← fourPointSpans_eq ha i₁ i₂ i₃ i₄] at hv
  obtain ⟨r, cs, heq⟩ := (mem_iterateSpan_iff _).mp hv
  let J : Fin r → IterateSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod)
      (Ordinary.of P₃.isMod) (Ordinary.of P₄.isMod) :=
    fun j => representedIterate F (cs j).outer (cs j).inner
  have hs (j : Fin r) (d : TestData P₁ P₂ P₃ P₄) :
      Summable (iterateWeightTerm F (J j) (ordinaryTest d)) :=
    representedIterate_summable F hV i₁ i₂ i₃ i₄ _ _ d
  refine ⟨∑ j, J j, ?_, ?_⟩
  · intro d
    change Summable (fun w => iterateWeightTerm F (∑ j, J j) (ordinaryTest d) w)
    simp_rw [iterateWeightTerm_sum]
    exact summable_sum (fun j _ => hs j d)
  · intro d
    rw [iterateEvaluation_sum F J _ (fun j => hs j d), representedProduct_evaluation]
    simp only [J, representedIterate_evaluation]
    simpa only [Finset.sum_apply] using (congrFun heq d).symm

end VOA.Huang.TensorCat
