import VOA.Huang.TensorCatFaithful

/-! # Absolute convergence and the five sewing edges

This file proves the Fubini step, including the exchange of the two internal
weights on the last edge. It does not infer joint convergence from convergence
of individual slices. The remaining estimate is explicitly the summability
of the sums of norms of the slices.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- The exact norm estimate needed to pass from slice convergence to joint
absolute convergence. Expected for the five actual expansions on their common chart. -/
def FivePointNormFibers : Prop :=
  ∀ (X Y Z T U : Ordinary W) (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U),
    (∀ w : ℂ, Summable (fun v : ℂ => ‖fivePointTerm F b k d (w, v)‖)) ∧
    Summable (fun w : ℂ => ∑' v : ℂ, ‖fivePointTerm F b k d (w, v)‖)

/-- The unspecialized joint convergence target, independent of an associator. -/
def FivePointSummability : Prop :=
  ∀ (X Y Z T U : Ordinary W) (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U), Summable (fivePointTerm F b k d)

/-- For complex scalar sums the norm-fiber criterion is equivalent to joint
summability. In particular the second bound cannot simply be omitted. -/
theorem fivePointSummability_iff_normFibers :
    FivePointSummability F ↔ FivePointNormFibers F := by
  constructor
  · intro hs X Y Z T U b k d
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mp (hs X Y Z T U b k d).norm
  · intro hs X Y Z T U b k d
    exact Summable.of_norm ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      (hs X Y Z T U b k d))

variable {X Y Z T U : Ordinary W}

/-- Fubini in the first internal-weight order. -/
theorem fivePointEvaluation_fubini (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (hs : Summable (fivePointTerm F b k d)) :
    fivePointEvaluation F b k d = ∑' w : ℂ, ∑' v : ℂ, fivePointTerm F b k d (w, v) :=
  hs.tsum_prod

/-- Fubini in the other internal-weight order. -/
theorem fivePointEvaluation_fubini_swap (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (hs : Summable (fivePointTerm F b k d)) :
    fivePointEvaluation F b k d = ∑' v : ℂ, ∑' w : ℂ, fivePointTerm F b k d (w, v) := by
  rw [fivePointEvaluation_fubini F b k d hs]
  exact (Summable.tsum_comm (f := fun w v => fivePointTerm F b k d (w, v)) hs).symm

variable (a : AssociatorFamily F)

/-- Individual four-point identities with the unaffected internal weight fixed.
The last edge keeps the Z--T weight, which changes index position. These are
analytic normalization obligations for the actual associator, not path equalities. -/
structure FivePointFiberEdges : Prop where
  edge01 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .inner ⟶ U)
      (d : FivePointTest X Y Z T U) (v : ℂ) :
    (∑' w : ℂ, fivePointTerm F .left (fiveEdge01 F X Y Z T a ≫ k) d (w, v)) =
      ∑' w : ℂ, fivePointTerm F .inner k d (w, v)
  edge12 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .middle ⟶ U)
      (d : FivePointTest X Y Z T U) (w : ℂ) :
    (∑' v : ℂ, fivePointTerm F .inner (fiveEdge12 F X Y Z T a ≫ k) d (w, v)) =
      ∑' v : ℂ, fivePointTerm F .middle k d (w, v)
  edge23 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .right ⟶ U)
      (d : FivePointTest X Y Z T U) (v : ℂ) :
    (∑' w : ℂ, fivePointTerm F .middle (fiveEdge23 F X Y Z T a ≫ k) d (w, v)) =
      ∑' w : ℂ, fivePointTerm F .right k d (w, v)
  edge04 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .pair ⟶ U)
      (d : FivePointTest X Y Z T U) (w : ℂ) :
    (∑' v : ℂ, fivePointTerm F .left (fiveEdge04 F X Y Z T a ≫ k) d (w, v)) =
      ∑' v : ℂ, fivePointTerm F .pair k d (w, v)
  edge43 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .right ⟶ U)
      (d : FivePointTest X Y Z T U) (v : ℂ) :
    (∑' w : ℂ, fivePointTerm F .pair (fiveEdge43 F X Y Z T a ≫ k) d (w, v)) =
      ∑' w : ℂ, fivePointTerm F .right k d (v, w)

/-- Joint absolute convergence justifies integrating each single-edge identity. -/
theorem fivePointEdges_of_fibers (hs : FivePointSummability F)
    (he : FivePointFiberEdges F a) : FivePointEdges F a where
  edge01 X Y Z T U k := by
    funext d
    rw [fivePointEvaluation_fubini_swap F _ _ d (hs _ _ _ _ _ _ _ d),
      fivePointEvaluation_fubini_swap F _ _ d (hs _ _ _ _ _ _ _ d)]
    exact tsum_congr (he.edge01 X Y Z T U k d)
  edge12 X Y Z T U k := by
    funext d
    rw [fivePointEvaluation_fubini F _ _ d (hs _ _ _ _ _ _ _ d),
      fivePointEvaluation_fubini F _ _ d (hs _ _ _ _ _ _ _ d)]
    exact tsum_congr (he.edge12 X Y Z T U k d)
  edge23 X Y Z T U k := by
    funext d
    rw [fivePointEvaluation_fubini_swap F _ _ d (hs _ _ _ _ _ _ _ d),
      fivePointEvaluation_fubini_swap F _ _ d (hs _ _ _ _ _ _ _ d)]
    exact tsum_congr (he.edge23 X Y Z T U k d)
  edge04 X Y Z T U k := by
    funext d
    rw [fivePointEvaluation_fubini F _ _ d (hs _ _ _ _ _ _ _ d),
      fivePointEvaluation_fubini F _ _ d (hs _ _ _ _ _ _ _ d)]
    exact tsum_congr (he.edge04 X Y Z T U k d)
  edge43 X Y Z T U k := by
    funext d
    rw [fivePointEvaluation_fubini_swap F _ _ d (hs _ _ _ _ _ _ _ d),
      fivePointEvaluation_fubini F _ _ d (hs _ _ _ _ _ _ _ d)]
    exact tsum_congr (he.edge43 X Y Z T U k d)

/-- The remaining five-point coefficient uniqueness, separated from convergence
and from the single-edge identities. -/
def FivePointLeftFaithfulness : Prop :=
  ∀ X Y Z T U : Ordinary W,
    Function.Injective (fivePointEvaluation F (X := X) (Y := Y) (Z := Z) (T := T) (U := U) .left)

/-- Explicit norm estimates, uniqueness, and the single-weight edge identities
suffice for the original sewing input. None is assumed as an axiom. -/
theorem fivePointSewingInput_of_normFibers (hn : FivePointNormFibers F)
    (hf : FivePointLeftFaithfulness F) (he : FivePointFiberEdges F a) :
    FivePointSewingInput F a where
  summability := (fivePointSummability_iff_normFibers F).mpr hn
  faithful := hf
  edges := fivePointEdges_of_fibers F a ((fivePointSummability_iff_normFibers F).mpr hn) he

/-- With four-point analysis discharged, only sewing and vacuum normalization
remain in the monoidal construction. This is still conditional. -/
abbrev monoidalCategoryOfStronglyRationalSewing (hV : StronglyRational W)
    (hs : FivePointSewingInput F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators)
    (hv : VacuumCreationCompatibility F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators) :
    MonoidalCategory (Ordinary W) :=
  monoidalCategoryOfEvaluation F (ordinaryFourPointInput_pbw F hV) hs hv

end VOA.Huang.TensorCat
