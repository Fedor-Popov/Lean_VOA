import VOA.Huang.FivePointSepMiddle
import VOA.Huang.FivePointSepPairTree
import VOA.Huang.UniformConvConsumers

/-!
# Five-point coefficient growth: assembly by pentagon vertex

`FivePointCoefficientGrowth F` (the open analytic input of the pentagon, consumed by
`fivePointNormGrowth_of_coefficientGrowth_pbw`) splits into one statement per pentagon vertex,
`FivePointTreeGrowth F b`. Proved here for strongly rational `W`:

* `fivePointTreeGrowth_right_pbw` — the product vertex `X ⊠ (Y ⊠ (Z ⊠ T))`;
* `fivePointTreeGrowth_inner_pbw` — the vertex `(X ⊠ (Y ⊠ Z)) ⊠ T`, by skew-symmetry at the
  root reduced to products;
* `fivePointTreeGrowth_middle_pbw` — the vertex `X ⊠ ((Y ⊠ Z) ⊠ T)` (iterate-in-product chart);
* `fivePointTreeGrowth_left_pbw` — the vertex `((X ⊠ Y) ⊠ Z) ⊠ T`, by skew-symmetry at the root
  reduced to the middle shape;
* `fivePointTreeGrowth_pair_pbw` — the pair vertex `(X ⊠ Y) ⊠ (Z ⊠ T)`, in the blow-up chart
  (first index `w + v`, second `w`; all external levels attached to the `X`–`Y` collision).

`fivePointCoefficientGrowth_pbw` and `fivePointNormGrowth_pbw`: for strongly rational
`W`, the full five-point coefficient growth and norm growth of the pentagon. Not proved:
`UniformConv.FivePointSeparateFuchsian` (two separate equations per chart), which is a strictly
stronger sufficient condition and is not needed.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.TensorCat VOA.Huang.HuangODEThree
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W)

/-- Local joint growth of the actual five-point array at one pentagon vertex. -/
def FivePointTreeGrowth (b : FiveTree) : Prop :=
  ∀ (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (h h' : ℂ),
    LocalJointGrowth (fun m n => fivePointTerm F b k d (h + m, h' + n))

theorem fivePointCoefficientGrowth_of_trees (h : ∀ b, FivePointTreeGrowth F b) :
    FivePointCoefficientGrowth F :=
  fun X Y Z T U b k d h₁ h₂ => h b X Y Z T U k d h₁ h₂

theorem fivePointTreeGrowth_of_coefficientGrowth (h : FivePointCoefficientGrowth F)
    (b : FiveTree) : FivePointTreeGrowth F b :=
  fun X Y Z T U k d h₁ h₂ => h X Y Z T U b k d h₁ h₂

theorem fivePointTreeGrowth_right (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) : FivePointTreeGrowth F .right :=
  fun _ _ _ _ _ k d h h' => fivePointCoefficientGrowth_right hV hΦ hs k d h h'

theorem fivePointTreeGrowth_inner (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) : FivePointTreeGrowth F .inner :=
  fun _ _ _ _ _ k d h h' => fivePointCoefficientGrowth_inner F hV hΦ hs k d h h'

/-- **The product pentagon vertex has coefficient growth** (strongly rational `W`). -/
theorem fivePointTreeGrowth_right_pbw (hV : StronglyRational W) :
    FivePointTreeGrowth F .right :=
  fivePointTreeGrowth_right F hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV)
    (ordinaryFourPointSummability_pbw F hV)

/-- **The inner pentagon vertex has coefficient growth** (strongly rational `W`). -/
theorem fivePointTreeGrowth_inner_pbw (hV : StronglyRational W) :
    FivePointTreeGrowth F .inner :=
  fivePointTreeGrowth_inner F hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV)
    (ordinaryFourPointSummability_pbw F hV)

theorem fivePointTreeGrowth_middle (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) : FivePointTreeGrowth F .middle :=
  fun _ _ _ _ _ k d h h' => fivePointCoefficientGrowth_middle F hV hΦ hs k d h h'

theorem fivePointTreeGrowth_left (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) : FivePointTreeGrowth F .left :=
  fun _ _ _ _ _ k d h h' => fivePointCoefficientGrowth_left F hV hΦ hs k d h h'

/-- **The middle pentagon vertex has coefficient growth** (strongly rational `W`). -/
theorem fivePointTreeGrowth_middle_pbw (hV : StronglyRational W) :
    FivePointTreeGrowth F .middle :=
  fivePointTreeGrowth_middle F hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV)
    (ordinaryFourPointSummability_pbw F hV)

/-- **The left pentagon vertex has coefficient growth** (strongly rational `W`). -/
theorem fivePointTreeGrowth_left_pbw (hV : StronglyRational W) :
    FivePointTreeGrowth F .left :=
  fivePointTreeGrowth_left F hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV)
    (ordinaryFourPointSummability_pbw F hV)

/-- The pair vertex `(X ⊠ Y) ⊠ (Z ⊠ T)` together with the four other (proved) vertices gives
the full five-point coefficient growth. -/
theorem fivePointCoefficientGrowth_of_pair_pbw (hV : StronglyRational W)
    (hp : FivePointTreeGrowth F .pair) : FivePointCoefficientGrowth F := by
  apply fivePointCoefficientGrowth_of_trees
  intro b
  cases b with
  | left => exact fivePointTreeGrowth_left_pbw F hV
  | inner => exact fivePointTreeGrowth_inner_pbw F hV
  | middle => exact fivePointTreeGrowth_middle_pbw F hV
  | right => exact fivePointTreeGrowth_right_pbw F hV
  | pair => exact hp

/-- Consequence: the five-point norm growth of the pentagon, from the pair vertex alone. -/
theorem fivePointNormGrowth_of_pair_pbw (hV : StronglyRational W)
    (hp : FivePointTreeGrowth F .pair) : FivePointNormGrowth F :=
  fivePointNormGrowth_of_coefficientGrowth_pbw F hV
    (fivePointCoefficientGrowth_of_pair_pbw F hV hp)

theorem fivePointTreeGrowth_pair (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (hs : OrdinaryFourPointSummability F) : FivePointTreeGrowth F .pair :=
  fun _ _ _ _ _ k d h h' => fivePointCoefficientGrowth_pair F hV hΦ hs k d h h'

/-- **The pair pentagon vertex has coefficient growth** (strongly rational `W`). -/
theorem fivePointTreeGrowth_pair_pbw (hV : StronglyRational W) :
    FivePointTreeGrowth F .pair :=
  fivePointTreeGrowth_pair F hV (PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV)
    (ordinaryFourPointSummability_pbw F hV)

/-- **Five-point coefficient growth** for strongly rational `W`: all five pentagon
vertices. -/
theorem fivePointCoefficientGrowth_pbw (hV : StronglyRational W) :
    FivePointCoefficientGrowth F :=
  fivePointCoefficientGrowth_of_pair_pbw F hV (fivePointTreeGrowth_pair_pbw F hV)

/-- **Five-point norm growth** of the pentagon for strongly rational `W`. -/
theorem fivePointNormGrowth_pbw (hV : StronglyRational W) : FivePointNormGrowth F :=
  fivePointNormGrowth_of_coefficientGrowth_pbw F hV (fivePointCoefficientGrowth_pbw F hV)

/-- Joint absolute convergence of all five pentagon expansions (strongly rational `W`). -/
theorem fivePointSummability_pbw (hV : StronglyRational W) : FivePointSummability F :=
  (fivePointSummability_iff_normGrowth_pbw F hV).mpr (fivePointNormGrowth_pbw F hV)

/-- The norm-fiber estimates of the pentagon (strongly rational `W`). -/
theorem fivePointNormFibers_pbw (hV : StronglyRational W) : FivePointNormFibers F :=
  (fivePointSummability_iff_normFibers F).mp (fivePointSummability_pbw F hV)

/-- The five sewing edges follow from their single-weight (fiber) identities alone. -/
theorem fivePointEdges_of_fiberEdges_pbw (hV : StronglyRational W) (a : AssociatorFamily F)
    (he : FivePointFiberEdges F a) : FivePointEdges F a :=
  fivePointEdges_of_fibers F a (fivePointSummability_pbw F hV) he

/-- The five-point sewing input, conditional only on left faithfulness and the single-weight
edge identities (convergence is proved). -/
theorem fivePointSewingInput_pbw (hV : StronglyRational W) (a : AssociatorFamily F)
    (hf : FivePointLeftFaithfulness F) (he : FivePointFiberEdges F a) :
    FivePointSewingInput F a :=
  fivePointSewingInput_of_normFibers F a (fivePointNormFibers_pbw F hV) hf he

/-- `FivePointSeparateFuchsian` (two separate equations per chart) implies every vertex
statement; it is a strictly stronger sufficient condition than what is used here. -/
theorem fivePointTreeGrowth_of_separate (hs : UniformConv.FivePointSeparateFuchsian F)
    (b : FiveTree) : FivePointTreeGrowth F b :=
  fivePointTreeGrowth_of_coefficientGrowth F
    (UniformConv.fivePointCoefficientGrowth_of_separate F hs) b

end VOA.Huang.FivePointSep
