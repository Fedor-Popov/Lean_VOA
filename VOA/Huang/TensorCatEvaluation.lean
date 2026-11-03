import VOA.Huang.TensorCatFourPoint

/-! # Ordinary four-point evaluations and their naturality

These are scalar matrix coefficients at the real overlap coordinates
`z₂ = 1`, `z₁ = 1 + x`, `0 < x < 1`. The sum is indexed by the
intermediate conformal weight, so coincident simple-channel weights are
collected, never counted twice. No decomposition or basis is chosen.

Summability, faithfulness, and equality of the two ranges are separate,
substantive residuals. They are the ordinary-module extension of Huang's
four-point theorem (Huang 2005; HLZ VI, arXiv:1012.4202). Naturality is proved
directly from the coefficients, including all three input variables.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Homogeneous tests on arbitrary ordinary modules, with a supported dual vector. -/
structure FourPointTest (X Y Z T : Ordinary W) where
  α : ℂ
  β : ℂ
  γ : ℂ
  δ : ℂ
  x : X.carrier
  y : Y.carrier
  z : Z.carrier
  functional : T.carrier →ₗ[ℂ] ℂ
  hx : x ∈ X.isMod.weight α
  hy : y ∈ Y.isMod.weight β
  hz : z ∈ Z.isMod.weight γ
  supported : SupportedAt T.isMod functional δ
  coordinate : ℝ
  positive : 0 < coordinate
  less_one : coordinate < 1

variable {X Y Z T U X' Y' Z' : Ordinary W}

/-- Pull the output functional back along an actual module morphism. -/
def FourPointTest.output (d : FourPointTest X Y Z U) (f : T ⟶ U) :
    FourPointTest X Y Z T :=
  { d with
    functional := d.functional.comp f.val
    supported := fun α hα _ hx => d.supported α hα _ (hom_mem_weight f.property hx) }

/-- Push the three input vectors forward. Their weights are preserved. -/
def FourPointTest.inputs (d : FourPointTest X Y Z T)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') : FourPointTest X' Y' Z' T :=
  { d with
    x := f.val d.x
    y := g.val d.y
    z := h.val d.z
    hx := hom_mem_weight f.property d.hx
    hy := hom_mem_weight g.property d.hy
    hz := hom_mem_weight h.property d.hz }

variable (F : FusionChoice W)

abbrev IterateSpace (X Y Z T : Ordinary W) :=
  IntertwiningOperator (F X Y).isMod Z.isMod T.isMod

abbrev ProductSpace (X Y Z T : Ordinary W) :=
  IntertwiningOperator X.isMod (F Y Z).isMod T.isMod

/-- The intermediate-weight summand of the actual iterate. -/
def iterateWeightTerm (I : IterateSpace F X Y Z T)
    (d : FourPointTest X Y Z T) (w : ℂ) : ℂ :=
  d.functional (I.val (w + d.γ - d.δ - 1)
    ((F X Y).intertwiner.val (d.α + d.β - w - 1) d.x d.y) d.z) *
      (d.coordinate : ℂ) ^ (w - d.α - d.β)

/-- The intermediate-weight summand of the actual product. -/
def productWeightTerm (I : ProductSpace F X Y Z T)
    (d : FourPointTest X Y Z T) (w : ℂ) : ℂ :=
  d.functional (I.val (d.α + w - d.δ - 1) d.x
    ((F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z)) *
      (1 + (d.coordinate : ℂ)) ^ (d.δ - d.α - w)

/-- Total scalar evaluation; convergence is asserted separately below. -/
def iterateEvaluation (I : IterateSpace F X Y Z T) (d : FourPointTest X Y Z T) : ℂ :=
  ∑' w : ℂ, iterateWeightTerm F I d w

/-- Total scalar evaluation; convergence is asserted separately below. -/
def productEvaluation (I : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) : ℂ :=
  ∑' w : ℂ, productWeightTerm F I d w

theorem iterateEvaluation_output (I : IterateSpace F X Y Z T) (f : T ⟶ U)
    (d : FourPointTest X Y Z U) :
    iterateEvaluation F (postcompose I U.isMod f) d =
      iterateEvaluation F I (d.output f) := rfl

theorem productEvaluation_output (I : ProductSpace F X Y Z T) (f : T ⟶ U)
    (d : FourPointTest X Y Z U) :
    productEvaluation F (postcompose I U.isMod f) d =
      productEvaluation F I (d.output f) := rfl

theorem iterateEvaluation_inputs (I : IterateSpace F X' Y' Z' T)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : FourPointTest X Y Z T) :
    iterateEvaluation F (restrictInputs (tensorHom F f g) h I) d =
      iterateEvaluation F I (d.inputs f g h) := by
  apply tsum_congr
  intro w
  change d.functional (I.val _ ((tensorHom F f g).val
    ((F X Y).intertwiner.val _ d.x d.y)) (h.val d.z)) * _ = _
  rw [tensorHom_intertwiner]
  rfl

theorem productEvaluation_inputs (I : ProductSpace F X' Y' Z' T)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') (d : FourPointTest X Y Z T) :
    productEvaluation F (restrictInputs f (tensorHom F g h) I) d =
      productEvaluation F I (d.inputs f g h) := by
  apply tsum_congr
  intro w
  change d.functional (I.val _ (f.val d.x) ((tensorHom F g h).val
    ((F Y Z).intertwiner.val _ d.y d.z))) * _ = _
  rw [tensorHom_intertwiner]
  rfl

/-- Absolute convergence on the real four-point overlap, for all ordinary
external modules. Expected under strong rationality, but not proved here. -/
def OrdinaryFourPointSummability : Prop :=
  ∀ (X Y Z T : Ordinary W) (d : FourPointTest X Y Z T),
    (∀ I : IterateSpace F X Y Z T, Summable (iterateWeightTerm F I d)) ∧
    (∀ I : ProductSpace F X Y Z T, Summable (productWeightTerm F I d))

/-- Analytic coefficient uniqueness after insertion of a universal intertwiner.
This is not injectivity of a trace map, nor separation by lowest weights alone. -/
def OrdinaryFourPointFaithfulness : Prop :=
  ∀ X Y Z T : Ordinary W,
    Function.Injective (iterateEvaluation F (X := X) (Y := Y) (Z := Z) (T := T)) ∧
    Function.Injective (productEvaluation F (X := X) (Y := Y) (Z := Z) (T := T))

/-- Equality of the actual ordinary four-point function ranges. This is the
remaining extension/representability step from `fourPointSpans_eq`, not a new
assumption of associator naturality or coherence. -/
def OrdinaryFourPointRangeEquality : Prop := ∀ X Y Z T : Ordinary W,
  Set.range (iterateEvaluation F (X := X) (Y := Y) (Z := Z) (T := T)) =
    Set.range (productEvaluation F (X := X) (Y := Y) (Z := Z) (T := T))

/-- The iterate evaluation is linear once its actual summability is supplied. -/
def iterateEvaluationLinear (hs : OrdinaryFourPointSummability F) (X Y Z T : Ordinary W) :
    IterateSpace F X Y Z T →ₗ[ℂ] (FourPointTest X Y Z T → ℂ) where
  toFun := iterateEvaluation F
  map_add' I J := by
    funext d
    change (∑' w, iterateWeightTerm F (I + J) d w) = _
    have he (w : ℂ) : iterateWeightTerm F (I + J) d w =
        iterateWeightTerm F I d w + iterateWeightTerm F J d w := by
      simp [iterateWeightTerm, map_add, add_mul]
    simp_rw [he]
    exact (hs X Y Z T d).1 I |>.tsum_add ((hs X Y Z T d).1 J)
  map_smul' c I := by
    funext d
    change (∑' w, iterateWeightTerm F (c • I) d w) = _
    have he (w : ℂ) : iterateWeightTerm F (c • I) d w =
        c * iterateWeightTerm F I d w := by
      simp [iterateWeightTerm, map_smul, mul_assoc]
    simp_rw [he]
    exact tsum_mul_left

/-- The product evaluation is linear once its actual summability is supplied. -/
def productEvaluationLinear (hs : OrdinaryFourPointSummability F) (X Y Z T : Ordinary W) :
    ProductSpace F X Y Z T →ₗ[ℂ] (FourPointTest X Y Z T → ℂ) where
  toFun := productEvaluation F
  map_add' I J := by
    funext d
    change (∑' w, productWeightTerm F (I + J) d w) = _
    have he (w : ℂ) : productWeightTerm F (I + J) d w =
        productWeightTerm F I d w + productWeightTerm F J d w := by
      simp [productWeightTerm, map_add, add_mul]
    simp_rw [he]
    exact (hs X Y Z T d).2 I |>.tsum_add ((hs X Y Z T d).2 J)
  map_smul' c I := by
    funext d
    change (∑' w, productWeightTerm F (c • I) d w) = _
    have he (w : ℂ) : productWeightTerm F (c • I) d w =
        c * productWeightTerm F I d w := by
      simp [productWeightTerm, map_smul, mul_assoc]
    simp_rw [he]
    exact tsum_mul_left

end VOA.Huang.TensorCat
