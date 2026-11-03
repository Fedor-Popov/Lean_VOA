import VOA.Huang.GenusTwoPointSepSpatialTraceEvaluation
import VOA.Huang.GenusTwoPointSepEnergyIdentity

/-!
# Finite coordinate transport on insertion vectors

Precomposition by Huang's actual U is an automorphism on bilinear functions
with ANY complex-linear target, in particular formal spatial distributions.
The square-mode formula is proved at arbitrary logarithmic coordinates.
This is insertion transport, not the still missing elliptic collection of
the normal-order expressions in `GenusTwoPointSepFormalTrace`.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

section Bilinear
variable {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- Finite insertion-coordinate transport, valid for formal-series targets. -/
def huangPairEquiv (P₁ P₂ : LWModule W) (t₁ t₂ : ℂ) :
    (P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) ≃ₗ[ℂ]
      (P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) where
  toFun S := S.compl₁₂ (huangU P₁ t₁).toLinearMap (huangU P₂ t₂).toLinearMap
  invFun S := S.compl₁₂ (huangU P₁ t₁).symm.toLinearMap (huangU P₂ t₂).symm.toLinearMap
  left_inv S := by ext x y; simp
  right_inv S := by ext x y; simp
  map_add' S T := by ext x y; rfl
  map_smul' c S := by ext x y; rfl

@[simp] theorem huangPairEquiv_apply (P₁ P₂ : LWModule W) (t₁ t₂ : ℂ)
    (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) (x : P₁.carrier) (y : P₂.carrier) :
    huangPairEquiv P₁ P₂ t₁ t₂ S x y = S (huangU P₁ t₁ x) (huangU P₂ t₂ y) := rfl

/-- Any linear spatial evaluation commutes with the finite insertion change. -/
theorem huangPairEquiv_postcompose {G : Type*} [AddCommGroup G] [Module ℂ G]
    (P₁ P₂ : LWModule W) (t₁ t₂ : ℂ) (ev : F →ₗ[ℂ] G)
    (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] F) :
    huangPairEquiv P₁ P₂ t₁ t₂ (S.compr₂ ev) =
      (huangPairEquiv P₁ P₂ t₁ t₂ S).compr₂ ev := by
  ext x y
  rfl

end Bilinear

/-- The concrete square-mode expression transported to logarithmic coordinate t. -/
def spatialSquareMode (P : LWModule W) (t : ℂ) (a : V) (m : ℤ)
    (x : P.carrier) : P.carrier :=
  huangModeScale m • moduleWeightExp P.isMod t
    (SquareModule.sqMode P.isMod m (huangStateU W a) (moduleWeightExp P.isMod (-t) x))

/-- At arbitrary t, U carries an ordinary descendant to this exact square mode.
All coordinate factors and the inverse weight scaling are retained. -/
theorem huangU_mode_spatialSquare (P : LWModule W) (t : ℂ)
    (a : V) (m : ℤ) (x : P.carrier) :
    huangU P t (mode (P.isMod.YM a) m x) =
      spatialSquareMode P t a m (huangU P t x) := by
  have ht (y : P.carrier) : huangU P t y = moduleWeightExp P.isMod t (huangU P 0 y) := by
    simpa using huangU_add P t 0 y
  rw [ht, huangU_mode_of_squareConjugation P (normalizedSquareConjugation_holds P),
    map_smul, spatialSquareMode, ht, ← moduleWeightExp_add, neg_add_cancel,
    moduleWeightExp_zero]

theorem spatialSquareMode_conjugation (P : LWModule W) (t : ℂ)
    (a : V) (m : ℤ) (x : P.carrier) :
    spatialSquareMode P t a m x =
      huangU P t (mode (P.isMod.YM a) m ((huangU P t).symm x)) := by
  rw [huangU_mode_spatialSquare, LinearEquiv.apply_symm_apply]

/-- The full raw formal distribution is bilinear before evaluation. -/
def rawSpatialTracePair {P₁ P₂ N Q : LWModule W}
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ℂ → ℂ → PowerSeries ℂ) where
  toFun x :=
    { toFun := fun y => rawSpatialTrace Y₁ Y₂ x y
      map_add' := by
        intro y z
        funext a b
        ext n
        simp [rawSpatialTrace, LinearMap.comp_add, gradedTraceOp_add]
      map_smul' := by
        intro c y
        funext a b
        ext n
        simp [rawSpatialTrace, LinearMap.comp_smul, gradedTraceOp_smul] }
  map_add' := by
    intro x y
    ext z a b n
    simp [rawSpatialTrace, LinearMap.add_comp, gradedTraceOp_add]
  map_smul' := by
    intro c x
    ext y a b n
    simp [rawSpatialTrace, LinearMap.smul_comp, gradedTraceOp_smul]

/-- The modified formal trace has finite coefficients even for inhomogeneous U-images. -/
theorem coeff_huangPairEquiv_rawSpatialTrace {P₁ P₂ N Q : LWModule W}
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (t₁ t₂ : ℂ) (x : P₁.carrier) (y : P₂.carrier) (a b : ℂ) (n : ℕ) :
    PowerSeries.coeff n
      (huangPairEquiv P₁ P₂ t₁ t₂ (rawSpatialTracePair Y₁ Y₂) x y a b) =
      productModeTrace Y₁ Y₂ (huangU P₁ t₁ x) (huangU P₂ t₂ y)
        (b - a - 1) (-b - 1) (N.h - W.centralCharge / 24 + n) := by
  exact coeff_rawSpatialTrace Y₁ Y₂ _ _ n a b

/-- The same finite coordinate operation gives the existing evaluated trace. -/
theorem modifiedProductCuspSeries_eq_huangPairEquiv {P₁ P₂ N Q : LWModule W}
    (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) :
    modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho =
      huangPairEquiv P₁ P₂ (Complex.log z₁) (Complex.log z₂)
        (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho) := rfl

end VOA.Huang.GenusTwoPoint.Separate
