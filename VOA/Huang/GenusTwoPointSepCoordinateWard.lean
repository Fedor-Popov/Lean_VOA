import VOA.Huang.GenusTwoPointSepSquareInsertion
import VOA.Huang.GenusOneModeLinear

/-!
# The remaining coordinate law and its Ward consumer

The named `NormalizedSquareConjugation` is the vertex-module part of Huang
(1.7), using the already implemented Zhu square modes. It is NOT proved here.
Its implication to the U(1) mode law is proved, including the factor for each
integer mode. No such factor may be discarded in a collected Ward identity.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The normalized coordinate operator on V, reusing the library construction. -/
def normalizedStateChange (W : VertexOperatorAlgebra V) : V ≃ₗ[ℂ] V :=
  changeCoord W (fun j => -iterativeLog (logarithmicCoordinate 1) j)

/-- Ordinary weight scaling of the VOA coordinate generator. -/
theorem coordGen_scale (a : ℕ → ℂ) (t : ℂ) (x : V) :
    moduleWeightExp (adjointModule W) t (coordGen W (scaleGenerator (Complex.exp t) a) x) =
      coordGen W a (moduleWeightExp (adjointModule W) t x) := by
  refine FusionTop.induction_weight (adjointModule W) x (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro α x hx
    rw [moduleWeightExp_of_weight (adjointModule W) t hx, map_smul, coordGen_apply,
      coordGen_apply, map_finsum _ (coordGen_support_finite W _ x),
      smul_finsum' _ (coordGen_support_finite W a x)]
    apply finsum_congr
    intro k
    have hm := mode_mem_weight (adjointModule W) W.conformal_mem hx ((k : ℤ) + 1 + 1)
    change mode (W.Y W.conformalVector) ((k : ℤ) + 1 + 1) x ∈
      (adjointModule W).weight (α + (2 : ℤ) - (((k : ℤ) + 1 + 1 : ℤ) : ℂ) - 1) at hm
    rw [map_smul, VertexOperatorAlgebra.L_def,
      moduleWeightExp_of_weight (adjointModule W) t hm]
    simp only [scaleGenerator, smul_smul, ← Complex.exp_nat_mul]
    have he : ((k + 1 : ℕ) : ℂ) * t +
        t * (α + (2 : ℤ) - (((k : ℤ) + 1 + 1 : ℤ) : ℂ) - 1) = t * α := by
      push_cast
      ring
    rw [mul_right_comm, ← Complex.exp_add, he]

private theorem coordGen_neg (a : ℕ → ℂ) :
    coordGen W (fun j => -a j) = -coordGen W a := by
  ext x
  simp [coordGen_apply, neg_smul, finsum_neg_distrib]

/-- The adjoint normalized operator is the same negative exponential as on modules. -/
theorem normalizedStateChange_exp (x : V) :
    normalizedStateChange W x =
      expFun (coordGen_isLocNilp W (iterativeLog (logarithmicCoordinate 1))).neg x := by
  simp only [normalizedStateChange, changeCoord, expEquiv_apply, coordGen_neg]

/-- The actual positive-Virasoro exponential on V obeys the same scaling law. -/
theorem stateCoordinateChange_scale (a : ℕ → ℂ) (t : ℂ) (x : V) :
    moduleWeightExp (adjointModule W) t
        (expFun (coordGen_isLocNilp W (scaleGenerator (Complex.exp t) a)).neg x) =
      expFun (coordGen_isLocNilp W a).neg (moduleWeightExp (adjointModule W) t x) := by
  apply expFun_intertwine (moduleWeightExp (adjointModule W) t)
    (coordGen_isLocNilp W _).neg (coordGen_isLocNilp W a).neg
  intro y
  simpa only [LinearMap.neg_apply, map_neg] using congrArg Neg.neg (coordGen_scale a t y)

/-- U(1) on V in its proved normalized form. -/
def huangStateU (W : VertexOperatorAlgebra V) : V ≃ₗ[ℂ] V :=
  (moduleWeightExpEquiv (adjointModule W) logTwoPiI).trans (normalizedStateChange W)

/-- Identification with Huang's original exponential definition on V. -/
theorem huangStateU_eq_exponential (x : V) :
    huangStateU W x = moduleWeightExp (adjointModule W) logTwoPiI
      (expFun (coordGen_isLocNilp W huangA).neg x) := by
  change normalizedStateChange W (moduleWeightExp (adjointModule W) logTwoPiI x) = _
  rw [normalizedStateChange_exp, huangA_scale, ← exp_logTwoPiI, stateCoordinateChange_scale]

/-- The still open coordinate-substitution law for vertex operators on P.
It is an equality of actual modes, not a substitute WeakModule structure. -/
def NormalizedSquareConjugation (P : LWModule W) : Prop :=
  ∀ (a : V) (m : ℤ) (x : P.carrier),
    normalizedCoordinateChange P (mode (P.isMod.YM a) m x) =
      SquareModule.sqMode P.isMod m (normalizedStateChange W a)
        (normalizedCoordinateChange P x)

/-- The mode factor in the change from Zhu's z to Huang's 2*pi*i*z. -/
def huangModeScale (m : ℤ) : ℂ := Complex.exp (-logTwoPiI * ((m : ℂ) + 1))

theorem huangModeScale_ne_zero (m : ℤ) : huangModeScale m ≠ 0 := Complex.exp_ne_zero _

/-- Full vertex-mode scaling with an arbitrary state, before coordinate change. -/
theorem vertexMode_weightExp (P : LWModule W) (a : V) (m : ℤ) (t : ℂ) (x : P.carrier) :
    moduleWeightExp P.isMod t (mode (P.isMod.YM a) m x) =
      Complex.exp (-t * ((m : ℂ) + 1)) •
        mode (P.isMod.YM (moduleWeightExp (adjointModule W) t a)) m
          (moduleWeightExp P.isMod t x) := by
  have h := intertwiner_weightExp_conjugation (moduleIntertwiner P.isMod) t (m : ℂ) a
    (moduleWeightExp P.isMod t x)
  rw [← moduleWeightExp_add, neg_add_cancel, moduleWeightExp_zero] at h
  simpa only [moduleIntertwiner, moduleModes_apply_intCast, OrdVModule.intMode] using h

/-- Huang (1.5) for vertex modes, conditional only on the normalized
square-bracket coordinate law. All ordinary weight scaling is discharged. -/
theorem huangU_mode_of_squareConjugation (P : LWModule W)
    (h : NormalizedSquareConjugation P) (a : V) (m : ℤ) (x : P.carrier) :
    huangU P 0 (mode (P.isMod.YM a) m x) = huangModeScale m •
      SquareModule.sqMode P.isMod m (huangStateU W a) (huangU P 0 x) := by
  rw [huangU_eq_normalized, moduleWeightExp_zero, vertexMode_weightExp, map_smul, h,
    huangU_eq_normalized, moduleWeightExp_zero]
  rfl

/-- Conjugation form, retaining the actual inverse of U. -/
theorem huangU_conjugation_of_squareConjugation (P : LWModule W)
    (h : NormalizedSquareConjugation P) (a : V) (m : ℤ) (x : P.carrier) :
    huangU P 0 (mode (P.isMod.YM a) m ((huangU P 0).symm x)) = huangModeScale m •
      SquareModule.sqMode P.isMod m (huangStateU W a) x := by
  rw [huangU_mode_of_squareConjugation P h, LinearEquiv.apply_symm_apply]

/-- The exact geometrically modified mode coefficient, with A_j fixed. -/
def huangModifiedModeTrace {P₁ P₂ N Q : LWModule W}
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ t₁ t₂ e : ℂ) : ℂ :=
  modifiedProductModeTrace Y₁ Y₂ huangA w₁ w₂ n₁ n₂ t₁ t₂ e

/-- Identification of the modified coefficient with the constructed U operators. -/
theorem huangModifiedModeTrace_eq {P₁ P₂ N Q : LWModule W}
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ t₁ t₂ e : ℂ) :
    huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e =
      Complex.exp (-t₁ * (n₁ + 1) - t₂ * (n₂ + 1)) *
        productModeTrace Y₁ Y₂ (huangU P₁ t₁ w₁) (huangU P₂ t₂ w₂) n₁ n₂ e := rfl

/-- Simultaneous translation for the actual Huang-normalized coefficient. -/
theorem huangModifiedModeTrace_translate {P₁ P₂ N Q : LWModule W}
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ t₁ t₂ e s : ℂ) :
    huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ (s + t₁) (s + t₂) e =
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e :=
  modifiedProductModeTrace_translate Y₁ Y₂ huangA w₁ w₂ n₁ n₂ t₁ t₂ e s

end VOA.Huang.GenusTwoPoint.Separate
