import VOA.Huang.GenusTwoPointSepIntertwinerFlow

/-!
# Translation after Huang's coordinate modification

The operator identity behind Huang Proposition 1.3 is unconditional. For an
individual complex-indexed mode it has two terms, one with the shifted index
n-1. Dropping that shift would incorrectly assert a derivative identity for a
single coefficient. No infinite trace sum is differentiated in this file.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Session 5's coordinate law at the conformal zero mode. -/
theorem normalizedCoordinateChange_Lm1 (P : LWModule W) (w : P.carrier) :
    normalizedCoordinateChange P (P.isMod.Lm1 w) =
      cylT P.isMod (normalizedCoordinateChange P w) := by
  have h := normalizedSquareConjugation_holds P W.conformalVector 0 w
  rw [normalizedStateChange_conformalVector] at h
  change normalizedCoordinateChange P (P.isMod.Lm1 w) =
    SquareModule.sqMode P.isMod ((-1 : ℤ) + 1) (SquareModule.shiftedOmega W)
      (normalizedCoordinateChange P w) at h
  rw [SquareModule.sqMode_shiftedOmega, sqL_negOne] at h
  exact h

/-- Ordinary scaling of translation, with the logarithm specified. -/
theorem moduleWeightExp_Lm1 (P : LWModule W) (t : ℂ) (w : P.carrier) :
    moduleWeightExp P.isMod t (P.isMod.Lm1 w) =
      Complex.exp t • P.isMod.Lm1 (moduleWeightExp P.isMod t w) := by
  have h := vertexMode_weightExp_conjugation P.isMod W.conformal_mem 0 t
    (moduleWeightExp P.isMod t w)
  rw [← moduleWeightExp_add, neg_add_cancel, moduleWeightExp_zero] at h
  norm_num at h
  exact h

/-- Ordinary scaling commutes with energy. -/
theorem moduleWeightExp_L0 (P : LWModule W) (t : ℂ) (w : P.carrier) :
    moduleWeightExp P.isMod t (mode (P.isMod.YM W.conformalVector) 1 w) =
      mode (P.isMod.YM W.conformalVector) 1 (moduleWeightExp P.isMod t w) := by
  have h := vertexMode_weightExp_conjugation P.isMod W.conformal_mem 1 t
    (moduleWeightExp P.isMod t w)
  rw [← moduleWeightExp_add, neg_add_cancel, moduleWeightExp_zero] at h
  norm_num at h
  exact h

/-- Huang (1.15) on every lowest-weight module, at every logarithmic point. -/
theorem huangU_Lm1 (P : LWModule W) (t : ℂ) (w : P.carrier) :
    huangU P t (P.isMod.Lm1 w) = Complex.exp logTwoPiI •
      (Complex.exp t • P.isMod.Lm1 (huangU P t w) +
        mode (P.isMod.YM W.conformalVector) 1 (huangU P t w)) := by
  have hzero : huangU P 0 (P.isMod.Lm1 w) =
      Complex.exp logTwoPiI • cylT P.isMod (huangU P 0 w) := by
    rw [huangU_eq_normalized, moduleWeightExp_zero, moduleWeightExp_Lm1,
      map_smul, normalizedCoordinateChange_Lm1,
      huangU_eq_normalized, moduleWeightExp_zero]
  have ht (v : P.carrier) : huangU P t v = moduleWeightExp P.isMod t (huangU P 0 v) := by
    simpa using huangU_add P t 0 v
  rw [ht, hzero, map_smul]
  simp only [cylT, LinearMap.add_apply, map_add, moduleWeightExp_Lm1,
    moduleWeightExp_L0, ht, OrdVModule.Lm1]

variable {P Q N : LWModule W}

/-- The exact two-term coefficient form of the modified derivative law for
a general intertwiner. The mode-shift contribution is retained. -/
theorem huangIntertwiner_Lm1 (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (n t : ℂ) (w : P.carrier) :
    Y.val n (huangU P t (P.isMod.Lm1 w)) =
      Complex.exp logTwoPiI •
        ((-n * Complex.exp t) • Y.val (n - 1) (huangU P t w) +
          Y.val n (mode (P.isMod.YM W.conformalVector) 1 (huangU P t w))) := by
  rw [huangU_Lm1, map_smul, map_add, map_smul, Y.property.L_neg_one, smul_smul]
  rw [mul_comm (Complex.exp t)]

/-- A scalar matrix coefficient of the algebraic weight exponential is
entire. No topology on the module, or continuity of its linear functional,
is necessary because each vector has finitely many weight components. -/
theorem hasDerivAt_weightExp_scalar (P : LWModule W) (f : P.carrier →ₗ[ℂ] ℂ)
    (w : P.carrier) (t : ℂ) :
    HasDerivAt (fun s => f (moduleWeightExp P.isMod s w))
      (f (mode (P.isMod.YM W.conformalVector) 1 (moduleWeightExp P.isMod t w))) t := by
  refine FusionTop.induction_weight P.isMod w ?_ ?_ ?_
  · simpa using (hasDerivAt_const t (0 : ℂ))
  · intro x y hx hy
    simpa only [map_add] using hx.add hy
  · intro α x hx
    simp only [moduleWeightExp_of_weight P.isMod _ hx, map_smul, smul_eq_mul,
      P.isMod.L0_weight α x hx]
    convert (((hasDerivAt_id t).mul_const α).cexp.mul_const (f x)) using 1
    simp only [id_eq]
    ring

/-- The derivative of a scalar modified insertion, on the logarithmic cover. -/
theorem hasDerivAt_huangU_scalar (P : LWModule W) (f : P.carrier →ₗ[ℂ] ℂ)
    (w : P.carrier) (t : ℂ) :
    HasDerivAt (fun s => f (huangU P s w))
      (f (mode (P.isMod.YM W.conformalVector) 1 (huangU P t w))) t := by
  have ht (s : ℂ) : huangU P s w = moduleWeightExp P.isMod s (huangU P 0 w) := by
    simpa using huangU_add P s 0 w
  convert hasDerivAt_weightExp_scalar P f (huangU P 0 w) t using 1
  · funext s
    rw [← ht]
  · rw [← ht]

variable {P₁ P₂ : LWModule W}

/-- Differentiation of one actual modified two-mode trace in its first
coordinate. This is finite-dimensional trace calculus at a fixed q-degree. -/
theorem hasDerivAt_huangModifiedModeTrace_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ t₁ t₂ e : ℂ) :
    HasDerivAt (fun s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ s t₂ e)
      (Complex.exp (-t₁ * (n₁ + 1) - t₂ * (n₂ + 1)) *
        productTracePair Y₁ Y₂ n₁ n₂ e
          (mode (P₁.isMod.YM W.conformalVector) 1 (huangU P₁ t₁ w₁))
          (huangU P₂ t₂ w₂) -
        (n₁ + 1) * huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e) t₁ := by
  let f := (productTracePair Y₁ Y₂ n₁ n₂ e).flip (huangU P₂ t₂ w₂)
  have h := hasDerivAt_huangU_scalar P₁ f w₁ t₁
  have he := (((hasDerivAt_id t₁).neg.mul_const (n₁ + 1)).sub_const
    (t₂ * (n₂ + 1))).cexp
  convert he.mul h using 1
  simp only [huangModifiedModeTrace, modifiedProductModeTrace, f,
    LinearMap.flip_apply, huangU, Pi.neg_apply, id_eq]
  ring

/-- The right coordinate derivative, with the product orientation retained. -/
theorem hasDerivAt_huangModifiedModeTrace_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ t₁ t₂ e : ℂ) :
    HasDerivAt (fun s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ s e)
      (Complex.exp (-t₁ * (n₁ + 1) - t₂ * (n₂ + 1)) *
        productTracePair Y₁ Y₂ n₁ n₂ e (huangU P₁ t₁ w₁)
          (mode (P₂.isMod.YM W.conformalVector) 1 (huangU P₂ t₂ w₂)) -
        (n₂ + 1) * huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e) t₂ := by
  let f := productTracePair Y₁ Y₂ n₁ n₂ e (huangU P₁ t₁ w₁)
  have h := hasDerivAt_huangU_scalar P₂ f w₂ t₂
  have he := (((hasDerivAt_id t₂).mul_const (n₂ + 1)).const_sub
    (-t₁ * (n₁ + 1))).cexp
  convert he.mul h using 1
  simp only [huangModifiedModeTrace, modifiedProductModeTrace, f, huangU, id_eq]
  ring

end VOA.Huang.GenusTwoPoint.Separate
