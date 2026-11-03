import VOA.Huang.GenusTwoPointCoordinates
import VOA.Huang.GenusTwoPointWard

/-!
# The simultaneous-coordinate Ward law for modified two-mode traces

This is an actual trace of the two coordinate-modified insertion vectors,
including both exponential coordinate factors. Its simultaneous translation
law holds on the logarithmic cover for arbitrary insertion vectors, not only
primaries. The positive-Virasoro coefficient family remains a parameter.
The elliptic minus-two and q-derivative Ward identities are not claimed here.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Bilinearity of the actual rectangular-mode trace before any infinite sum. -/
noncomputable def productTracePair
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) (n₁ n₂ e : ℂ) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] ℂ where
  toFun w₁ :=
    { toFun := fun w₂ => productModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ e
      map_add' := by
        intro x y
        simp only [productModeTrace, map_add, LinearMap.comp_add, gradedTraceOp_add,
          Pi.add_apply]
      map_smul' := by
        intro c x
        simp only [productModeTrace, map_smul, LinearMap.comp_smul, gradedTraceOp_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  map_add' := by
    intro x y
    ext w
    simp only [productModeTrace, map_add, LinearMap.add_comp, gradedTraceOp_add,
      Pi.add_apply, LinearMap.add_apply]
    rfl
  map_smul' := by
    intro c x
    ext w
    simp only [productModeTrace, map_smul, LinearMap.smul_comp, gradedTraceOp_smul,
      Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rfl

/-- Weight conservation determines simultaneous scaling even when either
insertion has several ordinary-weight components. -/
theorem productTracePair_weightExp
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) (n₁ n₂ e t : ℂ)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) :
    productTracePair Y₁ Y₂ n₁ n₂ e (moduleWeightExp P₁.isMod t w₁)
      (moduleWeightExp P₂.isMod t w₂) =
      Complex.exp (t * (n₁ + n₂ + 2)) * productTracePair Y₁ Y₂ n₁ n₂ e w₁ w₂ := by
  let T := productTracePair Y₁ Y₂ n₁ n₂ e
  change T (moduleWeightExp P₁.isMod t w₁) (moduleWeightExp P₂.isMod t w₂) =
    Complex.exp (t * (n₁ + n₂ + 2)) * T w₁ w₂
  refine FusionTop.induction_weight P₁.isMod w₁ (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply, hx, hy, mul_add]
  · intro α x hx
    refine FusionTop.induction_weight P₂.isMod w₂ (by simp) ?_ ?_
    · intro y z hy hz
      simp only [map_add, hy, hz, mul_add]
    · intro β y hy
      rw [moduleWeightExp_of_weight P₁.isMod t hx, moduleWeightExp_of_weight P₂.isMod t hy]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      by_cases hn : n₁ + n₂ = α + β - 2
      · rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        linear_combination -t * hn
      · have hz : T x y = 0 := productModeTrace_eq_zero Y₁ Y₂ hx hy hn e
        rw [hz, mul_zero, mul_zero, mul_zero]

/-- A modified coefficient on the logarithmic coordinate cover. The two
coordinate powers are exponential functions, so no principal-power rule is used. -/
noncomputable def modifiedProductModeTrace
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : ℕ → ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier)
    (n₁ n₂ t₁ t₂ e : ℂ) : ℂ :=
  Complex.exp (-t₁ * (n₁ + 1) - t₂ * (n₂ + 1)) *
    productTracePair Y₁ Y₂ n₁ n₂ e
      (coordinateModification P₁ a t₁ w₁) (coordinateModification P₂ a t₂ w₂)

/-- The simultaneous-coordinate Ward identity for actual modified mode traces.
It holds for descendants and for every q-degree separately. -/
theorem modifiedProductModeTrace_translate
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : ℕ → ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier)
    (n₁ n₂ t₁ t₂ e s : ℂ) :
    modifiedProductModeTrace Y₁ Y₂ a w₁ w₂ n₁ n₂ (s + t₁) (s + t₂) e =
      modifiedProductModeTrace Y₁ Y₂ a w₁ w₂ n₁ n₂ t₁ t₂ e := by
  unfold modifiedProductModeTrace
  rw [coordinateModification_add, coordinateModification_add, productTracePair_weightExp,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end VOA.Huang.GenusTwoPoint
