import VOA.Huang.GenusOneIntCoordTransport
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# The explicit complex-power bracket intertwiner

In the normalized variable `z` (Huang's variable multiplied by `2*pi*i`),
the bracket field is `Y(exp(z L(0)) w, exp(z)-1)`. On weight `α`, its mode `n`
is the sum over `r ≥ 0` of `Y(n+r) w` multiplied by the coefficient of `z^r` in
`exp(α z) ((exp(z)-1)/z)^(-n-r-1)`.

We use the binomial formal power series for the complex power of a unit.
All mode sums below have finite support by intertwiner truncation. The extension
to arbitrary insertions uses the finite ordinary-weight decomposition. No complex
analytic powers, convergence, or evaluated infinite sums enter this construction.

`NormalizedIntertwinerSubstitution` is the remaining true coordinate identity
(Huang, math/0303049, Proposition 1.2, normalized as (1.7)). It is explicitly
retained as a hypothesis, not proved by naming the transported field a substitution.
-/
noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint GenusTwoPoint.Separate
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V} {P Q N : LWModule W}

/-- The unit `(exp(z)-1)/z`, with constant coefficient one. -/
def exponentialUnit : PowerSeries ℂ :=
  PowerSeries.mk fun r => ((r + 1).factorial : ℂ)⁻¹

@[simp] theorem exponentialUnit_constant : PowerSeries.constantCoeff exponentialUnit = 1 := by
  simp [exponentialUnit, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The quotient notation in the definition is justified in the formal ring. -/
theorem X_mul_exponentialUnit :
    PowerSeries.X * exponentialUnit = PowerSeries.exp ℂ - 1 := by
  ext r
  cases r with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ r =>
    simp [PowerSeries.coeff_succ_X_mul, exponentialUnit, PowerSeries.coeff_exp]

/-- The argument of binomial substitution has zero constant term. -/
theorem exponentialUnit_sub_one_constant :
    PowerSeries.constantCoeff (exponentialUnit - 1) = 0 := by simp

/-- The honest formal expansion of `((exp(z)-1)/z)^b`, for complex `b`.
The substitution is valid since its argument has constant term zero. -/
def exponentialUnitPower (b : ℂ) : PowerSeries ℂ :=
  (PowerSeries.binomialSeries ℂ b).subst (exponentialUnit - 1)

theorem exponentialUnitPower_coeff_finite (b : ℂ) (r : ℕ) :
    (Function.support (fun d : ℕ => Ring.choose b d *
      PowerSeries.coeff r ((exponentialUnit - 1) ^ d))).Finite := by
  simpa only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
    Function.HasFiniteSupport] using
    PowerSeries.coeff_subst_finite'
      (PowerSeries.HasSubst.of_constantCoeff_zero' exponentialUnit_sub_one_constant)
      (PowerSeries.binomialSeries ℂ b) r

/-- Every complex-power coefficient is itself a finite binomial sum. -/
theorem exponentialUnitPower_coeff (b : ℂ) (r : ℕ) :
    PowerSeries.coeff r (exponentialUnitPower b) =
      ∑ᶠ d : ℕ, Ring.choose b d * PowerSeries.coeff r ((exponentialUnit - 1) ^ d) := by
  simp [exponentialUnitPower, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' exponentialUnit_sub_one_constant),
    smul_eq_mul]

@[simp] theorem exponentialUnitPower_constant (b : ℂ) :
    PowerSeries.constantCoeff (exponentialUnitPower b) = 1 := by
  rw [exponentialUnitPower,
    constantCoeff_subst_of_constantCoeff_eq_zero exponentialUnit_sub_one_constant]
  simp

/-- Scalar coefficient for a bracket mode on ordinary weight `α`. -/
def bracketCoeff (α n : ℂ) (r : ℕ) : ℂ :=
  PowerSeries.coeff r
    (PowerSeries.rescale α (PowerSeries.exp ℂ) *
      exponentialUnitPower (-n - (r : ℂ) - 1))

@[simp] theorem bracketCoeff_zero (α n : ℂ) : bracketCoeff α n 0 = 1 := by
  simp only [bracketCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, exponentialUnitPower_constant, mul_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
  simp

/-- Finiteness is supplied by modes, independent of the complex scalar factors. -/
theorem weighted_modes_support_finite
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (c : ℕ → ℂ) (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    (Function.support (fun r : ℕ => c r • Y.val (n + r) w x)).Finite := by
  obtain ⟨K, hK⟩ := Y.property.truncation w x n
  refine (Finset.range K.toNat).finite_toSet.subset fun r hr => ?_
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have hrK : K ≤ (r : ℤ) := by omega
  exact hr (by simpa using congrArg (c r • ·) (hK r hrK))

/-- Formal substitution on a single ordinary weight, extended bilinearly in
the vectors. The weight label is used only in the scalar coefficient. -/
def bracketAtWeight (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (α n : ℂ) : P.carrier →ₗ[ℂ] Q.carrier →ₗ[ℂ] N.carrier where
  toFun w :=
    { toFun := fun x => ∑ᶠ r : ℕ, bracketCoeff α n r • Y.val (n + r) w x
      map_add' x y := by
        simp only [map_add, smul_add]
        exact finsum_add_distrib (weighted_modes_support_finite Y _ n w x)
          (weighted_modes_support_finite Y _ n w y)
      map_smul' c x := by
        simp only [map_smul, RingHom.id_apply, smul_comm (bracketCoeff α n _) c]
        exact (smul_finsum' c (weighted_modes_support_finite Y _ n w x)).symm }
  map_add' w v := by
    ext x
    simp only [map_add, LinearMap.add_apply, smul_add]
    exact finsum_add_distrib (weighted_modes_support_finite Y _ n w x)
      (weighted_modes_support_finite Y _ n v x)
  map_smul' c w := by
    ext x
    simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply,
      smul_comm (bracketCoeff α n _) c]
    exact (smul_finsum' c (weighted_modes_support_finite Y _ n w x)).symm

/-- The explicit bracket intertwiner mode, extended over the finite ordinary
weight decomposition. This definition does not use coordinate conjugation. -/
def bracketModes (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) :
    IntertwiningModes P.carrier Q.carrier N.carrier := fun n =>
  letI := DirectSum.IsInternal.chooseDecomposition P.isMod.weight P.isMod.isInternal
  (DFinsupp.lsum ℂ (fun α =>
    (bracketAtWeight Y α n).comp (P.isMod.weight α).subtype)).comp
    (DirectSum.decomposeLinearEquiv P.isMod.weight).toLinearMap

/-- Coefficient extraction for `Y(exp(z L(0)) w, exp(z)-1)` on a homogeneous
insertion. Every displayed sum is finite after fixing the two input vectors. -/
theorem bracketModes_of_weight
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) (n : ℂ) (x : Q.carrier) :
    bracketModes Y n w x = ∑ᶠ r : ℕ, bracketCoeff α n r • Y.val (n + r) w x := by
  letI := DirectSum.IsInternal.chooseDecomposition P.isMod.weight P.isMod.isInternal
  change ((DFinsupp.lsum ℂ (fun α =>
    (bracketAtWeight Y α n).comp (P.isMod.weight α).subtype))
      (DirectSum.decompose P.isMod.weight w)) x = _
  rw [DirectSum.decompose_of_mem P.isMod.weight hw]
  exact congrArg (fun f : Q.carrier →ₗ[ℂ] N.carrier => f x)
    (DFinsupp.lsum_single ℂ (fun α =>
      (bracketAtWeight Y α n).comp (P.isMod.weight α).subtype) α ⟨w, hw⟩)

/-- An explicit finite cutoff formula; increasing the cutoff adds only zeros. -/
theorem bracketModes_eq_sum_range
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) (n : ℂ) (x : Q.carrier)
    (K : ℕ) (hK : ∀ r : ℕ, K ≤ r → Y.val (n + r) w x = 0) :
    bracketModes Y n w x =
      ∑ r ∈ Finset.range K, bracketCoeff α n r • Y.val (n + r) w x := by
  rw [bracketModes_of_weight Y hw]
  apply finsum_eq_sum_of_support_subset
  intro r hr
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hr (by dsimp; rw [hK r (le_of_not_gt h), smul_zero])

/-- The top nonzero mode on a homogeneous insertion is unchanged. -/
theorem bracketModes_eq_of_tail_zero
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) (n : ℂ) (x : Q.carrier)
    (ht : ∀ r : ℕ, 1 ≤ r → Y.val (n + r) w x = 0) :
    bracketModes Y n w x = Y.val n w x := by
  rw [bracketModes_eq_sum_range Y hw n x 1 ht]
  simp

/-- The explicitly substituted field remains lower truncated in every coset. -/
theorem bracketModes_truncation
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (w : P.carrier) (x : Q.carrier) (n : ℂ) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → bracketModes Y (n + k) w x = 0 := by
  refine FusionTop.induction_weight P.isMod w ?_ ?_ ?_
  · exact ⟨0, fun k _ => by simp⟩
  · intro w v hw hv
    obtain ⟨K, hK⟩ := hw
    obtain ⟨L, hL⟩ := hv
    exact ⟨max K L, fun k hk => by simp [hK k (le_trans (le_max_left _ _) hk),
      hL k (le_trans (le_max_right _ _) hk)]⟩
  · intro α w hw
    obtain ⟨K, hK⟩ := Y.property.truncation w x n
    refine ⟨K, fun k hk => ?_⟩
    rw [bracketModes_of_weight Y hw]
    apply finsum_eq_zero_of_forall_eq_zero
    intro r
    have he : n + (k : ℂ) + (r : ℂ) = n + ((k + (r : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    rw [he, hK (k + r) (by omega), smul_zero]

/-- The exact remaining normalized coordinate theorem: independently defined
formal substitution equals actual three-module exponential transport.
This is a true target for every intertwiner; no assertion that it holds is made here. -/
def NormalizedIntertwinerSubstitution
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) : Prop :=
  ∀ (n : ℂ) (w : P.carrier) (x : Q.carrier),
    bracketModes Y n w x = transportedModes Y n w x

/-- It suffices to prove the explicit scalar-coefficient identity on ordinary
weight vectors. This reduction keeps all complex modes and all source vectors. -/
theorem normalizedIntertwinerSubstitution_of_weight
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (h : ∀ (α n : ℂ) (w : P.carrier), w ∈ P.isMod.weight α → ∀ x : Q.carrier,
      (∑ᶠ r : ℕ, bracketCoeff α n r • Y.val (n + r) w x) =
        transportedModes Y n w x) : NormalizedIntertwinerSubstitution Y := by
  intro n w x
  refine FusionTop.induction_weight P.isMod w (by simp) ?_ ?_
  · intro w v hw hv
    simp only [map_add, LinearMap.add_apply, hw, hv]
  · intro α w hw
    rw [bracketModes_of_weight Y hw]
    exact h α n w hw x

/-- Equivalent sandwich form of the residual, with the state change explicit. -/
theorem normalizedIntertwinerSubstitution_iff_sandwich
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) :
    NormalizedIntertwinerSubstitution Y ↔
      ∀ (n : ℂ) (w : P.carrier) (x : Q.carrier),
        normalizedCoordinateChange N (Y.val n w ((normalizedCoordinateChange Q).symm x)) =
          bracketModes Y n (normalizedCoordinateChange P w) x := by
  constructor
  · intro h n w x
    rw [h, transportedModes_apply, LinearEquiv.symm_apply_apply]
  · intro h n w x
    simpa using (h n ((normalizedCoordinateChange P).symm w) x).symm

/-- The precise remaining comparison with the integrated geometric
jets suffices for substitution. Cutoffs may depend on the fixed mode and vectors. -/
theorem normalizedIntertwinerSubstitution_of_geometricJet
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (h : ∀ (n : ℂ) (w : P.carrier) (x : Q.carrier), ∃ K₀ : ℕ, ∀ K ≥ K₀,
      (∑ᶠ r, linearFlowCoeff
        (geometricJet (fun j => -iterativeLog (logarithmicCoordinate 1) j) K)
        (fun m v => Y.val m v) r n w x) =
          bracketModes Y n (normalizedCoordinateChange P w) x) :
    NormalizedIntertwinerSubstitution Y := by
  apply (normalizedIntertwinerSubstitution_iff_sandwich Y).mpr
  intro n w x
  obtain ⟨K₁, h₁⟩ := normalizedIntertwiner_eq_geometricJet Y n w x
  obtain ⟨K₂, h₂⟩ := h n w x
  exact (h₁ (max K₁ K₂) (le_max_left _ _)).trans
    (h₂ (max K₁ K₂) (le_max_right _ _))

/-- Huang's U(1) sandwich in complex modes, conditional only on the normalized
substitution identity. The `2*pi*i` scaling is retained at every complex index. -/
theorem huangIntertwiner_substitution_of_normalized
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (h : NormalizedIntertwinerSubstitution Y)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    huangU N 0 (Y.val n w ((huangU Q 0).symm x)) =
      Complex.exp (-logTwoPiI * (n + 1)) • bracketModes Y n (huangU P 0 w) x := by
  rw [huangIntertwiner_commutator_expansion,
    ← normalizedIntertwiner_commutator_expansion,
    (normalizedIntertwinerSubstitution_iff_sandwich Y).mp h]
  rw [huangU_eq_normalized, moduleWeightExp_zero]

/-- Once substitution is identified, the explicit bracket field has the
square translation law; no further analytic hypothesis is needed. -/
theorem bracketModes_derivative_of_substitution
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (h : NormalizedIntertwinerSubstitution Y) (n : ℂ) (w : P.carrier) :
    bracketModes Y n (sqL P.isMod (-1) w) = (-n) • bracketModes Y (n - 1) w := by
  unfold NormalizedIntertwinerSubstitution at h
  ext x
  simpa only [h, LinearMap.smul_apply] using
    congrArg (fun f : Q.carrier →ₗ[ℂ] N.carrier => f x) (transportedModes_derivative Y n w)

/-- Square-weight grading of the explicit bracket field, conditional precisely
on the named coordinate identity. -/
theorem bracketModes_weight_of_substitution
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (h : NormalizedIntertwinerSubstitution Y)
    {α β : ℂ} {w : P.carrier} {x : Q.carrier}
    (hw : sqL P.isMod 0 w = α • w) (hx : sqL Q.isMod 0 x = β • x) (n : ℂ) :
    sqL N.isMod 0 (bracketModes Y n w x) = (α + β - n - 1) • bracketModes Y n w x := by
  unfold NormalizedIntertwinerSubstitution at h
  simpa only [h] using transportedModes_weight Y hw hx n

/-- Square commutator for the explicit bracket field, conditional precisely on
the normalized coordinate identity. -/
theorem bracketModes_commutator_of_substitution
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (h : NormalizedIntertwinerSubstitution Y)
    (a : V) (w : P.carrier) (x : Q.carrier) (m : ℤ) (n : ℂ) :
    SquareModule.sqMode N.isMod m a (bracketModes Y n w x) -
      bracketModes Y n w (SquareModule.sqMode Q.isMod m a x) =
    ∑ᶠ i : ℤ, cbz m i • bracketModes Y (m + n - i)
      (SquareModule.sqMode P.isMod i a w) x := by
  unfold NormalizedIntertwinerSubstitution at h
  simpa only [h] using transportedModes_commutator Y a w x m n

/-- Full square Jacobi for the explicit substituted field, with the same
single coordinate hypothesis as the derivative and commutator consumers. -/
theorem bracketModes_jacobi_of_substitution
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (h : NormalizedIntertwinerSubstitution Y)
    (a : V) (w : P.carrier) (x : Q.carrier) (l m : ℤ) (n : ℂ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz l i) •
      (SquareModule.sqMode N.isMod (l + m - i) a (bracketModes Y (n + i) w x) -
        negOnePow l • bracketModes Y (l + n - i) w
          (SquareModule.sqMode Q.isMod (m + i) a x))) =
    ∑ᶠ i : ℤ, cbz m i • bracketModes Y (m + n - i)
      (SquareModule.sqMode P.isMod (l + i) a w) x := by
  unfold NormalizedIntertwinerSubstitution at h
  simpa only [h] using transportedModes_jacobi Y a w x l m n

end VOA.Huang.GenusOne.IntCoord
