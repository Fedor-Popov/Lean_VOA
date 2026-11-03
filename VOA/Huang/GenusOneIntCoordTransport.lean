import VOA.Huang.GenusTwoPointSepModifiedDerivative
import VOA.Huang.GenusTwoPointSepFlowTruncation

/-!
# Normalized transport of intertwining operators to square modules

These are complex-indexed, bilinear formal modes. The transport uses the actual
positive-Virasoro exponential on all three modules. Its square Jacobi, translation
and grading laws are unconditional. Identification with the independently
substituted field `Y(exp(z L(0)) w, exp(z)-1)` is a separate statement; it is not
part of the definition or inferred from these transport laws.
-/
noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint.Separate
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V} {P Q N : LWModule W}

private theorem equiv_finsum {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ι : Type*} (e : M ≃ₗ[ℂ] M) (f : ι → M) :
    e (∑ᶠ i, f i) = ∑ᶠ i, e (f i) := by
  exact e.toAddEquiv.map_finsum f

/-- The normalized conjugated field, including the inverse change on the
insertion module. Indices are arbitrary complex numbers. -/
def transportedModes (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) :
    IntertwiningModes P.carrier Q.carrier N.carrier := fun n =>
  { toFun := fun w => (normalizedCoordinateChange N).toLinearMap.comp
      ((Y.val n ((normalizedCoordinateChange P).symm w)).comp
        (normalizedCoordinateChange Q).symm.toLinearMap)
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

@[simp] theorem transportedModes_apply
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    transportedModes Y n w x = normalizedCoordinateChange N
      (Y.val n ((normalizedCoordinateChange P).symm w)
        ((normalizedCoordinateChange Q).symm x)) := rfl

/-- Transport preserves lower truncation in every complex mode coset. -/
theorem transportedModes_truncation
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (w : P.carrier) (x : Q.carrier) (n : ℂ) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → transportedModes Y (n + k) w x = 0 := by
  obtain ⟨K, hK⟩ := Y.property.truncation
    ((normalizedCoordinateChange P).symm w) ((normalizedCoordinateChange Q).symm x) n
  exact ⟨K, fun k hk => by simp [hK k hk]⟩

/-- Coordinate transport loses no intertwiner: all three changes are invertible. -/
theorem transportedModes_injective : Function.Injective
    (transportedModes (P := P) (Q := Q) (N := N)) := by
  intro Y Z h
  apply Subtype.ext
  funext n
  ext w x
  apply (normalizedCoordinateChange N).injective
  have he := congrArg (fun f : IntertwiningModes P.carrier Q.carrier N.carrier =>
    f n (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x)) h
  simpa only [transportedModes_apply, LinearEquiv.symm_apply_apply] using he

theorem inverse_square_mode (P : LWModule W) (a : V) (m : ℤ) (w : P.carrier) :
    (normalizedCoordinateChange P).symm (SquareModule.sqMode P.isMod m a w) =
      mode (P.isMod.YM ((normalizedStateChange W).symm a)) m
        ((normalizedCoordinateChange P).symm w) := by
  apply (normalizedCoordinateChange P).injective
  rw [LinearEquiv.apply_symm_apply, normalizedSquareConjugation_holds,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem inverse_square_energy (P : LWModule W) (w : P.carrier) :
    (normalizedCoordinateChange P).symm (sqL P.isMod 0 w) =
      mode (P.isMod.YM W.conformalVector) 1 ((normalizedCoordinateChange P).symm w) := by
  apply (normalizedCoordinateChange P).injective
  rw [LinearEquiv.apply_symm_apply, ← normalizedModuleZeroConjugation_holds,
    LinearEquiv.apply_symm_apply]

theorem inverse_square_translation (P : LWModule W) (w : P.carrier) :
    (normalizedCoordinateChange P).symm (sqL P.isMod (-1) w) =
      P.isMod.Lm1 ((normalizedCoordinateChange P).symm w) := by
  apply (normalizedCoordinateChange P).injective
  rw [LinearEquiv.apply_symm_apply, normalizedCoordinateChange_Lm1,
    LinearEquiv.apply_symm_apply, sqL_negOne]

/-- The exact bracket `L[-1]` derivative law, coefficient of `z^(-n-1)`.
This is a formal derivative, with no spatial evaluation or infinite interchange. -/
theorem transportedModes_derivative
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (n : ℂ) (w : P.carrier) :
    transportedModes Y n (sqL P.isMod (-1) w) =
      (-n) • transportedModes Y (n - 1) w := by
  ext x
  simp only [transportedModes_apply, inverse_square_translation,
    Y.property.L_neg_one, LinearMap.smul_apply, map_smul]

/-- The bracket energy commutator, for every insertion and complex mode. -/
theorem transportedModes_energy
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    sqL N.isMod 0 (transportedModes Y n w x) -
      transportedModes Y n w (sqL Q.isMod 0 x) =
    transportedModes Y n (sqL P.isMod 0 w) x -
      (n + 1) • transportedModes Y n w x := by
  have hzero : ∀ y : N.carrier, sqL N.isMod 0 (normalizedCoordinateChange N y) =
      normalizedCoordinateChange N (mode (N.isMod.YM W.conformalVector) 1 y) :=
    normalizedModuleZeroConjugation_holds N
  simpa only [transportedModes_apply, inverse_square_energy,
    hzero, map_sub, map_smul] using
    congrArg (normalizedCoordinateChange N) (LatFus.comm_L0 Y.property
      ((normalizedCoordinateChange P).symm w) ((normalizedCoordinateChange Q).symm x) n)

/-- A bracket mode carries square weights `α, β` to `α + β - n - 1`. -/
theorem transportedModes_weight
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    {α β : ℂ} {w : P.carrier} {x : Q.carrier}
    (hw : sqL P.isMod 0 w = α • w) (hx : sqL Q.isMod 0 x = β • x) (n : ℂ) :
    sqL N.isMod 0 (transportedModes Y n w x) =
      (α + β - n - 1) • transportedModes Y n w x := by
  have h := transportedModes_energy Y n w x
  rw [hw, hx, map_smul, map_smul, LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  module

/-- The left square Jacobi coefficient has finite support, before summation. -/
theorem transportedModes_jacobi_left_finite
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (a : V) (w : P.carrier) (x : Q.carrier) (l m : ℤ) (n : ℂ) :
    (Function.support (fun i : ℤ => (negOnePow i * cbz l i) •
      (SquareModule.sqMode N.isMod (l + m - i) a (transportedModes Y (n + i) w x) -
        negOnePow l • transportedModes Y (l + n - i) w
          (SquareModule.sqMode Q.isMod (m + i) a x)))).Finite := by
  refine (IsIntertwiningOperator.jacL_support_finite (A₂ := Q.isMod) (A₃ := N.isMod)
    Y.property.truncation
    ((normalizedStateChange W).symm a) ((normalizedCoordinateChange P).symm w)
    ((normalizedCoordinateChange Q).symm x) l m n).subset ?_
  intro i hi hz
  apply hi
  apply (normalizedCoordinateChange N).symm.injective
  simpa only [map_smul, map_sub, map_zero, inverse_square_mode,
    transportedModes_apply, LinearEquiv.symm_apply_apply,
    IsIntertwiningOperator.jacL] using hz

/-- The right square Jacobi coefficient (including the commutator case `l=0`)
has finite support, before summation. -/
theorem transportedModes_jacobi_right_finite
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (a : V) (w : P.carrier) (x : Q.carrier) (l m : ℤ) (n : ℂ) :
    (Function.support (fun i : ℤ => cbz m i • transportedModes Y (m + n - i)
      (SquareModule.sqMode P.isMod (l + i) a w) x)).Finite := by
  refine (IsIntertwiningOperator.jacR_support_finite (A₁ := P.isMod) Y.val
    ((normalizedStateChange W).symm a) ((normalizedCoordinateChange P).symm w)
    ((normalizedCoordinateChange Q).symm x) l m n).subset ?_
  intro i hi hz
  apply hi
  apply (normalizedCoordinateChange N).symm.injective
  simpa only [map_smul, map_zero, inverse_square_mode, transportedModes_apply,
    LinearEquiv.symm_apply_apply, IsIntertwiningOperator.jacR] using hz

/-- Full square-bracket Jacobi identity for the transported field, with the
existing explicit Zhu square modes on each of the three modules. -/
theorem transportedModes_jacobi
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (a : V) (w : P.carrier) (x : Q.carrier) (l m : ℤ) (n : ℂ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz l i) •
      (SquareModule.sqMode N.isMod (l + m - i) a (transportedModes Y (n + i) w x) -
        negOnePow l • transportedModes Y (l + n - i) w
          (SquareModule.sqMode Q.isMod (m + i) a x))) =
    ∑ᶠ i : ℤ, cbz m i • transportedModes Y (m + n - i)
      (SquareModule.sqMode P.isMod (l + i) a w) x := by
  apply (normalizedCoordinateChange N).symm.injective
  rw [equiv_finsum, equiv_finsum]
  simpa only [LinearEquiv.coe_toAddEquiv,
    map_smul, map_sub, inverse_square_mode, transportedModes_apply,
    LinearEquiv.symm_apply_apply] using
    Y.property.jacobi ((normalizedStateChange W).symm a)
      ((normalizedCoordinateChange P).symm w) ((normalizedCoordinateChange Q).symm x) l m n

/-- Square-mode commutator with an arbitrary VOA insertion. The sum is the
coefficientwise finite Jacobi commutator, and the intertwiner index is complex. -/
theorem transportedModes_commutator
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (a : V) (w : P.carrier) (x : Q.carrier) (m : ℤ) (n : ℂ) :
    SquareModule.sqMode N.isMod m a (transportedModes Y n w x) -
      transportedModes Y n w (SquareModule.sqMode Q.isMod m a x) =
    ∑ᶠ i : ℤ, cbz m i • transportedModes Y (m + n - i)
      (SquareModule.sqMode P.isMod i a w) x := by
  apply (normalizedCoordinateChange N).symm.injective
  rw [equiv_finsum]
  simpa only [map_sub, map_smul, inverse_square_mode, transportedModes_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.coe_toAddEquiv] using
    Y.property.commutator ((normalizedStateChange W).symm a)
      ((normalizedCoordinateChange P).symm w) ((normalizedCoordinateChange Q).symm x) m n

end VOA.Huang.GenusOne.IntCoord
