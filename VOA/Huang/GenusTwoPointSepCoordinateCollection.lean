import VOA.Huang.GenusTwoPointSepFormalCoordinate

/-!
# Exact square-coordinate collection residual

These equations are on the actual raw, spatially evaluated trace. The finite
coordinate conversion to the unchanged target is proved. The residual is
equivalent to that target, not a narrower theorem or a proof of collection.
In particular it must still be obtained by spatial reindexing and elliptic
collection of the formal normal-order identities.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation FuchsianODE
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The three collected equations with explicit square-coordinate insertions.
The cutoff is transported through the actual inverse U. -/
def SquareCoordinateIdentities (P₁ P₂ : LWModule W) (t₁ t₂ s₁ s₂ lam : ℂ)
    (c : Kernels SubexpPS) (g₂ p₁ : SubexpPS)
    (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] PowerSeries ℂ) : Prop :=
  (∀ a x y, ∃ K, TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a
      ((huangU P₁ t₁).symm x) ((huangU P₂ t₂).symm y) K ∧
    S (spatialSquareMode P₁ t₁ a (-2) x) y +
      (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : SubexpPS) * c.G k) •
        S (spatialSquareMode P₁ t₁ a (2 * (k + 1)) x) y) +
      (∑ m ∈ Finset.range K, ((-1 : SubexpPS) ^ m * (m + 1) * c.Pleft m) •
        S x (spatialSquareMode P₂ t₂ a m y)) = 0) ∧
  (∀ a x y, ∃ K, TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a
      ((huangU P₁ t₁).symm x) ((huangU P₂ t₂).symm y) K ∧
    S x (spatialSquareMode P₂ t₂ a (-2) y) +
      (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : SubexpPS) * c.G k) •
        S x (spatialSquareMode P₂ t₂ a (2 * (k + 1)) y)) +
      (∑ m ∈ Finset.range K, ((-1 : SubexpPS) ^ m * (m + 1) * c.Pright m) •
        S (spatialSquareMode P₁ t₁ a m x) y) = 0) ∧
  (∀ x y, ∃ K, TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule W.conformalVector
      ((huangU P₁ t₁).symm x) ((huangU P₂ t₂).symm y) K ∧
    (2 * (Real.pi : ℂ) * Complex.I) ^ 2 • thetaShift lam (S x y) +
      (g₂ • (S (spatialSquareMode P₁ t₁ W.conformalVector 1 x) y +
        S x (spatialSquareMode P₂ t₂ W.conformalVector 1 y) +
        s₁ • S (spatialSquareMode P₁ t₁ W.conformalVector 0 x) y +
        s₂ • S x (spatialSquareMode P₂ t₂ W.conformalVector 0 y)) -
        p₁ • S x (spatialSquareMode P₂ t₂ W.conformalVector 0 y)) =
    S (spatialSquareMode P₁ t₁ W.conformalVector (-1) x) y -
      (∑ k ∈ Finset.range K, c.G k •
        S (spatialSquareMode P₁ t₁ W.conformalVector (2 * (k + 1) + 1) x) y) +
      ∑ m ∈ Finset.range K, ((-1 : SubexpPS) ^ (m + 1) * c.Pleft m) •
        S x (spatialSquareMode P₂ t₂ W.conformalVector (m + 1) y))

/-- Coordinate conversion of all three equations, with no analytic hypothesis. -/
theorem squareCoordinateIdentities_iff (P₁ P₂ : LWModule W) (t₁ t₂ s₁ s₂ lam : ℂ)
    (c : Kernels SubexpPS) (g₂ p₁ : SubexpPS)
    (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] PowerSeries ℂ) :
    SquareCoordinateIdentities P₁ P₂ t₁ t₂ s₁ s₂ lam c g₂ p₁ S ↔
    (CollectedLeftWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule c
        (huangPairEquiv P₁ P₂ t₁ t₂ S) ∧
      CollectedRightWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule c
        (huangPairEquiv P₁ P₂ t₁ t₂ S) ∧
      MixedPairWard SubexpPS P₁.isMod.toWeakModule P₂.isMod.toWeakModule c g₂ p₁ s₁ s₂ lam
        (huangPairEquiv P₁ P₂ t₁ t₂ S)) := by
  constructor
  · rintro ⟨hL, hR, hE⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a x y
      obtain ⟨K, hK, he⟩ := hL a (huangU P₁ t₁ x) (huangU P₂ t₂ y)
      refine ⟨K, by simpa using hK, ?_⟩
      simpa only [huangPairEquiv_apply, spatialSquareMode_conjugation,
        LinearEquiv.symm_apply_apply] using he
    · intro a x y
      obtain ⟨K, hK, he⟩ := hR a (huangU P₁ t₁ x) (huangU P₂ t₂ y)
      refine ⟨K, by simpa using hK, ?_⟩
      simpa only [huangPairEquiv_apply, spatialSquareMode_conjugation,
        LinearEquiv.symm_apply_apply] using he
    · intro x y
      obtain ⟨K, hK, he⟩ := hE (huangU P₁ t₁ x) (huangU P₂ t₂ y)
      refine ⟨K, by simpa using hK, ?_⟩
      simpa only [mixedEnergyCorrection, mixedEnergyDescendants, huangPairEquiv_apply,
        spatialSquareMode_conjugation, LinearEquiv.symm_apply_apply] using he
  · rintro ⟨hL, hR, hE⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a x y
      obtain ⟨K, hK, he⟩ := hL a ((huangU P₁ t₁).symm x) ((huangU P₂ t₂).symm y)
      refine ⟨K, hK, ?_⟩
      simpa only [huangPairEquiv_apply, huangU_mode_spatialSquare,
        LinearEquiv.apply_symm_apply] using he
    · intro a x y
      obtain ⟨K, hK, he⟩ := hR a ((huangU P₁ t₁).symm x) ((huangU P₂ t₂).symm y)
      refine ⟨K, hK, ?_⟩
      simpa only [huangPairEquiv_apply, huangU_mode_spatialSquare,
        LinearEquiv.apply_symm_apply] using he
    · intro x y
      obtain ⟨K, hK, he⟩ := hE ((huangU P₁ t₁).symm x) ((huangU P₂ t₂).symm y)
      refine ⟨K, hK, ?_⟩
      simpa only [mixedEnergyCorrection, mixedEnergyDescendants, huangPairEquiv_apply,
        huangU_mode_spatialSquare, LinearEquiv.apply_symm_apply] using he

variable {P₁ P₂ N Q : LWModule W}

/-- Exact remaining collection statement on the actual raw trace. TRUE in
Huang's setting, but not proved here. This is equivalent to the old residual. -/
def RawCuspCoordinateCollection (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) : Prop :=
  SquareCoordinateIdentities P₁ P₂ (Complex.log z₁) (Complex.log z₂)
    (cuspLogCoordinate z₁) (cuspLogCoordinate z₂) (N.h - W.centralCharge / 24)
    (cuspWardKernels hz₂ hz hr) (cuspEnergyG2 hz₂ hz hr) (cuspEnergyP1 hz₂ hz hr)
    (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho)

/-- No equation is weakened by moving coordinate modification to the insertions. -/
theorem rawCuspCoordinateCollection_iff (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    RawCuspCoordinateCollection hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr ↔
      ProductCollectedCuspIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr := by
  unfold RawCuspCoordinateCollection ProductCollectedCuspIdentities
  rw [modifiedProductCuspSeries_eq_huangPairEquiv]
  exact squareCoordinateIdentities_iff _ _ _ _ _ _ _ _ _ _ _

/-- Consumer at the single natural boundary radius; collection remains a premise. -/
theorem productCollectedCuspIdentities_of_rawCollection (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (h : RawCuspCoordinateCollection hV i₁ i₂ iN Y₁ Y₂ hz₂ hz
      (rho := z₂ / z₁) le_rfl) :
    ProductCollectedCuspIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (rho := z₂ / z₁) le_rfl :=
  (rawCuspCoordinateCollection_iff hV i₁ i₂ iN Y₁ Y₂ hz₂ hz le_rfl).mp h

end VOA.Huang.GenusTwoPoint.Separate
