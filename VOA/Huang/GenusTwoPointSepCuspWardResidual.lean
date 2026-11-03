import VOA.Huang.GenusOneQEquationSepCuspEnergy
import VOA.Huang.GenusTwoPointSepCuspKernelEvaluation

/-!
# The precise evaluated Ward identities remaining at the natural radius

All kernels are explicit rescaled Fourier series in SubexpPS. The residual
contains the two minus-two identities and the mixed omega identity, on the
actual modified product trace. It is not proved here. The implications below
remove energy-span closure as an additional independent input and use the
single boundary scale rho = z₂/z₁ for the whole open product annulus.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Additive insertion coordinate on the selected logarithmic branch. -/
def cuspLogCoordinate (z : ℂ) : ℂ := Complex.log z / (2 * (Real.pi : ℂ) * Complex.I)

/-- The weight-two coefficient of the mixed energy Ward law. -/
def cuspEnergyG2 {z₁ z₂ rho : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) : ↥SubexpPS :=
  ⟨eisensteinCuspSeries 1 rho,
    eisensteinCusp_mem_subexp 1 (annulus_kernel_conditions hz₂ hz hr).1⟩

/-- wp₁ with its additive-coordinate term retained. -/
def cuspEnergyP1 {z₁ z₂ rho : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) : ↥SubexpPS :=
  ⟨wpCuspSeries 0 (z₂ / z₁) (cuspLogCoordinate z₂ - cuspLogCoordinate z₁) rho,
    wpCusp_mem_subexp 0 _ (annulus_kernel_conditions hz₂ hz hr).1
      (annulus_kernel_conditions hz₂ hz hr).2.1
      (annulus_kernel_conditions hz₂ hz hr).2.2⟩

/-- Huang (2.22), l=2 in both slots, and its omega/l=1 specialization
(Lemma 3.8), after evaluation in the spatial variables and q-rescaling.
These are still genuine unproved trace identities; no growth premise occurs. -/
def ProductCollectedCuspIdentities (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) : Prop :=
  let c := cuspWardKernels hz₂ hz hr
  let S := modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
  CollectedLeftWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule c S ∧
  CollectedRightWard P₁.isMod.toWeakModule P₂.isMod.toWeakModule c S ∧
  MixedPairWard SubexpPS P₁.isMod.toWeakModule P₂.isMod.toWeakModule c
    (cuspEnergyG2 hz₂ hz hr) (cuspEnergyP1 hz₂ hz hr)
    (cuspLogCoordinate z₁) (cuspLogCoordinate z₂) (N.h - W.centralCharge / 24) S

/-- The full residual implies the sufficient Ward predicate `ProductCuspWard`. -/
theorem productCuspWard_of_explicitIdentities (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖)
    (h : ProductCollectedCuspIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr) :
    ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho :=
  productCuspWard_of_collected hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
    (cuspWardKernels hz₂ hz hr) h.1 h.2.1
    (pairEulerClosed_of_mixedPairWard SubexpPS _ _ _ _ _ _ _ _ _ h.2.2)

/-- A single explicit nonzero radius suffices. The Ward identities at that
radius remain the sole hypothesis beyond the ordinary VOA data. -/
theorem exists_productCuspWard_of_boundaryIdentities (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (h : ProductCollectedCuspIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz
      (rho := z₂ / z₁) le_rfl) :
    ∃ rho : ℂ, rho ≠ 0 ∧ ‖rho‖ = ‖z₂ / z₁‖ ∧
      ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  exact ⟨z₂ / z₁, div_ne_zero hz₂ hz₁, rfl,
    productCuspWard_of_explicitIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz le_rfl h⟩

/-- Conditional convergence throughout Huang's natural open product annulus.
No family of Ward hypotheses at all smaller radii is needed. -/
theorem productQSummable_of_boundaryIdentities (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (h : ProductCollectedCuspIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz
      (rho := z₂ / z₁) le_rfl)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ * ‖z₁‖ < ‖z₂‖) :
    ProductQSummable Y₁ Y₂ x y α₁ α₂ z₁ z₂ τ := by
  apply productQSummable_of_cuspWard hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz
    (productCuspWard_of_explicitIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz le_rfl h) τ
  rw [norm_div, lt_div_iff₀ ((norm_nonneg _).trans_lt hz)]
  exact hq

end VOA.Huang.GenusTwoPoint.Separate
