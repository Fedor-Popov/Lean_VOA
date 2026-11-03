import VOA.Huang.GenusOneWardMixedClause

/-!
# Genus-one two-point Ward identities: headline

`RawCuspCoordinateCollection` (the collected minus-two Ward identities in both
slots and the mixed omega identity, on the actual raw cusp trace) holds for
every admissible rescaling `ρ`, in particular at the natural radius
`ρ = z₂/z₁`. Consequently `ProductCollectedCuspIdentities` holds, and through
the existing conditional chain the two-point product trace is `q`-summable on
Huang's open annulus `|q| |z₁| < |z₂| < |z₁|`, with no further hypothesis
beyond strong rationality and irreducibility (the PBW theorem `VOA.pbw` is not used by this file's
proofs).
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.Separate
open VOA.Huang.GenusTwoPoint (ProductQSummable productCoeff)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- **The genus-one two-point Ward identities on the actual raw trace.** -/
theorem rawCuspCoordinateCollection_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    RawCuspCoordinateCollection hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr :=
  ⟨leftClause hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr, rightClause hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr,
    mixedClause hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr⟩

/-- **Huang's collected cusp Ward identities (2.22) and Lemma 3.8.** -/
theorem productCollectedCuspIdentities_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    ProductCollectedCuspIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr :=
  (rawCuspCoordinateCollection_iff hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr).mp
    (rawCuspCoordinateCollection_holds hV i₁ i₂ iN Y₁ Y₂ hz₂ hz hr)

/-- The cusp Ward predicate `ProductCuspWard`, unconditionally at the natural radius. -/
theorem productCuspWard_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    ProductCuspWard hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (z₂ / z₁) :=
  productCuspWard_of_explicitIdentities hV i₁ i₂ iN Y₁ Y₂ hz₂ hz le_rfl
    (productCollectedCuspIdentities_holds hV i₁ i₂ iN Y₁ Y₂ hz₂ hz le_rfl)

/-- **Two-point genus-one convergence.** The product trace
`Tr Y₁(x,z₁) Y₂(y,z₂) q^{L₀}` is summable in `q` on `|q| |z₁| < |z₂| < |z₁|`. -/
theorem productQSummable_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ * ‖z₁‖ < ‖z₂‖) :
    ProductQSummable Y₁ Y₂ x y α₁ α₂ z₁ z₂ τ :=
  productQSummable_of_boundaryIdentities hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz
    (productCollectedCuspIdentities_holds hV i₁ i₂ iN Y₁ Y₂ hz₂ hz le_rfl) τ hq

/-- **The two-point genus-one q-system**, unconditionally: the modified two-point
traces lie in a finitely generated module over the subexponential coefficient
ring, closed under the twisted Euler operator (a regular-singular system in `q`). -/
theorem exists_product_cusp_system_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    ∃ (U : Finset P₁.carrier) (Z : Finset P₂.carrier)
      (C : U × Z → U × Z → ↥SubexpPS),
      (∀ k, FuchsianODE.thetaShift (N.h - W.centralCharge / 24)
          (modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (z₂ / z₁) k.1.val k.2.val) =
        ∑ l : U × Z, (C k l).val *
          modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (z₂ / z₁) l.1.val l.2.val) ∧
      (∀ x y, ∃ c : U × Z → ↥SubexpPS,
        modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (z₂ / z₁) x y =
        ∑ l : U × Z, (c l).val *
          modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (z₂ / z₁) l.1.val l.2.val) :=
  exists_product_cusp_system hV i₁ i₂ iN Y₁ Y₂ hz₂ hz (z₂ / z₁)
    (productCuspWard_holds hV i₁ i₂ iN Y₁ Y₂ hz₂ hz)

/-- The normalized two-point trace is analytic at the cusp `q = 0`. -/
theorem analyticAt_product_qSeries_zero_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    AnalyticAt ℂ (fun q : ℂ => ∑' n : ℕ,
      productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ * q ^ n) 0 := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  exact analyticAt_product_qSeries_zero_of_cuspWard hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz
    (productCuspWard_holds hV i₁ i₂ iN Y₁ Y₂ hz₂ hz) (div_ne_zero hz₂ hz₁)

/-- The certified value of the genus-one two-point trace on Huang's annulus. -/
theorem hasSum_product_qTrace_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ * ‖z₁‖ < ‖z₂‖) :
    HasSum (fun n : ℕ => productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ *
        VOA.Huang.GenusTwoPoint.qFactor N τ n)
      (VOA.Huang.GenusTwoPoint.qTrace N (fun β => productCoeff Y₁ Y₂ x y α₁ α₂ β z₁ z₂) τ) :=
  (productQSummable_holds hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz τ hq).hasSum

end VOA.Huang.GenusOneWard
