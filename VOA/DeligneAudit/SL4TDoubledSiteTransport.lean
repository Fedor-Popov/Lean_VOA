import VOA.DeligneAudit.SL4TDoubledSitePairTruncation
import VOA.DeligneAudit.SL4TCompositeThomChain

/-! Composite boundary kernels and characteristic lifts for the surviving doubled sites. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- A principal image boundary lifts modulo a kernel already killed by multiplication. -/
theorem mul_mem_of_principal_image {R S : Type*} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (ρ : R →ₐ[ℂ] S) (hρ : Function.Surjective ρ)
    (I : Ideal R) (t b : R) (hker : ∀ x, ρ x = 0 → t * x ∈ I)
    (hb : t * b ∈ I) (x : R) (hx : ρ x ∈ Ideal.span {ρ b}) : t * x ∈ I := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨z, rfl⟩ := hρ y
  have hz : ρ (x - b * z) = 0 := by rw [map_sub, map_mul, hy, sub_self]
  have h := I.add_mem (hker _ hz) (I.mul_mem_right z hb)
  convert h using 1 <;> ring

/-- The two removed states of a surviving pair, in their original mixed-state notation. -/
def doubledSitePairStates (k : Fin 10) : MixedBState × MixedBState :=
  (mixedBOrder (doubledSiteFlagIndex (doubledPairIndices k).1),
    mixedBOrder (doubledSiteFlagIndex (doubledPairIndices k).2))

/-- Block parameters after removing the two distinguished sites. -/
def doubledSiteReducedParams (q : MixedParams) (k : Fin 10) : MixedParams :=
  mixedBNext (mixedBNext q (doubledSitePairStates k).1) (doubledSitePairStates k).2

/-- The signed second boundary, lowered once when the two roots share a block. -/
def doubledSiteRemovedTop (q : MixedParams) (i j : Fin 4) : MixedRing q :=
  if j = i then doubledSiteSignedLinear q i else doubledSiteSignedTop q j

/-- The explicit signed boundary maps to the top of the once-reduced block. -/
theorem doubledSiteRemovedTop_map (q : MixedParams) (hq : MixedValid q) (i j : Fin 4)
    (hi : MixedValid (mixedBNext q (mixedBOrder (doubledSiteFlagIndex i)))) :
    mixedBProjection q hq (mixedBOrder (doubledSiteFlagIndex i)) hi
        (doubledSiteRemovedTop q i j) =
      (doubledSiteFlagPolynomials
        (mixedBNext q (mixedBOrder (doubledSiteFlagIndex i))) j).coeff 0 := by
  have h := congrArg (fun p => p.coeff 0)
    (middleFlagRemovedPolynomial_map q hq (doubledSiteFlagIndex i)
      (doubledSiteFlagIndex j) hi)
  have he : doubledSiteFlagIndex j = doubledSiteFlagIndex i ↔ j = i := by
    fin_cases i <;> fin_cases j <;> decide
  by_cases hj : j = i
  · subst j
    simpa only [middleFlagRemovedPolynomial, doubledSiteRemovedTop, doubledSiteSignedTop,
      doubledSiteSignedLinear, doubledSiteFlagPolynomials, if_true, coeff_map,
      coeff_divX, zero_add] using h
  · simpa only [middleFlagRemovedPolynomial, doubledSiteRemovedTop, doubledSiteSignedTop,
      doubledSiteSignedLinear, doubledSiteFlagPolynomials, he, if_neg hj, coeff_map] using h

/-- The composite quotient map removes the two distinguished roots. -/
def doubledSitePairProjection (q : MixedParams) (hq : MixedValid q) (k : Fin 10)
    (hi : MixedValid (mixedBNext q (doubledSitePairStates k).1))
    (hj : MixedValid (doubledSiteReducedParams q k)) :
    MixedRing q →ₐ[ℂ] MixedRing (doubledSiteReducedParams q k) :=
  (mixedBProjection _ hi (doubledSitePairStates k).2 hj).comp
    (mixedBProjection q hq (doubledSitePairStates k).1 hi)

/-- Both boundary projections, and hence their composite, are onto. -/
theorem doubledSitePairProjection_surjective (q : MixedParams) (hq : MixedValid q)
    (k : Fin 10) (hi : MixedValid (mixedBNext q (doubledSitePairStates k).1))
    (hj : MixedValid (doubledSiteReducedParams q k)) :
    Function.Surjective (doubledSitePairProjection q hq k hi hj) :=
  (mixedBProjection_surjective _ hi _ hj).comp
    (mixedBProjection_surjective q hq _ hi)

/-- The retained characteristic is the product of the two retained flag polynomials. -/
theorem doubledSiteFlagPolynomials_characteristic (q : MixedParams) :
    mixedCharacteristic q = doubledSiteFlagPolynomials q 2 * doubledSiteFlagPolynomials q 3 :=
  rfl

/-- The explicit lift of every surviving pair maps to the inner retained characteristic. -/
theorem doubledSitePairProjection_polynomial (q : MixedParams) (hq : MixedValid q)
    (k : Fin 10) (hi : MixedValid (mixedBNext q (doubledSitePairStates k).1))
    (hj : MixedValid (doubledSiteReducedParams q k)) :
    (doubledPairPolynomial (doubledSiteFlagPolynomials q) k).map
        (doubledSitePairProjection q hq k hi hj).toRingHom =
      mixedCharacteristic (doubledSiteReducedParams q k) := by
  have he : doubledPairPolynomial (doubledSiteFlagPolynomials q) k =
      middleFlagTwiceRemovedPolynomial q
        (doubledSiteFlagIndex (doubledPairIndices k).1)
        (doubledSiteFlagIndex (doubledPairIndices k).2) 1 *
      middleFlagTwiceRemovedPolynomial q
        (doubledSiteFlagIndex (doubledPairIndices k).1)
        (doubledSiteFlagIndex (doubledPairIndices k).2) 3 := by
    fin_cases k <;> rfl
  rw [he, Polynomial.map_mul]
  change _ * _ = middleFlagPolynomial _ 1 * middleFlagPolynomial _ 3
  exact congrArg₂ (· * ·)
    (middleFlagTwiceRemovedPolynomial_map q hq _ _ 1 hi hj)
    (middleFlagTwiceRemovedPolynomial_map q hq _ _ 3 hi hj)

/-- Both signed boundary products lie in the preceding surviving-pair ideal. -/
theorem doubledSitePair_boundaries (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (k : Fin 10) :
    let a := doubledSiteSignedTop q
    let t := doubledPairTop a k
    let J := doubledPairPrefix a (middleFlagTailIdeal q (q.B.toNat - 1)) k.val
    t * a (doubledPairIndices k).1 ∈ J ∧
      t * doubledSiteRemovedTop q (doubledPairIndices k).1
        (doubledPairIndices k).2 ∈ J := by
  dsimp only
  apply doubledPairTop_boundaries (doubledSiteSignedTop q) (doubledSiteSignedLinear q)
  · have he : (∏ i : Fin 4, doubledSiteFlagPolynomials q i) = X ^ q.B.toNat := by
      have h := middleFlagPolynomial_product q hq hA
      convert h using 1
      simp [doubledSiteFlagPolynomials, doubledSiteFlagIndex, Fin.prod_univ_succ]
      ring
    have h := congrArg (fun p : (MixedRing q)[X] => p.coeff 0) he
    have hp : 0 < q.B.toNat := by omega
    change (doubledSiteFlagPolynomials q 0).coeff 0 *
      (doubledSiteFlagPolynomials q 1).coeff 0 *
      (doubledSiteFlagPolynomials q 2).coeff 0 *
      (doubledSiteFlagPolynomials q 3).coeff 0 = 0
    simpa [Fin.prod_univ_succ, mul_assoc, hp.ne, hp.ne'] using h
  · intro i
    rw [doubledSiteSignedLinear_tail q hq hA hB]
    exact Ideal.subset_span ⟨doubledSiteFlagIndex i, rfl⟩

/-- The first projection kernel is killed modulo the surviving-pair prefix. -/
theorem doubledSitePair_first_kernel (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (k : Fin 10)
    (hi : MixedValid (mixedBNext q (doubledSitePairStates k).1))
    (x : MixedRing q) (hx : mixedBProjection q hq (doubledSitePairStates k).1 hi x = 0) :
    doubledPairTop (doubledSiteSignedTop q) k * x ∈
      doubledPairPrefix (doubledSiteSignedTop q)
        (middleFlagTailIdeal q (q.B.toNat - 1)) k.val := by
  apply principalBoundary_mul_mem _ _ _ (doubledSitePair_boundaries q hq hA hB k).1 x
  have hk := mixedBProjection_kernel q hq (by omega) (doubledSitePairStates k).1 hi
  dsimp only [doubledSitePairStates] at hk
  rw [middleFlag_stateIdeal_constant q hq hA] at hk
  exact (show RingHom.ker (mixedBProjection q hq _ hi).toRingHom ≤ _ from hk.le) hx

/-- The composite kernel is killed by its Thom coefficient modulo the earlier pairs. -/
theorem doubledSitePairProjection_kernel (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (k : Fin 10)
    (hi : MixedValid (mixedBNext q (doubledSitePairStates k).1))
    (hj : MixedValid (doubledSiteReducedParams q k))
    (x : MixedRing q) (hx : doubledSitePairProjection q hq k hi hj x = 0) :
    doubledPairTop (doubledSiteSignedTop q) k * x ∈
      doubledPairPrefix (doubledSiteSignedTop q)
        (middleFlagTailIdeal q (q.B.toNat - 1)) k.val := by
  let q' := mixedBNext q (doubledSitePairStates k).1
  have hA' : q'.A = 0 := by
    dsimp only [q']
    cases (doubledSitePairStates k).1 <;> exact hA
  have hB' : 1 ≤ q'.B := by
    dsimp only [q']
    cases (doubledSitePairStates k).1 <;> change 1 ≤ q.B - 1 <;> omega
  apply mul_mem_of_principal_image (mixedBProjection q hq _ hi)
    (mixedBProjection_surjective q hq _ hi) _ _
    (doubledSiteRemovedTop q (doubledPairIndices k).1 (doubledPairIndices k).2)
    (doubledSitePair_first_kernel q hq hA hB k hi)
    (doubledSitePair_boundaries q hq hA hB k).2
  dsimp only [doubledSitePairStates]
  erw [doubledSiteRemovedTop_map q hq (doubledPairIndices k).1 (doubledPairIndices k).2 hi]
  have hk := mixedBProjection_kernel q' hi hB' (doubledSitePairStates k).2 hj
  dsimp only [doubledSitePairStates] at hk
  rw [middleFlag_stateIdeal_constant q' hi hA'] at hk
  exact (show RingHom.ker (mixedBProjection q' hi _ hj).toRingHom ≤ _ from hk.le) hx

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mul_mem_of_principal_image
#print axioms VOA.DeligneAudit.SL4T.doubledSiteRemovedTop_map
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairProjection_surjective
#print axioms VOA.DeligneAudit.SL4T.doubledSiteFlagPolynomials_characteristic
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairProjection_polynomial
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_boundaries
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_first_kernel
#print axioms VOA.DeligneAudit.SL4T.doubledSitePairProjection_kernel
