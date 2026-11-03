import VOA.DeligneAudit.SL4TDoubledSiteCatalog

/-! Spanning chains of the doubled-site quotient ring at the shortened current cutoff. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- An invalid reduction has its entire Thom image in the preceding pair ideal. -/
theorem doubledSitePair_invalid_mem (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (k : Fin 10)
    (hj : ¬ MixedValid (doubledSiteReducedParams q k)) :
    doubledPairTop (doubledSiteSignedTop q) k ∈
      doubledPairPrefix (doubledSiteSignedTop q)
        (middleFlagTailIdeal q (q.B.toNat - 1)) k.val := by
  let q' := mixedBNext q (doubledSitePairStates k).1
  have hA' : q'.A = 0 := (mixedBNext_outer q _).trans hA
  have hB' : 1 ≤ q'.B := by dsimp only [q']; rw [mixedBNext_middle]; omega
  have hb := doubledSitePair_boundaries q hq hA hB k
  by_cases hi : MixedValid q'
  · have hz := mixedBStateIdeal_eq_top_of_invalid q' hi hB'
      (doubledSitePairStates k).2 hj
    dsimp only [doubledSitePairStates] at hz
    rw [middleFlag_stateIdeal_constant q' hi hA'] at hz
    have hm := mul_mem_of_principal_image (mixedBProjection q hq _ hi)
      (mixedBProjection_surjective q hq _ hi) _ _
      (doubledSiteRemovedTop q (doubledPairIndices k).1 (doubledPairIndices k).2)
      (doubledSitePair_first_kernel q hq hA hB k hi) hb.2 1
    apply (by simpa only [mul_one] using hm)
    erw [doubledSiteRemovedTop_map q hq (doubledPairIndices k).1
      (doubledPairIndices k).2 hi]
    erw [hz]
    trivial
  · have hz := mixedBStateIdeal_eq_top_of_invalid q hq (by omega)
      (doubledSitePairStates k).1 hi
    dsimp only [doubledSitePairStates] at hz
    rw [middleFlag_stateIdeal_constant q hq hA] at hz
    have hone : (1 : MixedRing q) ∈
        Ideal.span {doubledSiteSignedTop q (doubledPairIndices k).1} := by
      rw [show Ideal.span {doubledSiteSignedTop q (doubledPairIndices k).1} = ⊤ from hz]
      trivial
    simpa only [mul_one] using principalBoundary_mul_mem _ _ _ hb.1 1 hone

/-- A surviving pair transports its inner mixed chain, with empty invalid reductions. -/
theorem doubledSitePair_spanningChain (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (k : Fin 10) :
    let a := doubledSiteSignedTop q
    let I := middleFlagTailIdeal q (q.B.toNat - 1)
    SpanningChain
      (relationIdeal (doubledSiteFlagPolynomials q 2) (doubledSiteFlagPolynomials q 3)
        (q.B.toNat - 1))
      (doubledPairPrefix a I k.val) (doubledPairPrefix a I (k.val + 1))
      ((mixedCellLevels (q.B.toNat - 2) (doubledSiteReducedParams q k)).map
        (fun n => n + doubledPairLevelShift k)) := by
  dsimp only
  simp only [doubledPairPrefix, principalIdealPrefix_step _ k, ← sup_assoc]
  by_cases hj : MixedValid (doubledSiteReducedParams q k)
  · have hi := doubledSiteReducedParams_first_valid q k hj
    have hl := doubledSiteReducedParams_labels q k
    have hn : ((doubledSiteReducedParams q k).A +
        (doubledSiteReducedParams q k).B).toNat = q.B.toNat - 2 := by
      rw [hl.1, hl.2, hA, zero_add]
      omega
    have hs := mixedCellFlag_recursive (q.B.toNat - 2)
      (doubledSiteReducedParams q k) hj hn
    have hp := doubledSitePair_polynomialRelations q hq hA hB k
    apply SpanningChain.thom_of_generators (doubledSitePairProjection q hq k hi hj)
      (doubledSitePairProjection_surjective q hq k hi hj)
      (doubledPairTop (doubledSiteSignedTop q) k) _ _
      (doubledPairPolynomial (doubledSiteFlagPolynomials q) k) (q.B.toNat - 2)
      (doubledPairLevelShift k) (doubledSitePairProjection_kernel q hq hA hB k hi hj)
      hp.1 hp.2
    rw [doubledSitePairProjection_polynomial]
    simpa only [mixedTruncationIdeal, hn] using hs
  · rw [mixedCellLevels_invalid _ _ hj, List.map_nil]
    have ht := doubledSitePair_invalid_mem q hq hA hB k hj
    have hle : Ideal.span {doubledPairTop (doubledSiteSignedTop q) k} ≤
        doubledPairPrefix (doubledSiteSignedTop q)
          (middleFlagTailIdeal q (q.B.toNat - 1)) k.val :=
      Ideal.span_le.mpr (by rintro x rfl; exact ht)
    dsimp only [doubledPairPrefix] at hle
    rw [sup_eq_left.mpr hle]
    exact .nil _

/-- Concatenate consecutive ideal chains indexed by an ordered finite interval. -/
theorem SpanningChain.join_finRange {R : Type*} [CommRing R] [Algebra ℂ R]
    (A : Ideal R[X]) (J : ℕ → Ideal R) (n : ℕ) (ns : Fin n → List ℕ)
    (h : ∀ i, SpanningChain A (J i.val) (J (i.val + 1)) (ns i)) :
    SpanningChain A (J 0) (J n) ((List.finRange n).flatMap ns) := by
  induction n with
  | zero => simpa using SpanningChain.nil (A := A) (J 0)
  | succ n ih =>
      rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      simpa using (ih (fun i => ns i.castSucc) (fun i => h i.castSucc)).append (h (Fin.last n))

/-- The ten surviving inner chains span from the tail ideal to the whole mixed ring. -/
theorem doubledSite_spanningChain_before_quotient (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) :
    SpanningChain
      (Ideal.span {mixedCharacteristic q} ⊔
        Ideal.span {(X : (MixedRing q)[X]) ^ (q.B.toNat - 1)})
      (middleFlagTailIdeal q (q.B.toNat - 1)) ⊤
      ((mixedCatalogFiber q (doubledSiteCellCatalog (q.B.toNat - 2))).map mixedCellLevel) := by
  rw [doubledSiteCellCatalog_levels q hA hB, doubledSiteFlagPolynomials_characteristic]
  have h := SpanningChain.join_finRange
    (relationIdeal (doubledSiteFlagPolynomials q 2) (doubledSiteFlagPolynomials q 3)
      (q.B.toNat - 1))
    (doubledPairPrefix (doubledSiteSignedTop q) (middleFlagTailIdeal q (q.B.toNat - 1)))
    10 _ (doubledSitePair_spanningChain q hq hA hB)
  have hend : principalIdealPrefix (doubledPairTop (doubledSiteSignedTop q)) 10 = ⊤ :=
    principalIdealPrefix_top_of_unit _ 9 rfl
  simpa only [doubledPairPrefix, principalIdealPrefix_zero, sup_bot_eq, hend, sup_top_eq,
    relationIdeal] using h

/-- Every valid middle-weight block has the doubled-site quotient spanning filtration. -/
theorem doubledSiteSpanningFiltration (B : ℕ) (hB : 2 ≤ B) (q : MixedParams)
    (hq : MixedValid q) (hA : q.A = 0) (hsites : q.B = B) :
    DoubledSiteSpanningFiltration B q := by
  have h := doubledSite_spanningChain_before_quotient q hq hA (by omega)
  have hn : q.B.toNat = B := by omega
  rw [hn] at h
  let I := middleFlagTailIdeal q (B - 1)
  have hm := h.map_surjective (Ideal.Quotient.mkₐ ℂ I)
    (Ideal.Quotient.mkₐ_surjective ℂ I)
  have hz : (middleFlagTailIdeal q (B - 1)).map (Ideal.Quotient.mkₐ ℂ I).toRingHom = ⊥ := by
    apply le_antisymm _ bot_le
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    Polynomial.coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X,
    Ideal.map_top, hz] using hm

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_invalid_mem
#print axioms VOA.DeligneAudit.SL4T.doubledSitePair_spanningChain
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.join_finRange
#print axioms VOA.DeligneAudit.SL4T.doubledSite_spanningChain_before_quotient
#print axioms VOA.DeligneAudit.SL4T.doubledSiteSpanningFiltration
