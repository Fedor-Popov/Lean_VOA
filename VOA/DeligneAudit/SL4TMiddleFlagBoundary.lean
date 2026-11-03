import VOA.DeligneAudit.SL4TMixedStateFlag

/-!
The four flag-block top classes at zero outer labels, their principal boundary ideals,
and the forward and reverse site chains.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The top elementary class of each of the four middle-weight flag blocks. -/
def middleFlagTop (q : MixedParams) : MixedBState → MixedRing q
  | .s1 => mixedEvaluation q (mixedG1prime (mixedP q - q.e1).toNat)
  | .d1 => mixedEvaluation q (mixedE 3 q.e1.toNat)
  | .s2 => mixedEvaluation q (mixedE 4 q.e2.toNat)
  | .d2 => mixedEvaluation q (mixedG2prime (mixedQ q - q.e2).toNat)

/-- The two outer lowering alphabets are empty at zero outer labels. -/
theorem middleFlag_outer_lengths (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0) :
    q.d1 = 0 ∧ q.d3 = 0 := by
  simp only [MixedValid] at hq
  omega

/-- The first two flag tops multiply to the signed top of the complementary base. -/
theorem middleFlag_first_top_product (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) :
    middleFlagTop q .s1 * middleFlagTop q .d1 =
      (-1) ^ (q.B - q.d2).toNat *
        mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat) := by
  have hd := (middleFlag_outer_lengths q hq hA).1
  have h := (mixedG1prime_top q hq).trans (mixedU_top q hq)
  simpa [middleFlagTop, hd, mixedE, mul_comm] using h

/-- The last two flag tops multiply to the top of the chosen middle base. -/
theorem middleFlag_second_top_product (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) :
    middleFlagTop q .s2 * middleFlagTop q .d2 =
      mixedEvaluation q (mixedE 1 q.d2.toNat) := by
  have hd := (middleFlag_outer_lengths q hq hA).2
  have h := (mixedG2prime_top q hq).trans (mixedV_top q hq)
  simpa [middleFlagTop, hA, hd, mixedH] using h

/-- The product of all four top classes vanishes at every positive number of sites. -/
theorem middleFlag_top_product_zero (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 1 ≤ q.B) :
    middleFlagTop q .s1 * middleFlagTop q .d1 *
      middleFlagTop q .s2 * middleFlagTop q .d2 = 0 := by
  have hc := mixedBase_corner_product q hq 1 hB
  change mixedEvaluation q (mixedE 1 q.d2.toNat) *
    mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat) = 0 at hc
  calc
    _ = (middleFlagTop q .s1 * middleFlagTop q .d1) *
        (middleFlagTop q .s2 * middleFlagTop q .d2) := by ring
    _ = 0 := by
      rw [middleFlag_first_top_product q hq hA, middleFlag_second_top_product q hq hA]
      linear_combination (-1 : MixedRing q) ^ (q.B - q.d2).toNat * hc

/-- At zero outer labels each old two-generator state ideal is a principal flag boundary. -/
theorem middleFlag_stateIdeal (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (s : MixedBState) :
    mixedBStateIdeal q s = Ideal.span {middleFlagTop q s} := by
  have hfirst := middleFlag_first_top_product q hq hA
  have hsecond := middleFlag_second_top_product q hq hA
  have hsign : (-1 : MixedRing q) ^ (q.B - q.d2).toNat *
      (-1) ^ (q.B - q.d2).toNat = 1 := by rw [← mul_pow]; simp
  have hcomp : mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat) =
      (-1) ^ (q.B - q.d2).toNat *
        (middleFlagTop q .s1 * middleFlagTop q .d1) := by
    rw [hfirst, ← mul_assoc, hsign, one_mul]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    have hmem := Ideal.subset_span (rfl : middleFlagTop q s ∈ {middleFlagTop q s})
    change x ∈ {(mixedEvaluation q) (mixedBPair q s).1,
      (mixedEvaluation q) (mixedBPair q s).2} at hx
    rcases hx with rfl | hx
    · cases s
      · change mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat) ∈ _
        rw [hcomp]
        exact (Ideal.span {middleFlagTop q .s1}).mul_mem_left _
          ((Ideal.span {middleFlagTop q .s1}).mul_mem_right _ hmem)
      · change mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat) ∈ _
        rw [hcomp]
        exact (Ideal.span {middleFlagTop q .d1}).mul_mem_left _
          ((Ideal.span {middleFlagTop q .d1}).mul_mem_left _ hmem)
      · change mixedEvaluation q (mixedE 1 q.d2.toNat) ∈ _
        rw [← hsecond]
        exact (Ideal.span {middleFlagTop q .s2}).mul_mem_right _ hmem
      · change mixedEvaluation q (mixedE 1 q.d2.toNat) ∈ _
        rw [← hsecond]
        exact (Ideal.span {middleFlagTop q .d2}).mul_mem_left _ hmem
    · have he : x = middleFlagTop q s := by
        cases s <;> simpa [mixedBPair, middleFlagTop] using hx
      simpa only [he] using hmem
  · apply Ideal.span_le.mpr
    rintro x rfl
    apply Ideal.subset_span
    cases s <;> simp [mixedBPair, middleFlagTop, mixedEvaluation,
      Ideal.Quotient.mkₐ_eq_mk]

/-- The site order puts both unretained blocks before both retained blocks. -/
def doubledSiteOuterOrder (i : Fin 4) : MixedBState := ![.s1, .s2, .d1, .d2] i

/-- The second site uses the reverse order. -/
def doubledSiteInnerOrder (i : Fin 4) : MixedBState := ![.d2, .d1, .s2, .s1] i

/-- Thom products for the first of the two sites. -/
def doubledSiteOuterThom (q : MixedParams) (i : Fin 4) : MixedRing q :=
  ![middleFlagTop q .s2 * middleFlagTop q .d1 * middleFlagTop q .d2,
    middleFlagTop q .d1 * middleFlagTop q .d2, middleFlagTop q .d2, 1] i

/-- Thom products for the reversed second site. -/
def doubledSiteInnerThom (q : MixedParams) (i : Fin 4) : MixedRing q :=
  ![middleFlagTop q .d1 * middleFlagTop q .s2 * middleFlagTop q .s1,
    middleFlagTop q .s2 * middleFlagTop q .s1, middleFlagTop q .s1, 1] i

/-- The first-site chain of principal prefix ideals. -/
def doubledSiteOuterChain (q : MixedParams) : ℕ → Ideal (MixedRing q) :=
  principalIdealPrefix (doubledSiteOuterThom q)

/-- The second-site chain of principal prefix ideals in reverse block order. -/
def doubledSiteInnerChain (q : MixedParams) : ℕ → Ideal (MixedRing q) :=
  principalIdealPrefix (doubledSiteInnerThom q)

/-- Multiplication on a principal boundary is determined by its top generator. -/
theorem principalBoundary_mul_mem {R : Type*} [CommRing R]
    (I : Ideal R) (t e : R) (h : t * e ∈ I) :
    ∀ x ∈ Ideal.span {e}, t * x ∈ I := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  simpa only [mul_assoc, mul_left_comm t e] using I.mul_mem_right y h

/-- Every first-site boundary is killed modulo the preceding prefix. -/
theorem doubledSiteOuterThom_boundary (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 1 ≤ q.B) (i : Fin 4) :
    ∀ x ∈ mixedBStateIdeal q (doubledSiteOuterOrder i),
      doubledSiteOuterThom q i * x ∈ doubledSiteOuterChain q i.val := by
  rw [middleFlag_stateIdeal q hq hA]
  apply principalBoundary_mul_mem
  have hz := middleFlag_top_product_zero q hq hA hB
  have hm (k : ℕ) (j : Fin 4) (hj : j.val < k) :
      doubledSiteOuterThom q j ∈ doubledSiteOuterChain q k :=
    mem_principalIdealPrefix _ k j hj
  fin_cases i
  · change _ ∈ principalIdealPrefix _ 0
    rw [principalIdealPrefix_zero]
    change _ = 0
    dsimp [doubledSiteOuterThom, doubledSiteOuterOrder]
    linear_combination hz
  · convert hm 1 0 (by decide) using 1 <;>
      dsimp [doubledSiteOuterThom, doubledSiteOuterOrder] <;> ring
  · convert hm 2 1 (by decide) using 1 <;>
      dsimp [doubledSiteOuterThom, doubledSiteOuterOrder] <;> ring
  · simpa [doubledSiteOuterThom, doubledSiteOuterOrder] using hm 3 2 (by decide)

/-- Every reversed second-site boundary is killed modulo its preceding prefix. -/
theorem doubledSiteInnerThom_boundary (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 1 ≤ q.B) (i : Fin 4) :
    ∀ x ∈ mixedBStateIdeal q (doubledSiteInnerOrder i),
      doubledSiteInnerThom q i * x ∈ doubledSiteInnerChain q i.val := by
  rw [middleFlag_stateIdeal q hq hA]
  apply principalBoundary_mul_mem
  have hz := middleFlag_top_product_zero q hq hA hB
  have hm (k : ℕ) (j : Fin 4) (hj : j.val < k) :
      doubledSiteInnerThom q j ∈ doubledSiteInnerChain q k :=
    mem_principalIdealPrefix _ k j hj
  fin_cases i
  · change _ ∈ principalIdealPrefix _ 0
    rw [principalIdealPrefix_zero]
    change _ = 0
    dsimp [doubledSiteInnerThom, doubledSiteInnerOrder]
    linear_combination hz
  · convert hm 1 0 (by decide) using 1 <;>
      dsimp [doubledSiteInnerThom, doubledSiteInnerOrder] <;> ring
  · convert hm 2 1 (by decide) using 1 <;>
      dsimp [doubledSiteInnerThom, doubledSiteInnerOrder] <;> ring
  · simpa [doubledSiteInnerThom, doubledSiteInnerOrder] using hm 3 2 (by decide)

/-- Both ordered chains begin at zero and end at the full ring. -/
theorem doubledSiteChains_endpoints (q : MixedParams) :
    doubledSiteOuterChain q 0 = ⊥ ∧ doubledSiteOuterChain q 4 = ⊤ ∧
      doubledSiteInnerChain q 0 = ⊥ ∧ doubledSiteInnerChain q 4 = ⊤ := by
  exact ⟨principalIdealPrefix_zero _, principalIdealPrefix_top_of_unit _ 3 rfl,
    principalIdealPrefix_zero _, principalIdealPrefix_top_of_unit _ 3 rfl⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.middleFlag_outer_lengths
#print axioms VOA.DeligneAudit.SL4T.middleFlag_first_top_product
#print axioms VOA.DeligneAudit.SL4T.middleFlag_second_top_product
#print axioms VOA.DeligneAudit.SL4T.middleFlag_top_product_zero
#print axioms VOA.DeligneAudit.SL4T.middleFlag_stateIdeal
#print axioms VOA.DeligneAudit.SL4T.principalBoundary_mul_mem
#print axioms VOA.DeligneAudit.SL4T.doubledSiteOuterThom_boundary
#print axioms VOA.DeligneAudit.SL4T.doubledSiteInnerThom_boundary
#print axioms VOA.DeligneAudit.SL4T.doubledSiteChains_endpoints
