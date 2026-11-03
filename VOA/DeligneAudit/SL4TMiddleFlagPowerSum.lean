import VOA.DeligneAudit.SL4TMiddleFlagBoundary
import VOA.DeligneAudit.SL4TComplementPowerSum
import VOA.DeligneAudit.SL4TDoubledSiteRingImage

/-! The four flag characteristic polynomials and their last-mode tail identities. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- The lengths of the four blocks in their original flag order. -/
def middleFlagLength (q : MixedParams) (i : Fin 4) : ℕ :=
  ![(mixedP q - q.e1).toNat, q.e1.toNat, q.e2.toNat,
    (mixedQ q - q.e2).toNat] i

/-- The elementary coefficients of the four flag blocks in the original generators. -/
def middleFlagElementary (i : Fin 4) : ℕ → MixedPoly :=
  ![mixedG1prime, mixedE 3, mixedE 4, mixedG2prime] i

/-- The ascending signed elementary polynomial of a flag block. -/
def middleFlagCoefficientPolynomial (q : MixedParams) (i : Fin 4) : (MixedRing q)[X] :=
  coefficientPoly (fun n => (-1) ^ n * mixedEvaluation q (middleFlagElementary i n))
    (middleFlagLength q i)

/-- The characteristic polynomial of a flag block. -/
def middleFlagPolynomial (q : MixedParams) (i : Fin 4) : (MixedRing q)[X] :=
  (middleFlagCoefficientPolynomial q i).reflect (middleFlagLength q i)

/-- The four block lengths add to the number of middle sites. -/
theorem middleFlagLength_sum (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0) :
    ∑ i : Fin 4, middleFlagLength q i = q.B.toNat := by
  obtain ⟨hd1, hd3⟩ := middleFlag_outer_lengths q hq hA
  simp only [MixedValid, mixedP, mixedQ] at hq
  simp [Fin.sum_univ_succ, middleFlagLength, mixedP, mixedQ, hA, hd1, hd3]
  omega

/-- The original finite relations force the entire tail of each block to vanish. -/
theorem middleFlagElementary_tail (q : MixedParams) (hq : MixedValid q)
    (i : Fin 4) (n : ℕ) (hn : middleFlagLength q i < n) :
    mixedEvaluation q (middleFlagElementary i n) = 0 := by
  fin_cases i
  · exact mixedG1prime_tail q hq n hn
  · exact mixedElementary_tail q hq 3 n hn
  · exact mixedElementary_tail q hq 4 n hn
  · exact mixedG2prime_tail q hq n hn

/-- Every coefficient of a block polynomial agrees with its full elementary sequence. -/
theorem middleFlagCoefficientPolynomial_coeff (q : MixedParams) (hq : MixedValid q)
    (i : Fin 4) (n : ℕ) :
    (middleFlagCoefficientPolynomial q i).coeff n =
      (-1) ^ n * mixedEvaluation q (middleFlagElementary i n) := by
  apply coefficientPoly_coeff_of_tail
  intro j hj
  rw [middleFlagElementary_tail q hq i j hj, mul_zero]

/-- Empty elementary alphabets have no positive power sums. -/
theorem mixedAlphabetPowerSum_empty (q : MixedParams) (hq : MixedValid q)
    (i : Fin 5) (hi : mixedLengths q i = 0) (s : ℕ) (hs : 0 < s) :
    mixedAlphabetPowerSum (mixedEvaluation q) i (mixedLengths q i) s = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  simp only [mixedAlphabetPowerSum, powerSumOfCoeff]
  have hz (j : ℕ) (hj : 0 < j) : mixedEvaluation q (mixedE i j) = 0 :=
    mixedElementary_tail q hq i j (by omega)
  rw [hz (n + 1) (by omega), mul_zero, smul_zero]
  rw [zero_sub, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j _
  rw [hz (j.val + 1) (by omega), mul_zero, mul_zero]

/-- Newton reconstruction identifies the four Cartan tail symbols with the flag blocks. -/
theorem middleFlag_newtonCoeff (q : MixedParams) (hq : MixedValid q) (hA : q.A = 0)
    (i : Fin 4) (n : ℕ) :
    newtonCoeff (fun s => middleFlagTailSymbols q s i) n =
      (-1) ^ n * mixedEvaluation q (middleFlagElementary i n) := by
  obtain ⟨hd1, hd3⟩ := middleFlag_outer_lengths q hq hA
  have hx0 (s : ℕ) (hs : 0 < s) :
      mixedAlphabetPowerSum (mixedEvaluation q) 0 q.d1.toNat s = 0 :=
    mixedAlphabetPowerSum_empty q hq 0 (by simp [mixedLengths, hd1]) s hs
  have hx2 (s : ℕ) (hs : 0 < s) :
      mixedAlphabetPowerSum (mixedEvaluation q) 2 q.d3.toNat s = 0 :=
    mixedAlphabetPowerSum_empty q hq 2 (by simp [mixedLengths, hd3]) s hs
  fin_cases i
  · have h := congrArg (PowerSeries.coeff n)
      (newtonCoefficientSeries_relativeAlphabet (mixedEvaluation q) mixedU 3 q.e1.toNat _
        (newtonCoefficientSeries_mixedAmbient (mixedEvaluation q) 0 1
          q.d1.toNat q.d2.toNat))
    have hc := newtonCoeff_congr_positive
      (fun s => middleFlagTailSymbols q s 0)
      (fun s => mixedAlphabetPowerSum (mixedEvaluation q) 0 q.d1.toNat s -
        mixedAlphabetPowerSum (mixedEvaluation q) 1 q.d2.toNat s -
        mixedAlphabetPowerSum (mixedEvaluation q) 3 q.e1.toNat s)
      (by intro s hs; simp [middleFlagTailSymbols, mixedLengths, hx0 s hs]) n
    exact hc.trans (by simpa [newtonCoefficientSeries, mixedSignedSeries,
      middleFlagElementary, mixedG1prime] using h)
  · exact newtonCoeff_powerSumOfCoeff q.e1.toNat _ (by simp [mixedE]) n
  · exact newtonCoeff_powerSumOfCoeff q.e2.toNat _ (by simp [mixedE]) n
  · have h := congrArg (PowerSeries.coeff n)
      (newtonCoefficientSeries_relativeAlphabet (mixedEvaluation q) mixedV 4 q.e2.toNat _
        (newtonCoefficientSeries_mixedAmbient (mixedEvaluation q) 1 2
          q.d2.toNat q.d3.toNat))
    have hc := newtonCoeff_congr_positive
      (fun s => middleFlagTailSymbols q s 3)
      (fun s => mixedAlphabetPowerSum (mixedEvaluation q) 1 q.d2.toNat s -
        mixedAlphabetPowerSum (mixedEvaluation q) 2 q.d3.toNat s -
        mixedAlphabetPowerSum (mixedEvaluation q) 4 q.e2.toNat s)
      (by intro s hs; simp [middleFlagTailSymbols, mixedLengths, hx2 s hs]) n
    exact hc.trans (by simpa [newtonCoefficientSeries, mixedSignedSeries,
      middleFlagElementary, mixedG2prime] using h)

/-- The ascending flag polynomial is the Newton coefficient series of its Cartan symbol. -/
theorem middleFlagCoefficientPolynomial_series (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (i : Fin 4) :
    (middleFlagCoefficientPolynomial q i : PowerSeries (MixedRing q)) =
      newtonCoefficientSeries (fun s => middleFlagTailSymbols q s i) := by
  ext n : 1
  rw [Polynomial.coeff_coe, middleFlagCoefficientPolynomial_coeff q hq]
  simpa only [newtonCoefficientSeries, PowerSeries.coeff_mk] using
    (middleFlag_newtonCoeff q hq hA i n).symm

/-- The four ascending flag polynomials multiply to one. -/
theorem middleFlagCoefficientPolynomial_product (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) : ∏ i : Fin 4, middleFlagCoefficientPolynomial q i = 1 := by
  apply Polynomial.coe_injective (MixedRing q)
  simp only [Fin.prod_univ_succ,
    Fin.prod_univ_zero, mul_one, Polynomial.coe_mul, Polynomial.coe_one,
    middleFlagCoefficientPolynomial_series q hq hA]
  rw [← newtonCoefficientSeries_add, ← newtonCoefficientSeries_add,
    ← newtonCoefficientSeries_add]
  convert (newtonCoefficientSeries_zero (R := MixedRing q)) using 1
  congr 1
  funext s
  dsimp [middleFlagTailSymbols]
  ring

/-- The coefficient polynomial of the other three blocks. -/
def middleFlagComplementCoefficientPolynomial (q : MixedParams) (i : Fin 4) :
    (MixedRing q)[X] :=
  ∏ j ∈ Finset.univ.erase i, middleFlagCoefficientPolynomial q j

/-- Each block has the other three blocks as its polynomial inverse. -/
theorem middleFlagCoefficientPolynomial_complement (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (i : Fin 4) :
    middleFlagCoefficientPolynomial q i * middleFlagComplementCoefficientPolynomial q i =
      1 := by
  rw [middleFlagComplementCoefficientPolynomial, Finset.mul_prod_erase _ _ (by simp)]
  exact middleFlagCoefficientPolynomial_product q hq hA

/-- The last-mode symbol is the differentiated block constant times its complement constant. -/
theorem middleFlagTailSymbols_last_mode (q : MixedParams) (hq : MixedValid q)
    (hA : q.A = 0) (hB : 2 ≤ q.B) (i : Fin 4) :
    middleFlagTailSymbols q (q.B.toNat - 1) i =
      (middleFlagPolynomial q i).coeff 1 *
        ∏ j ∈ Finset.univ.erase i, (middleFlagPolynomial q j).coeff 0 := by
  let d := middleFlagLength q i
  let e := ∑ j ∈ Finset.univ.erase i, middleFlagLength q j
  have hlen : d + e = q.B.toNat := by
    rw [← middleFlagLength_sum q hq hA]
    exact Finset.add_sum_erase Finset.univ (middleFlagLength q) (Finset.mem_univ i)
  have hdeg (j : Fin 4) :
      (middleFlagCoefficientPolynomial q j).natDegree ≤ middleFlagLength q j :=
    coefficientPoly_degree _ _
  have he : (middleFlagComplementCoefficientPolynomial q i).natDegree ≤ e :=
    (natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun j _ => hdeg j))
  have hf : (middleFlagCoefficientPolynomial q i).coeff 0 = 1 := by
    rw [middleFlagCoefficientPolynomial_coeff q hq]
    fin_cases i <;> simp [middleFlagElementary, mixed_series_zero, mixedE]
  have hc : (middleFlagCoefficientPolynomial q i).coeff =
      newtonCoeff (fun s => middleFlagTailSymbols q s i) := by
    funext n
    rw [middleFlagCoefficientPolynomial_coeff q hq, middleFlag_newtonCoeff q hq hA]
  have hp := powerSumOfCoeff_last_mode (middleFlagCoefficientPolynomial q i)
    (middleFlagComplementCoefficientPolynomial q i) d e hf
    (middleFlagCoefficientPolynomial_complement q hq hA i) (hdeg i) he (by omega)
  rw [hc, powerSumOfCoeff_newtonCoeff _ _ _ (by omega), hlen] at hp
  rw [hp]
  congr 1
  rw [coeff_reflect, revAt_zero]
  change (∏ j ∈ Finset.univ.erase i, middleFlagCoefficientPolynomial q j).coeff
      (∑ j ∈ Finset.univ.erase i, middleFlagLength q j) = _
  rw [coefficient_prod_sum_degrees _ _ _ (fun j _ => hdeg j)]
  apply Finset.prod_congr rfl
  intro j _
  exact (show (middleFlagPolynomial q j).coeff 0 =
    (middleFlagCoefficientPolynomial q j).coeff (middleFlagLength q j) by
      rw [middleFlagPolynomial, coeff_reflect, revAt_zero]).symm

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.middleFlagLength_sum
#print axioms VOA.DeligneAudit.SL4T.middleFlagElementary_tail
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_coeff
#print axioms VOA.DeligneAudit.SL4T.mixedAlphabetPowerSum_empty
#print axioms VOA.DeligneAudit.SL4T.middleFlag_newtonCoeff
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_series
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_product
#print axioms VOA.DeligneAudit.SL4T.middleFlagCoefficientPolynomial_complement
#print axioms VOA.DeligneAudit.SL4T.middleFlagTailSymbols_last_mode
