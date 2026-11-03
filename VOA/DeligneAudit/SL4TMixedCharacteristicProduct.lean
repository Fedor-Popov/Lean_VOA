import VOA.DeligneAudit.SL4TMixedRelativeTail
import VOA.DeligneAudit.SL4TMixedTruncationIdentity

/-! # Characteristic factorizations of the mixed alphabets -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-- Multiplication of finite signed coefficient series realizes coefficient convolution. -/
theorem mixedConv_signed_coefficient_product (φ : MixedPoly →+* R)
    (f g : ℕ → MixedPoly) (d e : ℕ)
    (hf : ∀ j, d < j → φ (f j) = 0) (hg : ∀ j, e < j → φ (g j) = 0) :
    coefficientPoly (fun j => (-1) ^ j * φ (f j)) d *
        coefficientPoly (fun j => (-1) ^ j * φ (g j)) e =
      coefficientPoly (fun j => (-1) ^ j * φ (mixedConv f g j)) (d + e) := by
  have hfc := coefficientPoly_coeff_of_tail (fun j => (-1) ^ j * φ (f j)) d
    (fun j hj => by dsimp; rw [hf j hj, mul_zero])
  have hgc := coefficientPoly_coeff_of_tail (fun j => (-1) ^ j * φ (g j)) e
    (fun j hj => by dsimp; rw [hg j hj, mul_zero])
  have hcc := coefficientPoly_coeff_of_tail
    (fun j => (-1) ^ j * φ (mixedConv f g j)) (d + e)
    (fun j hj => by dsimp; rw [mixedConv_tail φ f g d e hf hg j hj, mul_zero])
  ext n : 1
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [hfc, hgc, hcc]
  simp only [mixedConv, map_sum, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  calc
    _ = ((-1 : R) ^ i * (-1) ^ (n - i)) * (φ (f i) * φ (g (n - i))) := by ring
    _ = _ := by rw [← pow_add, show i + (n - i) = n by omega]

/-- Reflection turns the signed convolution identity into characteristic multiplication. -/
theorem mixedConv_characteristic_product (φ : MixedPoly →+* R)
    (f g : ℕ → MixedPoly) (d e : ℕ)
    (hf : ∀ j, d < j → φ (f j) = 0) (hg : ∀ j, e < j → φ (g j) = 0) :
    descendingPoly (fun j => (-1) ^ j * φ (f j)) d *
        descendingPoly (fun j => (-1) ^ j * φ (g j)) e =
      descendingPoly (fun j => (-1) ^ j * φ (mixedConv f g j)) (d + e) := by
  unfold descendingPoly
  rw [← reflect_mul _ _ (coefficientPoly_degree _ _) (coefficientPoly_degree _ _),
    mixedConv_signed_coefficient_product φ f g d e hf hg]

/-- Applying the characteristic sign to the complementary coefficients removes both signs. -/
theorem mixedComplete_characteristic_sign (φ : MixedPoly →+* R) (i : Fin 5) (d : ℕ) :
    descendingPoly (fun j => (-1) ^ j * φ ((-1) ^ j * mixedH i j)) d =
      descendingPoly (fun j => φ (mixedH i j)) d := by
  congr 1
  funext j
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [← mul_assoc, ← mul_pow]
  simp

/-- The unsigned elementary and complementary coefficients multiply to the unit series. -/
theorem mixedElementary_complement_convolution (i : Fin 5) (n : ℕ) :
    mixedConv (mixedE i) (fun j => (-1) ^ j * mixedH i j) n =
      if n = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n) (mixedAlphabet_series_inverse i)
  rw [← mixedConv_series, PowerSeries.coeff_mk, PowerSeries.coeff_one] at h
  exact h

/-- Every elementary alphabet has its defining generator tail in the mixed ring. -/
theorem mixedElementary_tail (q : MixedParams) (hq : MixedValid q) (i : Fin 5)
    (n : ℕ) (hn : mixedLengths q i < n) : mixedEvaluation q (mixedE i n) = 0 :=
  mixedRelation_zero q hq _ (Or.inl ⟨i, n, hn, rfl⟩)

/-- The characteristic polynomial of a chosen base alphabet. -/
def mixedBaseChosenPolynomial (q : MixedParams) (i : Fin 3) : (MixedRing q)[X] :=
  descendingPoly (fun j => (-1) ^ j * mixedEvaluation q (mixedE (mixedBaseIndex i) j))
    (mixedBaseLength q i).toNat

/-- The characteristic polynomial of a complementary base alphabet. -/
def mixedBaseComplementPolynomial (q : MixedParams) (i : Fin 3) : (MixedRing q)[X] :=
  descendingPoly (fun j => mixedEvaluation q (mixedH (mixedBaseIndex i) j))
    (mixedBaseSize q i - mixedBaseLength q i).toNat

/-- Each base alphabet and its complement factor the appropriate pure power. -/
theorem mixedBase_characteristic_product (q : MixedParams) (hq : MixedValid q) (i : Fin 3) :
    mixedBaseChosenPolynomial q i * mixedBaseComplementPolynomial q i =
      X ^ (mixedBaseSize q i).toNat := by
  have hv := mixedBase_valid q hq i
  have hs : (mixedBaseLength q i).toNat +
      (mixedBaseSize q i - mixedBaseLength q i).toNat = (mixedBaseSize q i).toNat := by omega
  have h := mixedConv_characteristic_product (mixedEvaluation q).toRingHom
    (mixedE (mixedBaseIndex i)) (fun j => (-1) ^ j * mixedH (mixedBaseIndex i) j)
    (mixedBaseLength q i).toNat (mixedBaseSize q i - mixedBaseLength q i).toNat
    (mixedBase_elementary_tail q hq i) (by
      intro j hj
      simp only [map_mul, map_pow, map_neg, map_one]
      exact mul_eq_zero_of_right _ (mixedBase_complete_tail q hq i j hj))
  rw [mixedComplete_characteristic_sign, hs] at h
  change mixedBaseChosenPolynomial q i * mixedBaseComplementPolynomial q i = _ at h
  rw [h]
  rw [descendingPoly_eq_sum, Finset.sum_eq_single 0]
  · simp [mixedElementary_complement_convolution]
  · intro j _ hj
    simp [mixedElementary_complement_convolution, hj]
  · intro hz
    exact False.elim (hz (Finset.mem_range.mpr (by omega)))

/-- The first relative complementary characteristic polynomial. -/
def mixedFirstComplementPolynomial (q : MixedParams) : (MixedRing q)[X] :=
  descendingPoly (fun j => (-1) ^ j * mixedEvaluation q (mixedG1prime j))
    (mixedP q - q.e1).toNat

/-- The characteristic polynomial of the chosen part of the second ambient alphabet. -/
def mixedSecondChosenPolynomial (q : MixedParams) : (MixedRing q)[X] :=
  descendingPoly (fun j => (-1) ^ j * mixedEvaluation q (mixedE 4 j)) q.e2.toNat

/-- The first relative factorization, with no extra infinite relations imposed. -/
theorem mixedFirst_relative_factorization (q : MixedParams) (hq : MixedValid q) :
    mixedFirstPolynomial q * mixedFirstComplementPolynomial q =
      mixedBaseChosenPolynomial q 0 * mixedBaseComplementPolynomial q 1 := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  have hs : q.e1.toNat + (mixedP q - q.e1).toNat = (mixedP q).toNat := by
    simp only [mixedP]
    omega
  have ht : q.d1.toNat + (q.B - q.d2).toNat = (mixedP q).toNat := by
    simp only [mixedP]
    omega
  have h := mixedConv_characteristic_product (mixedEvaluation q).toRingHom
    (mixedE 3) mixedG1prime q.e1.toNat (mixedP q - q.e1).toNat
    (mixedElementary_tail q hq 3) (mixedG1prime_tail q hq)
  simp only [mixedG1prime_convolution, hs] at h
  have hbase := mixedConv_characteristic_product (mixedEvaluation q).toRingHom
    (mixedE 0) (fun j => (-1) ^ j * mixedH 1 j) q.d1.toNat (q.B - q.d2).toNat
    (mixedBase_elementary_tail q hq 0) (by
      intro j hj
      simp only [map_mul, map_pow, map_neg, map_one]
      exact mul_eq_zero_of_right _ (mixedBase_complete_tail q hq 1 j hj))
  rw [mixedComplete_characteristic_sign, ht] at hbase
  exact h.trans hbase.symm

/-- The second relative factorization. -/
theorem mixedSecond_relative_factorization (q : MixedParams) (hq : MixedValid q) :
    mixedSecondChosenPolynomial q * mixedSecondPolynomial q =
      mixedBaseChosenPolynomial q 1 * mixedBaseComplementPolynomial q 2 := by
  have hv := hq
  simp only [MixedValid, mixedP, mixedQ] at hv
  have hs : q.e2.toNat + (mixedQ q - q.e2).toNat = (mixedQ q).toNat := by
    simp only [mixedQ]
    omega
  have ht : q.d2.toNat + (q.A - q.d3).toNat = (mixedQ q).toNat := by
    simp only [mixedQ]
    omega
  have h := mixedConv_characteristic_product (mixedEvaluation q).toRingHom
    (mixedE 4) mixedG2prime q.e2.toNat (mixedQ q - q.e2).toNat
    (mixedElementary_tail q hq 4) (mixedG2prime_tail q hq)
  simp only [mixedG2prime_convolution, hs] at h
  have hbase := mixedConv_characteristic_product (mixedEvaluation q).toRingHom
    (mixedE 1) (fun j => (-1) ^ j * mixedH 2 j) q.d2.toNat (q.A - q.d3).toNat
    (mixedBase_elementary_tail q hq 1) (by
      intro j hj
      simp only [map_mul, map_pow, map_neg, map_one]
      exact mul_eq_zero_of_right _ (mixedBase_complete_tail q hq 2 j hj))
  rw [mixedComplete_characteristic_sign, ht] at hbase
  exact h.trans hbase.symm

/-- The complement of the first selected alphabet in the full set of sites. -/
def mixedFirstAmbientComplement (q : MixedParams) : (MixedRing q)[X] :=
  mixedFirstComplementPolynomial q * mixedBaseComplementPolynomial q 0 *
    mixedBaseChosenPolynomial q 1

/-- The complement of the second complementary alphabet in the full set of sites. -/
def mixedSecondAmbientComplement (q : MixedParams) : (MixedRing q)[X] :=
  mixedSecondChosenPolynomial q * mixedBaseComplementPolynomial q 1 *
    mixedBaseChosenPolynomial q 2

/-- The first alphabet embeds as a characteristic factor of the total-site power. -/
theorem mixedFirst_ambient_factorization (q : MixedParams) (hq : MixedValid q) :
    mixedFirstPolynomial q * mixedFirstAmbientComplement q = X ^ (q.A + q.B).toNat := by
  have hv := hq
  simp only [MixedValid] at hv
  unfold mixedFirstAmbientComplement
  calc
    _ = (mixedFirstPolynomial q * mixedFirstComplementPolynomial q) *
        mixedBaseComplementPolynomial q 0 * mixedBaseChosenPolynomial q 1 := by ring
    _ = (mixedBaseChosenPolynomial q 0 * mixedBaseComplementPolynomial q 1) *
        mixedBaseComplementPolynomial q 0 * mixedBaseChosenPolynomial q 1 := by
          rw [mixedFirst_relative_factorization q hq]
    _ = (mixedBaseChosenPolynomial q 0 * mixedBaseComplementPolynomial q 0) *
        (mixedBaseChosenPolynomial q 1 * mixedBaseComplementPolynomial q 1) := by ring
    _ = X ^ ((mixedBaseSize q 0).toNat + (mixedBaseSize q 1).toNat) := by
      rw [mixedBase_characteristic_product q hq 0,
        mixedBase_characteristic_product q hq 1, ← pow_add]
    _ = _ := by congr 1; change q.A.toNat + q.B.toNat = (q.A + q.B).toNat; omega

/-- The second alphabet likewise has an explicit complement in all sites. -/
theorem mixedSecond_ambient_factorization (q : MixedParams) (hq : MixedValid q) :
    mixedSecondPolynomial q * mixedSecondAmbientComplement q = X ^ (q.A + q.B).toNat := by
  have hv := hq
  simp only [MixedValid] at hv
  unfold mixedSecondAmbientComplement
  calc
    _ = (mixedSecondChosenPolynomial q * mixedSecondPolynomial q) *
        mixedBaseComplementPolynomial q 1 * mixedBaseChosenPolynomial q 2 := by ring
    _ = (mixedBaseChosenPolynomial q 1 * mixedBaseComplementPolynomial q 2) *
        mixedBaseComplementPolynomial q 1 * mixedBaseChosenPolynomial q 2 := by
          rw [mixedSecond_relative_factorization q hq]
    _ = (mixedBaseChosenPolynomial q 1 * mixedBaseComplementPolynomial q 1) *
        (mixedBaseChosenPolynomial q 2 * mixedBaseComplementPolynomial q 2) := by ring
    _ = X ^ ((mixedBaseSize q 1).toNat + (mixedBaseSize q 2).toNat) := by
      rw [mixedBase_characteristic_product q hq 1,
        mixedBase_characteristic_product q hq 2, ← pow_add]
    _ = _ := by congr 1; change q.B.toNat + q.A.toNat = (q.A + q.B).toNat; omega

theorem mixedBaseChosenPolynomial_constant (q : MixedParams) (i : Fin 3) :
    (mixedBaseChosenPolynomial q i).coeff 0 = (-1) ^ (mixedBaseLength q i).toNat *
      mixedEvaluation q (mixedE (mixedBaseIndex i) (mixedBaseLength q i).toNat) :=
  descendingPoly_constant _ _

theorem mixedBaseComplementPolynomial_constant (q : MixedParams) (i : Fin 3) :
    (mixedBaseComplementPolynomial q i).coeff 0 = mixedEvaluation q
      (mixedH (mixedBaseIndex i) (mixedBaseSize q i - mixedBaseLength q i).toNat) :=
  descendingPoly_constant _ _

theorem mixedFirstComplementPolynomial_constant (q : MixedParams) :
    (mixedFirstComplementPolynomial q).coeff 0 = (-1) ^ (mixedP q - q.e1).toNat *
      mixedEvaluation q (mixedG1prime (mixedP q - q.e1).toNat) :=
  descendingPoly_constant _ _

theorem mixedSecondChosenPolynomial_constant (q : MixedParams) :
    (mixedSecondChosenPolynomial q).coeff 0 = (-1) ^ q.e2.toNat *
      mixedEvaluation q (mixedE 4 q.e2.toNat) := descendingPoly_constant _ _

/-- The first ambient complement has constant term in the second b-chain ideal. -/
theorem mixedFirstAmbientComplement_constant_mem (q : MixedParams) :
    (mixedFirstAmbientComplement q).coeff 0 ∈ mixedBChain q 2 := by
  rw [mixedFirstAmbientComplement, mul_coeff_zero, mul_coeff_zero,
    mixedFirstComplementPolynomial_constant, mixedBaseComplementPolynomial_constant,
    mixedBaseChosenPolynomial_constant]
  have hx : mixedEvaluation q (mixedE 1 q.d2.toNat) ∈ mixedBChain q 2 :=
    mem_principalIdealPrefix _ 2 (1 : Fin 4) (by decide)
  exact (mixedBChain q 2).mul_mem_left _ ((mixedBChain q 2).mul_mem_left _ hx)

/-- The second ambient complementary constant term is annihilated by the b-site top. -/
theorem mixedSecondAmbientComplement_constant_annihilated (q : MixedParams)
    (hq : MixedValid q) (hB : 1 ≤ q.B) :
    mixedEvaluation q (mixedE 1 q.d2.toNat) * (mixedSecondAmbientComplement q).coeff 0 = 0 := by
  rw [mixedSecondAmbientComplement, mul_coeff_zero, mul_coeff_zero,
    mixedSecondChosenPolynomial_constant, mixedBaseComplementPolynomial_constant,
    mixedBaseChosenPolynomial_constant]
  have hc := mixedBase_corner_product q hq 1 hB
  change mixedEvaluation q (mixedE 1 q.d2.toNat) *
    mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat) = 0 at hc
  change mixedEvaluation q (mixedE 1 q.d2.toNat) *
    (((-1) ^ q.e2.toNat * mixedEvaluation q (mixedE 4 q.e2.toNat) *
      mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat)) *
        ((-1) ^ q.d3.toNat * mixedEvaluation q (mixedE 2 q.d3.toNat))) = 0
  linear_combination ((-1) ^ q.e2.toNat * mixedEvaluation q (mixedE 4 q.e2.toNat) *
    (-1) ^ q.d3.toNat * mixedEvaluation q (mixedE 2 q.d3.toNat)) * hc

/-- After the b-sites disappear, the second complementary constant is the double-root Thom class. -/
theorem mixedSecondAmbientComplement_constant_without_b (q : MixedParams)
    (hq : MixedValid q) (hB : q.B = 0) :
    (mixedSecondAmbientComplement q).coeff 0 = (-1) ^ (q.e2.toNat + q.d3.toNat) *
      (mixedEvaluation q (mixedE 4 q.e2.toNat) * mixedEvaluation q (mixedE 2 q.d3.toNat)) := by
  have hd : q.d2 = 0 := by obtain ⟨_, _, _, _, h, h', _⟩ := hq; omega
  rw [mixedSecondAmbientComplement, mul_coeff_zero, mul_coeff_zero,
    mixedSecondChosenPolynomial_constant, mixedBaseComplementPolynomial_constant,
    mixedBaseChosenPolynomial_constant]
  change ((-1) ^ q.e2.toNat * mixedEvaluation q (mixedE 4 q.e2.toNat) *
    mixedEvaluation q (mixedH 1 (q.B - q.d2).toNat)) *
      ((-1) ^ q.d3.toNat * mixedEvaluation q (mixedE 2 q.d3.toNat)) = _
  rw [hB, hd]
  have hh : mixedEvaluation q (mixedH 1 0) = 1 := by simp [mixedH]
  simp only [sub_self, Int.toNat_zero, hh, mul_one, pow_add]
  ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedConv_signed_coefficient_product
#print axioms VOA.DeligneAudit.SL4T.mixedConv_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.mixedComplete_characteristic_sign
#print axioms VOA.DeligneAudit.SL4T.mixedElementary_complement_convolution
#print axioms VOA.DeligneAudit.SL4T.mixedElementary_tail
#print axioms VOA.DeligneAudit.SL4T.mixedBase_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.mixedFirst_relative_factorization
#print axioms VOA.DeligneAudit.SL4T.mixedSecond_relative_factorization

#print axioms VOA.DeligneAudit.SL4T.mixedFirst_ambient_factorization
#print axioms VOA.DeligneAudit.SL4T.mixedSecond_ambient_factorization
#print axioms VOA.DeligneAudit.SL4T.mixedBaseChosenPolynomial_constant
#print axioms VOA.DeligneAudit.SL4T.mixedBaseComplementPolynomial_constant
#print axioms VOA.DeligneAudit.SL4T.mixedFirstComplementPolynomial_constant
#print axioms VOA.DeligneAudit.SL4T.mixedSecondChosenPolynomial_constant
#print axioms VOA.DeligneAudit.SL4T.mixedFirstAmbientComplement_constant_mem
#print axioms VOA.DeligneAudit.SL4T.mixedSecondAmbientComplement_constant_annihilated
#print axioms VOA.DeligneAudit.SL4T.mixedSecondAmbientComplement_constant_without_b
