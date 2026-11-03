import VOA.DeligneAudit.SL4TMarkedFlagRing

/-!
# Vanishing identities and cutoff exchanges in marked full flags

For a coinvariant alphabet (all positive elementary functions vanish) the complete series of a
group of roots is the signed elementary polynomial of the complementary group
(`groupCompleteSeries_eq_complement`). Hence the complete function of two roots vanishes in every
degree above the size of the complement, and also in degree equal to that size when the product of
the complement vanishes (`pairComplete_vanish`). This replaces the inverse power series argument of
the note: the products `prod V = 0` enter only through the product of the complement.

The cutoff exchanges are proved for an arbitrary commutative algebra with a coinvariant alphabet
satisfying the stated relations:

* `pair_boundary_mem_of_product` and `pair_boundary_mem_of_card`: for a root `a` with `a^N = 0`
  and another root `u`, `a^(N-1) u^k ∈ (u^(k+1))` when the complete function of degree
  `N + k - 1` vanishes; these give all two-root cutoff exchanges of the marked recursions.
* `pair_middle_zero`: the middle relation `x^h y^h = 0`.
* `powerSum_boundary_mem`: the power-sum exchange.
* `group_power_product_zero`: `y^h` kills the product of the other roots of its group.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

variable {A : Type*} [CommRing A]

/-! ### Group polynomials -/

section Group

variable {ι : Type*} [DecidableEq ι]

/-- The signed elementary polynomial `∏_{i ∈ S} (1 - x_i t)` of a group of roots. -/
def groupElementaryPolynomial (x : ι → A) (S : Finset ι) : Polynomial A :=
  ∏ i ∈ S, (1 - Polynomial.C (x i) * Polynomial.X)

/-- The complete series `∏_{i ∈ S} (1 - x_i t)⁻¹` of a group of roots. -/
def groupCompleteSeries (x : ι → A) (S : Finset ι) : PowerSeries A :=
  ∏ i ∈ S, D4Levi.ksGeometricSeries (x i)

theorem groupCompleteSeries_mul_elementary (x : ι → A) (S : Finset ι) :
    groupCompleteSeries x S * (groupElementaryPolynomial x S : PowerSeries A) = 1 := by
  have hc : ((groupElementaryPolynomial x S : Polynomial A) : PowerSeries A) =
      ∏ i ∈ S, ((1 - Polynomial.C (x i) * Polynomial.X : Polynomial A) : PowerSeries A) :=
    map_prod Polynomial.coeToPowerSeries.ringHom _ _
  rw [hc, groupCompleteSeries, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_X]
  exact D4Levi.ksGeometricSeries_mul_linear (x i)

/-- In a coinvariant alphabet the complete series of a group is the signed elementary
polynomial of the complementary group. -/
theorem groupCompleteSeries_eq_complement [Fintype ι] (x : ι → A) (S : Finset ι)
    (hE : groupElementaryPolynomial x Finset.univ = 1) :
    groupCompleteSeries x S = (groupElementaryPolynomial x Sᶜ : PowerSeries A) := by
  have hsplit : groupElementaryPolynomial x S * groupElementaryPolynomial x Sᶜ = 1 := by
    rw [← hE, groupElementaryPolynomial, groupElementaryPolynomial, groupElementaryPolynomial,
      ← Finset.prod_union disjoint_compl_right, Finset.union_compl]
  calc groupCompleteSeries x S
      = groupCompleteSeries x S *
          ((groupElementaryPolynomial x S * groupElementaryPolynomial x Sᶜ : Polynomial A) :
            PowerSeries A) := by rw [hsplit, Polynomial.coe_one, mul_one]
    _ = (groupCompleteSeries x S * (groupElementaryPolynomial x S : PowerSeries A)) *
          (groupElementaryPolynomial x Sᶜ : PowerSeries A) := by
        rw [Polynomial.coe_mul, mul_assoc]
    _ = _ := by rw [groupCompleteSeries_mul_elementary, one_mul]

theorem groupElementaryPolynomial_natDegree_le (x : ι → A) (S : Finset ι) :
    (groupElementaryPolynomial x S).natDegree ≤ S.card := by
  rw [groupElementaryPolynomial]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc ∑ i ∈ S, (1 - Polynomial.C (x i) * Polynomial.X).natDegree ≤ ∑ _i ∈ S, 1 := by
        apply Finset.sum_le_sum
        intro i _
        apply (Polynomial.natDegree_sub_le _ _).trans
        exact max_le (by simp)
          ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
    _ = S.card := by simp

/-- The signed elementary polynomial of a group has no coefficient above the group size. -/
theorem groupElementaryPolynomial_coeff_eq_zero (x : ι → A) (S : Finset ι) (m : ℕ)
    (hm : S.card < m) : (groupElementaryPolynomial x S).coeff m = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt
    ((groupElementaryPolynomial_natDegree_le x S).trans_lt hm)

/-- The top coefficient of the signed elementary polynomial is the signed product. -/
theorem groupElementaryPolynomial_coeff_card (x : ι → A) (S : Finset ι) :
    (groupElementaryPolynomial x S).coeff S.card = (-1) ^ S.card * ∏ i ∈ S, x i := by
  induction S using Finset.induction_on with
  | empty => simp [groupElementaryPolynomial]
  | insert a S ha ih =>
      rw [groupElementaryPolynomial, Finset.prod_insert ha, ← groupElementaryPolynomial,
        Finset.card_insert_of_notMem ha, Finset.prod_insert ha, sub_mul, one_mul,
        Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, ih,
        groupElementaryPolynomial_coeff_eq_zero x S (S.card + 1) (by omega)]
      ring

/-- The complete function of two distinct roots. -/
theorem pairCompleteSeries_coeff (x : ι → A) (a b : ι) (hab : a ≠ b) (m : ℕ) :
    PowerSeries.coeff m (groupCompleteSeries x {a, b}) =
      ∑ e ∈ Finset.range (m + 1), x a ^ e * x b ^ (m - e) := by
  rw [groupCompleteSeries, Finset.prod_pair hab, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [D4Levi.ksGeometricSeries]

/-- In a coinvariant alphabet the complete function of two roots vanishes above the size of
the complement, and at that size when the product of the complement vanishes. -/
theorem pairComplete_vanish [Fintype ι] (x : ι → A)
    (hE : groupElementaryPolynomial x Finset.univ = 1) (a b : ι) (hab : a ≠ b) (m : ℕ)
    (hm : ({a, b}ᶜ : Finset ι).card < m ∨
      (({a, b}ᶜ : Finset ι).card = m ∧ ∏ i ∈ ({a, b}ᶜ : Finset ι), x i = 0)) :
    ∑ e ∈ Finset.range (m + 1), x a ^ e * x b ^ (m - e) = 0 := by
  rw [← pairCompleteSeries_coeff x a b hab, groupCompleteSeries_eq_complement x _ hE,
    Polynomial.coeff_coe]
  rcases hm with hm | ⟨hm, hp⟩
  · exact groupElementaryPolynomial_coeff_eq_zero _ _ _ hm
  · rw [← hm, groupElementaryPolynomial_coeff_card, hp, mul_zero]

theorem pairComplement_card [Fintype ι] (a b : ι) (hab : a ≠ b) :
    ({a, b}ᶜ : Finset ι).card = Fintype.card ι - 2 := by
  rw [Finset.card_compl, Finset.card_pair hab]

/-- A product over a group containing a group with vanishing product vanishes. -/
theorem prod_eq_zero_of_subset (x : ι → A) {V Z : Finset ι} (hVZ : V ⊆ Z)
    (hV : ∏ i ∈ V, x i = 0) : ∏ i ∈ Z, x i = 0 := by
  rw [← Finset.prod_sdiff hVZ, hV, mul_zero]

end Group

/-- The signed elementary polynomial of a tuple is that of the full group of positions. -/
theorem ksEPoly_ofFn_eq_group {n : ℕ} (x : Fin n → A) :
    D4Levi.ksEPoly (List.ofFn x) = groupElementaryPolynomial x Finset.univ := by
  simp only [D4Levi.ksEPoly, List.map_ofFn, List.prod_ofFn, groupElementaryPolynomial,
    Function.comp_def]

/-! ### Exchanges -/

/-- Raising both exponents of an exchange relation by the same amount. -/
theorem mem_span_pow_succ_of_le (y z : A) (k i : ℕ) (hki : k ≤ i)
    (h : y * z ^ k ∈ Ideal.span {z ^ (k + 1)}) : y * z ^ i ∈ Ideal.span {z ^ (i + 1)} := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨a, ?_⟩
  calc a * z ^ (i + 1) = (a * z ^ (k + 1)) * z ^ (i - k) := by
        rw [mul_assoc, ← pow_add, show k + 1 + (i - k) = i + 1 by omega]
    _ = (y * z ^ k) * z ^ (i - k) := by rw [ha]
    _ = y * z ^ i := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hki]

section Exchange

variable {n : ℕ} (x : Fin n → A) (hE : groupElementaryPolynomial x Finset.univ = 1)
include hE

/-- Cutoff exchange through a vanishing product: if `a, u` lie outside a group `V` with
`prod V = 0`, `a^N = 0` and there are `N + k + 1` roots, then `a^(N-1) u^k ∈ (u^(k+1))`. -/
theorem pair_boundary_mem_of_product (V : Finset (Fin n)) (hV : ∏ i ∈ V, x i = 0)
    (a u : Fin n) (hau : a ≠ u) (ha : a ∉ V) (hu : u ∉ V) (N k : ℕ) (hN : 0 < N)
    (hn : n = N + k + 1) (hx : x a ^ N = 0) :
    x a ^ (N - 1) * x u ^ k ∈ Ideal.span {x u ^ (k + 1)} := by
  apply twoRoot_boundary_power_mem (x a) (x u) N k hN hx
  have h := pairComplete_vanish x hE a u hau (N + k - 1) (Or.inr ⟨by
    rw [pairComplement_card a u hau, Fintype.card_fin]; omega, by
    apply prod_eq_zero_of_subset x _ hV
    intro i hi
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha (h ▸ hi), fun h => hu (h ▸ hi)⟩⟩)
  simpa only [show N + k - 1 + 1 = N + k by omega] using h

/-- Cutoff exchange by size: if `a^N = 0` and there are at most `N + k` roots, then
`a^(N-1) u^k ∈ (u^(k+1))`. -/
theorem pair_boundary_mem_of_card (a u : Fin n) (hau : a ≠ u) (N k : ℕ) (hN : 0 < N)
    (hn : n ≤ N + k) (hx : x a ^ N = 0) :
    x a ^ (N - 1) * x u ^ k ∈ Ideal.span {x u ^ (k + 1)} := by
  apply twoRoot_boundary_power_mem (x a) (x u) N k hN hx
  have h := pairComplete_vanish x hE a u hau (N + k - 1) (Or.inl (by
    rw [pairComplement_card a u hau, Fintype.card_fin]; omega))
  simpa only [show N + k - 1 + 1 = N + k by omega] using h

end Exchange

/-- Two roots with cutoff `h + 1` whose complete function of degree `2h` vanishes have
`x^h y^h = 0`. -/
theorem pair_middle_zero (x y : A) (h : ℕ) (hx : x ^ (h + 1) = 0) (hy : y ^ (h + 1) = 0)
    (hs : ∑ e ∈ Finset.range (2 * h + 1), x ^ e * y ^ (2 * h - e) = 0) : x ^ h * y ^ h = 0 := by
  rw [Finset.sum_eq_single h] at hs
  · simpa only [show 2 * h - h = h by omega] using hs
  · intro e _ hne
    by_cases he : h < e
    · rw [pow_eq_zero_of_le (by omega) hx, zero_mul]
    · rw [pow_eq_zero_of_le (show h + 1 ≤ 2 * h - e by omega) hy, mul_zero]
  · intro hh
    exact absurd (Finset.mem_range.mpr (by omega)) hh

/-- In a coinvariant alphabet of at most `2h + 1` roots with cutoff `h + 1`, any two
distinct roots satisfy `x^h y^h = 0`. -/
theorem pair_middle_zero_of_card {n : ℕ} (x : Fin n → A)
    (hE : groupElementaryPolynomial x Finset.univ = 1) (a b : Fin n) (hab : a ≠ b) (h : ℕ)
    (hn : n ≤ 2 * h + 1) (ha : x a ^ (h + 1) = 0) (hb : x b ^ (h + 1) = 0) :
    x a ^ h * x b ^ h = 0 := by
  apply pair_middle_zero _ _ h ha hb
  apply pairComplete_vanish x hE a b hab (2 * h) (Or.inl _)
  rw [pairComplement_card a b hab, Fintype.card_fin]
  omega

/-- The power-sum exchange. Here `pU e` stands for the power sums of the
first group without the deleted root `u`, `pV e` for those of the second group, and the relation
`hrel` is the sum over the first group of the vanishing complete functions of degree `M`. -/
theorem powerSum_boundary_mem (pU pV : ℕ → A) (u : A) (M K h : ℕ) (hh : 2 ≤ h)
    (hM : M + 1 = K + h)
    (hrel : ∑ e ∈ Finset.range (M + 1), pU e * u ^ (M - e) = 0)
    (hsplit : pU (h - 1) = -pV (h - 1) - u ^ (h - 1))
    (htail : ∀ e, h ≤ e → pU e = -u ^ e) :
    pV (h - 1) * u ^ K ∈ Ideal.span {u ^ (K + 1)} := by
  let q := Ideal.Quotient.mk (Ideal.span {u ^ (K + 1)})
  have hu : q u ^ (K + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hr := congrArg q hrel
  simp only [map_sum, map_mul, map_pow, map_zero] at hr
  rw [Finset.sum_eq_single (h - 1)] at hr
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hM' : M - (h - 1) = K := by omega
    rw [hM', hsplit, map_sub, map_neg, map_pow, sub_mul, neg_mul, ← pow_add,
      show h - 1 + K = M by omega, pow_eq_zero_of_le (show K + 1 ≤ M by omega) hu,
      sub_zero, neg_eq_zero] at hr
    simpa only [map_mul, map_pow] using hr
  · intro e he hne
    by_cases hle : h ≤ e
    · rw [htail e hle, map_neg, map_pow, neg_mul, ← pow_add,
        show e + (M - e) = M by have := Finset.mem_range.mp he; omega,
        pow_eq_zero_of_le (show K + 1 ≤ M by omega) hu, neg_zero]
    · rw [pow_eq_zero_of_le (show K + 1 ≤ M - e by omega) hu, mul_zero]
  · intro hh'
    exact absurd (Finset.mem_range.mpr (by omega)) hh'

/-- If the `h`-th power sum of a group vanishes and every root of the group has cutoff
`h + 1`, then `y^h` kills the product of the other roots of the group. -/
theorem group_power_product_zero {ι : Type*} [DecidableEq ι] (x : ι → A) (U : Finset ι)
    (y : ι) (hy : y ∈ U) (h : ℕ) (hp : ∑ i ∈ U, x i ^ h = 0)
    (hc : ∀ i ∈ U, x i ^ (h + 1) = 0) : x y ^ h * ∏ i ∈ U.erase y, x i = 0 := by
  have hz := congrArg (· * ∏ i ∈ U.erase y, x i) hp
  simp only [zero_mul, Finset.sum_mul] at hz
  rw [Finset.sum_eq_single y] at hz
  · exact hz
  · intro i hi hne
    rw [← Finset.mul_prod_erase (U.erase y) x (Finset.mem_erase.mpr ⟨hne, hi⟩), ← mul_assoc,
      ← pow_succ, hc i hi, zero_mul]
  · intro hn
    exact absurd hy hn

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.groupCompleteSeries_mul_elementary
#print axioms VOA.DeligneAudit.SL4T.groupCompleteSeries_eq_complement
#print axioms VOA.DeligneAudit.SL4T.groupElementaryPolynomial_natDegree_le
#print axioms VOA.DeligneAudit.SL4T.groupElementaryPolynomial_coeff_eq_zero
#print axioms VOA.DeligneAudit.SL4T.groupElementaryPolynomial_coeff_card
#print axioms VOA.DeligneAudit.SL4T.pairCompleteSeries_coeff
#print axioms VOA.DeligneAudit.SL4T.pairComplete_vanish
#print axioms VOA.DeligneAudit.SL4T.pairComplement_card
#print axioms VOA.DeligneAudit.SL4T.prod_eq_zero_of_subset
#print axioms VOA.DeligneAudit.SL4T.ksEPoly_ofFn_eq_group
#print axioms VOA.DeligneAudit.SL4T.mem_span_pow_succ_of_le
#print axioms VOA.DeligneAudit.SL4T.pair_boundary_mem_of_product
#print axioms VOA.DeligneAudit.SL4T.pair_boundary_mem_of_card
#print axioms VOA.DeligneAudit.SL4T.pair_middle_zero
#print axioms VOA.DeligneAudit.SL4T.pair_middle_zero_of_card
#print axioms VOA.DeligneAudit.SL4T.powerSum_boundary_mem
#print axioms VOA.DeligneAudit.SL4T.group_power_product_zero
