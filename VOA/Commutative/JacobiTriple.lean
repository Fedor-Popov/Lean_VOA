/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.FourTriangular

/-!
# The Jacobi triple product identity

For any commutative ring `A` and any unit `u ∈ Aˣ`, in `A⟦q⟧`:

  `(1 - u) ∏_{m ≥ 1} (1 - u q^m)(1 - u⁻¹ q^m)(1 - q^m) = ∑_{j ∈ ℤ} (-1)^j u^j q^{j(j-1)/2}`

(`jacobiTriple`).  Taking `A = ℤ[x, x⁻¹]` (or any Laurent-type ring) and `u` a monomial gives the
two-variable identity with `z` Laurent; each `q`-coefficient of both sides is then a Laurent
polynomial in `z`.

Proof: the homogeneous finite q-binomial theorem with `a = q^n`, `b = -u` gives the finite form

  `(u;q)_n (q/u;q)_n = ∑_{|j| ≤ n} (-1)^j u^j q^{j(j-1)/2} [2n, n+j]_q`     (`jacobiTriple_finite`)

and `[2n, n+j]_q → 1/(q)_∞` coefficientwise.
-/

namespace VOA.QSeries.JTP

open PowerSeries VOA.QSeries

open scoped BigOperators

noncomputable section

section Exponent

/-- The exponent `j ↦ j(j-1)/2` on `ℤ`. -/
def pentExp (j : ℤ) : ℕ := (j * (j - 1) / 2).toNat

theorem two_mul_cast_pentExp (j : ℤ) : 2 * ((pentExp j : ℕ) : ℤ) = j * (j - 1) := by
  have heven : 2 ∣ j * (j - 1) := by
    have := Int.even_mul_pred_self j
    exact even_iff_two_dvd.mp this
  have hnn : 0 ≤ j * (j - 1) / 2 := by
    apply Int.ediv_nonneg _ (by norm_num)
    rcases le_or_gt j 0 with h | h <;> nlinarith
  rw [pentExp, Int.toNat_of_nonneg hnn, Int.mul_ediv_cancel' heven]

theorem natAbs_le_pentExp (j : ℤ) : j.natAbs ≤ pentExp j + 1 := by
  have h := two_mul_cast_pentExp j
  zify
  rcases le_or_gt 0 j with hj | hj
  · rw [abs_of_nonneg hj]; nlinarith
  · rw [abs_of_neg hj]; nlinarith

end Exponent

section Triple

theorem two_mul_sum_range_id_add (n : ℕ) : 2 * (∑ j ∈ Finset.range n, j) + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; nlinarith

variable {A : Type*} [CommRing A]

/-- The coefficient `(-1)^j u^j` of the triple-product sum. -/
def tripleCoeff (u : Aˣ) (j : ℤ) : A := negSign j * ((u ^ j : Aˣ) : A)

/-- `∑_{j ∈ ℤ} (-1)^j u^j q^{j(j-1)/2}`. -/
def tripleSum (u : Aˣ) : PowerSeries A := zSeries (tripleCoeff u) pentExp

/-- The factors `(1 - u q^{m+1})(1 - u⁻¹ q^{m+1})(1 - q^{m+1})`. -/
def tripleFactor (u : Aˣ) (m : ℕ) : PowerSeries A :=
  (1 - C (u : A) * X ^ (m + 1)) * (1 - C ((u⁻¹ : Aˣ) : A) * X ^ (m + 1)) * (1 - X ^ (m + 1))

theorem prodFactors_tripleFactor (u : Aˣ) : ProdFactors (tripleFactor u) := by
  have h1 := prodFactors_one_add (R := A) (-(u : A)) (fun m => m + 1) (fun m => Nat.lt_succ_self m)
  have h2 := prodFactors_one_add (R := A) (-((u⁻¹ : Aˣ) : A)) (fun m => m + 1)
    (fun m => Nat.lt_succ_self m)
  have h3 := prodFactors_one_add (R := A) (-1) (fun m => m + 1) (fun m => Nat.lt_succ_self m)
  have := (h1.mul h2).mul h3
  intro m
  simpa [tripleFactor, sub_eq_add_neg] using this m

/-- The sign-unit bookkeeping `(-u)^k = (-u)^n · (-1)^{k-n} u^{k-n}`. -/
theorem neg_C_pow_eq (u : Aˣ) (n k : ℕ) :
    (-C (u : A)) ^ k = (-C (u : A)) ^ n * C (tripleCoeff u ((k : ℤ) - n)) := by
  rcases le_or_gt n k with h | h
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
    have : ((n + r : ℕ) : ℤ) - n = (r : ℤ) := by push_cast; ring
    rw [this, tripleCoeff, negSign, Int.natAbs_natCast, zpow_natCast, pow_add, map_mul, map_pow,
      map_neg, map_one, Units.val_pow_eq_pow_val, map_pow, neg_pow (C (u : A)) r]
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have : (k : ℤ) - ((k + r : ℕ) : ℤ) = -(r : ℤ) := by push_cast; ring
    rw [this, tripleCoeff, negSign, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast,
      ← inv_pow, Units.val_pow_eq_pow_val, map_mul, map_pow, map_pow, map_neg, map_one,
      pow_add, neg_pow (C (u : A)) k, neg_pow (C (u : A)) r]
    have hu : C (u : A) * C ((u⁻¹ : Aˣ) : A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (-1) ^ k * C (u : A) ^ k
        = (-1) ^ k * C (u : A) ^ k * ((-1) ^ r * (-1) ^ r) *
            (C (u : A) * C ((u⁻¹ : Aˣ) : A)) ^ r := by
          rw [hu, one_pow, ← pow_add, ← two_mul, pow_mul]; simp
      _ = _ := by ring

/-- **Finite Jacobi triple product** (Cauchy/MacMahon), division-free. -/
theorem jacobiTriple_finite (u : Aˣ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1 - C (u : A) * X ^ j)) *
        (∏ m ∈ Finset.range n, (1 - C ((u⁻¹ : Aˣ) : A) * X ^ (m + 1))) =
      ∑ k ∈ Finset.range (2 * n + 1),
        C (tripleCoeff u ((k : ℤ) - n)) * X ^ pentExp ((k : ℤ) - n) *
          gaussian (X : PowerSeries A) (2 * n) k := by
  set z : PowerSeries A := C (u : A)
  set zi : PowerSeries A := C ((u⁻¹ : Aˣ) : A)
  have hzz : z * zi = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have h := finite_qBinomial_homog (X : PowerSeries A) (X ^ n) (-z) (2 * n)
  have hprod : (∏ j ∈ Finset.range (2 * n), (X ^ n + -z * X ^ j : PowerSeries A)) =
      X ^ (n * n + ∑ j ∈ Finset.range n, j) * (-z) ^ n *
        ((∏ j ∈ Finset.range n, (1 - z * X ^ j)) *
          (∏ m ∈ Finset.range n, (1 - zi * X ^ (m + 1)))) := by
    rw [show Finset.range (2 * n) = Finset.range (n + n) by rw [two_mul],
      Finset.prod_range_add]
    have hlow : (∏ j ∈ Finset.range n, (X ^ n + -z * X ^ j : PowerSeries A)) =
        (-z) ^ n * X ^ (∑ j ∈ Finset.range n, j) *
          ∏ m ∈ Finset.range n, (1 - zi * X ^ (m + 1)) := by
      rw [← Finset.prod_range_reflect (fun m => (1 - zi * X ^ (m + 1) : PowerSeries A)) n,
        ← Finset.prod_pow_eq_pow_sum,
        show (-z) ^ n = ∏ _j ∈ Finset.range n, (-z) by rw [Finset.prod_const, Finset.card_range],
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [show n - 1 - j + 1 = n - j by omega]
      have hX : (X : PowerSeries A) ^ n = X ^ j * X ^ (n - j) := by
        rw [← pow_add]; congr 1; omega
      rw [hX]
      linear_combination (-(X ^ j * X ^ (n - j))) * hzz
    have hhigh : (∏ i ∈ Finset.range n, (X ^ n + -z * X ^ (n + i) : PowerSeries A)) =
        X ^ (n * n) * ∏ i ∈ Finset.range n, (1 - z * X ^ i) := by
      have hc : (∏ _i ∈ Finset.range n, (X ^ n : PowerSeries A)) = X ^ (n * n) := by
        rw [Finset.prod_const, Finset.card_range, ← pow_mul]
      rw [← hc, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [pow_add]
      ring
    rw [hlow, hhigh, pow_add]
    ring
  rw [hprod] at h
  have hunit : IsUnit (X ^ 0 * (-z) ^ n : PowerSeries A) := by
    rw [pow_zero, one_mul]
    apply IsUnit.pow
    exact ⟨⟨-z, -zi, by rw [neg_mul_neg, hzz], by rw [neg_mul_neg, mul_comm, hzz]⟩, rfl⟩
  have hterm : ∀ k ∈ Finset.range (2 * n + 1),
      weightedGaussian (X : PowerSeries A) (2 * n) k * (-z) ^ k * (X ^ n) ^ (2 * n - k) =
        X ^ 0 * (-z) ^ n * (X ^ (n * n + ∑ j ∈ Finset.range n, j) *
          (C (tripleCoeff u ((k : ℤ) - n)) * X ^ pentExp ((k : ℤ) - n) *
            gaussian (X : PowerSeries A) (2 * n) k)) := by
    intro k hk
    have hk' : k ≤ 2 * n := by have := Finset.mem_range.mp hk; omega
    rw [weightedGaussian_eq, neg_C_pow_eq u n k, ← pow_mul]
    have hexp : k.choose 2 + n * (2 * n - k) =
        (n * n + ∑ j ∈ Finset.range n, j) + pentExp ((k : ℤ) - n) := by
      have h1 := two_mul_choose_two_add k
      have h2 := two_mul_cast_pentExp ((k : ℤ) - n)
      have h3 := two_mul_sum_range_id_add n
      generalize (∑ j ∈ Finset.range n, j) = S at h3 ⊢
      zify [hk'] at h1 h3 ⊢
      nlinarith [h1, h2, h3]
    calc X ^ (k.choose 2) * gaussian X (2 * n) k *
          ((-z) ^ n * C (tripleCoeff u ((k : ℤ) - n))) * X ^ (n * (2 * n - k))
        = (-z) ^ n * (X ^ (k.choose 2 + n * (2 * n - k)) *
            (C (tripleCoeff u ((k : ℤ) - n)) * gaussian X (2 * n) k)) := by
          rw [pow_add]; ring
      _ = _ := by rw [hexp, pow_add]; ring
  apply X_pow_mul_cancel (n * n + ∑ j ∈ Finset.range n, j)
  apply hunit.mul_left_cancel
  calc X ^ 0 * (-z) ^ n * (X ^ (n * n + ∑ j ∈ Finset.range n, j) *
        ((∏ j ∈ Finset.range n, (1 - z * X ^ j)) *
          (∏ m ∈ Finset.range n, (1 - zi * X ^ (m + 1)))))
      = X ^ (n * n + ∑ j ∈ Finset.range n, j) * (-z) ^ n *
        ((∏ j ∈ Finset.range n, (1 - z * X ^ j)) *
          (∏ m ∈ Finset.range n, (1 - zi * X ^ (m + 1)))) := by ring
    _ = _ := h
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl hterm

theorem prodFactors_negC (a : A) :
    ProdFactors fun m => (1 : PowerSeries A) + C (-a) * X ^ (m + 1) :=
  prodFactors_one_add _ (fun m => m + 1) fun m => Nat.lt_succ_self m

theorem infProd_tripleFactor (u : Aˣ) :
    infProd (tripleFactor u) =
      infProd (fun m => (1 : PowerSeries A) + C (-(u : A)) * X ^ (m + 1)) *
        infProd (fun m => (1 : PowerSeries A) + C (-((u⁻¹ : Aˣ) : A)) * X ^ (m + 1)) * euler := by
  rw [infProd_mul (prodFactors_negC _) (prodFactors_negC _), euler_eq_infProd,
    infProd_mul ((prodFactors_negC _).mul (prodFactors_negC _)) prodFactors_euler]
  apply infProd_congr
  intro m
  simp only [tripleFactor, map_neg]
  ring

/-- The product side of the finite identity approximates the infinite product. -/
theorem agreeTo_triple_product (u : Aˣ) (n : ℕ) :
    AgreeTo n ((1 - C (u : A)) *
        (infProd (fun m => (1 : PowerSeries A) + C (-(u : A)) * X ^ (m + 1)) *
          infProd (fun m => (1 : PowerSeries A) + C (-((u⁻¹ : Aˣ) : A)) * X ^ (m + 1))))
      ((∏ j ∈ Finset.range (n + 1), (1 - C (u : A) * X ^ j)) *
        (∏ m ∈ Finset.range (n + 1), (1 - C ((u⁻¹ : Aˣ) : A) * X ^ (m + 1)))) := by
  have hPa := agreeTo_infProd (prodFactors_negC (u : A)) n
  have hPb := agreeTo_infProd (prodFactors_negC ((u⁻¹ : Aˣ) : A)) n
  have hPb' := (hPb.trans (partialProd_agree (prodFactors_negC ((u⁻¹ : Aˣ) : A))
    (Nat.le_succ n)).symm).mono (Nat.le_succ n)
  have h := ((hPa.mono (Nat.le_succ n)).mul hPb').mul_left (1 - C (u : A))
  refine h.trans (AgreeTo.of_eq ?_)
  rw [Finset.prod_range_succ' (fun j => (1 - C (u : A) * X ^ j)), pow_zero, mul_one,
    mul_comm _ (1 - C (u : A)), mul_assoc]
  congr 2
  · apply Finset.prod_congr rfl
    intro m _
    simp only [map_neg]
    ring
  · apply Finset.prod_congr rfl
    intro m _
    simp only [map_neg]
    ring

/-- The sum side of the finite identity approximates `tripleSum u / (q)_∞`. -/
theorem agreeTo_triple_sum (u : Aˣ) (n : ℕ) :
    AgreeTo n (∑ k ∈ Finset.range (2 * (n + 1) + 1),
        C (tripleCoeff u ((k : ℤ) - (n + 1 : ℕ))) * X ^ pentExp ((k : ℤ) - (n + 1 : ℕ)) *
          gaussian (X : PowerSeries A) (2 * (n + 1)) k)
      (tripleSum u * reciprocalEuler) := by
  set M := n + 1 with hM
  have hterm : ∀ k ∈ Finset.range (2 * M + 1),
      AgreeTo n (C (tripleCoeff u ((k : ℤ) - (M : ℕ))) * X ^ pentExp ((k : ℤ) - (M : ℕ)) *
          gaussian (X : PowerSeries A) (2 * M) k)
        (C (tripleCoeff u ((k : ℤ) - (M : ℕ))) * X ^ pentExp ((k : ℤ) - (M : ℕ)) *
          reciprocalEuler) := by
    intro k hk
    have hk' : k ≤ 2 * M := by have := Finset.mem_range.mp hk; omega
    have h1 := agreeTo_gaussian_reciprocalEuler (R := A) (2 * M) k hk'
    have h2 := (h1.X_pow_mul (pentExp ((k : ℤ) - (M : ℕ)))).mul_left
      (C (tripleCoeff u ((k : ℤ) - (M : ℕ))))
    rw [← mul_assoc, ← mul_assoc] at h2
    apply h2.mono
    have hb := natAbs_le_pentExp ((k : ℤ) - (M : ℕ))
    have hmin : min k (2 * M - k) + ((k : ℤ) - (M : ℕ)).natAbs = M := by omega
    omega
  refine (AgreeTo.finset_sum _ hterm).trans ?_
  rw [← Finset.sum_mul]
  refine AgreeTo.mul_right _ ?_
  have hreindex : (∑ k ∈ Finset.range (2 * M + 1),
        C (tripleCoeff u ((k : ℤ) - (M : ℕ))) * X ^ pentExp ((k : ℤ) - (M : ℕ))) =
      ∑ j ∈ Finset.Icc (-((M : ℕ) : ℤ)) (M : ℕ),
        C (tripleCoeff u j) * (X : PowerSeries A) ^ pentExp j := by
    symm
    apply Finset.sum_nbij' (fun (j : ℤ) => (j + (M : ℕ)).toNat)
      (fun (k : ℕ) => (k : ℤ) - (M : ℕ))
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      omega
    · intro k _
      omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have : ((j + (M : ℕ)).toNat : ℤ) - (M : ℕ) = j := by omega
      rw [this]
  rw [hreindex]
  refine (agreeTo_zSeries (tripleCoeff u) pentExp natAbs_le_pentExp
    (K := n) (Finset.Icc (-((M : ℕ) : ℤ)) (M : ℕ)) (fun j hj => ?_)).symm
  have := natAbs_le_pentExp j
  simp only [Finset.mem_Icc]
  omega

/-- **The Jacobi triple product identity.** For `u ∈ Aˣ`, in `A⟦q⟧`:
`(1 - u) ∏_{m ≥ 1} (1 - u q^m)(1 - u⁻¹ q^m)(1 - q^m) = ∑_{j ∈ ℤ} (-1)^j u^j q^{j(j-1)/2}`. -/
theorem jacobiTriple (u : Aˣ) :
    (1 - C (u : A)) * infProd (tripleFactor u) = tripleSum u := by
  have hmain : (1 - C (u : A)) *
      (infProd (fun m => (1 : PowerSeries A) + C (-(u : A)) * X ^ (m + 1)) *
        infProd (fun m => (1 : PowerSeries A) + C (-((u⁻¹ : Aˣ) : A)) * X ^ (m + 1))) =
      tripleSum u * reciprocalEuler := by
    apply eq_of_agreeTo
    intro N
    have h := (agreeTo_triple_product u (N + 1)).trans
      ((AgreeTo.of_eq (jacobiTriple_finite u (N + 1 + 1))).trans (agreeTo_triple_sum u (N + 1)))
    exact h
  rw [infProd_tripleFactor]
  calc (1 - C (u : A)) *
        (infProd (fun m => (1 : PowerSeries A) + C (-(u : A)) * X ^ (m + 1)) *
          infProd (fun m => (1 : PowerSeries A) + C (-((u⁻¹ : Aˣ) : A)) * X ^ (m + 1)) * euler)
      = tripleSum u * (reciprocalEuler * euler) := by linear_combination euler * hmain
    _ = tripleSum u := by rw [mul_comm reciprocalEuler, euler_mul_reciprocal, mul_one]

end Triple

end

end VOA.QSeries.JTP
