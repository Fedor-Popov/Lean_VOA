/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTripleCore
import VOA.Commutative.QBinomialFiniteSum
import VOA.Commutative.QBinomialAlternating

/-!
# Gauss's product for the theta series `φ(x) = ∑_{n ∈ ℤ} x^{n²}`

The specialization `z = 1` of the Jacobi triple product:

  `φ(x) = (x²;x²)_∞ (-x;x²)_∞²`,   `φ(-x) = (x²;x²)_∞ (x;x²)_∞²`.

Proof: the homogeneous finite q-binomial theorem `finite_qBinomial_homog` at base `x²`, with
`a = x^{2n-1}`, `b = 1`, gives the centered finite identity (`gauss_finite`)

  `∑_{k ≤ 2n} x^{(k-n)²} [2n, k]_{x²} = (-x;x²)_n²`,

and `[2n, n+j]_{x²} → 1/(x²;x²)_∞` coefficientwise (`coeff_gaussian_eq_reciprocalQFactorial`).
Everything is division-free over an arbitrary commutative ring.
-/

namespace VOA.QSeries.JTP

open PowerSeries VOA.QSeries

open scoped BigOperators

noncomputable section

section Homogeneous

variable {R : Type*} [CommRing R]

/-- The homogeneous finite q-binomial theorem
`∏_{j<n} (a + b q^j) = ∑_k q^{k(k-1)/2} [n,k]_q b^k a^{n-k}` (weighted form). -/
theorem finite_qBinomial_homog (q a b : R) (n : ℕ) :
    (∏ j ∈ Finset.range n, (a + b * q ^ j)) =
      ∑ k ∈ Finset.range (n + 1), weightedGaussian q n k * b ^ k * a ^ (n - k) := by
  induction n with
  | zero => simp [weightedGaussian]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Finset.sum_range_succ' _ (n + 1)]
      simp only [weightedGaussian_succ_succ, weightedGaussian_zero_right, add_mul,
        Finset.sum_add_distrib, Nat.add_sub_add_right, pow_zero, one_mul, mul_one, Nat.sub_zero]
      have h1 : (∑ k ∈ Finset.range (n + 1), weightedGaussian q n (k + 1) * b ^ (k + 1) *
            a ^ (n - k)) + a ^ (n + 1) =
          (∑ k ∈ Finset.range (n + 1), weightedGaussian q n k * b ^ k * a ^ (n - k)) * a := by
        have h := Finset.sum_range_succ' (fun k => weightedGaussian q n k * b ^ k *
          a ^ (n + 1 - k)) (n + 1)
        rw [Finset.sum_range_succ, weightedGaussian_eq_zero_of_lt q (Nat.lt_succ_self n)] at h
        simp only [zero_mul, add_zero, weightedGaussian_zero_right, pow_zero, mul_one, one_mul,
          Nat.sub_zero, Nat.add_sub_add_right] at h
        rw [← h, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [show n + 1 - k = (n - k) + 1 by have := Finset.mem_range.mp hk; omega, pow_succ]
        ring
      have h2 : (∑ k ∈ Finset.range (n + 1), q ^ n * weightedGaussian q n k * b ^ (k + 1) *
            a ^ (n - k)) =
          (∑ k ∈ Finset.range (n + 1), weightedGaussian q n k * b ^ k * a ^ (n - k)) *
            (b * q ^ n) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [h2, add_right_comm, h1]
      ring

end Homogeneous

section Gauss

variable {R : Type*} [CommRing R]

/-- `1 + X^(e k)` factors are admissible when `e k > k`. -/
theorem prodFactors_one_add_X_pow (e : ℕ → ℕ) (he : ∀ k, k < e k) :
    ProdFactors fun k => (1 : PowerSeries R) + X ^ e k := by
  simpa using prodFactors_one_add (R := R) 1 e he

/-- `1 - X^(e k)` factors are admissible when `e k > k`. -/
theorem prodFactors_one_sub_X_pow (e : ℕ → ℕ) (he : ∀ k, k < e k) :
    ProdFactors fun k => (1 : PowerSeries R) - X ^ e k := by
  simpa [sub_eq_add_neg] using prodFactors_one_add (R := R) (-1) e he

theorem rescale_X_pow (a : R) (m : ℕ) :
    rescale a (X ^ m : PowerSeries R) = C (a ^ m) * X ^ m := by
  rw [map_pow, rescale_X, mul_pow, map_pow]

/-- The theta series `φ(x) = ∑_{n ∈ ℤ} x^{n²}`. -/
def thetaPhi : PowerSeries R := zSeries (fun _ => 1) (fun n => n.natAbs ^ 2)

/-- `(-x;x²)_∞ = ∏_{k ≥ 0} (1 + x^{2k+1})`. -/
def oddPlus : PowerSeries R := infProd fun k => 1 + X ^ (2 * k + 1)

/-- `(x;x²)_∞ = ∏_{k ≥ 0} (1 - x^{2k+1})`. -/
def oddMinus : PowerSeries R := infProd fun k => 1 - X ^ (2 * k + 1)

/-- `(x²;x²)_∞ = ∏_{k ≥ 0} (1 - x^{2k+2})`. -/
def evenEuler : PowerSeries R := infProd fun k => 1 - X ^ (2 * k + 2)

theorem prodFactors_oddPlus : ProdFactors fun k => (1 : PowerSeries R) + X ^ (2 * k + 1) :=
  prodFactors_one_add_X_pow _ fun k => by omega

theorem prodFactors_oddMinus : ProdFactors fun k => (1 : PowerSeries R) - X ^ (2 * k + 1) :=
  prodFactors_one_sub_X_pow _ fun k => by omega

theorem prodFactors_evenEuler : ProdFactors fun k => (1 : PowerSeries R) - X ^ (2 * k + 2) :=
  prodFactors_one_sub_X_pow _ fun k => by omega

theorem prodFactors_euler : ProdFactors fun k => (1 : PowerSeries R) - X ^ (k + 1) :=
  prodFactors_one_sub_X_pow _ fun k => by omega

/-- The repository's Euler product is the infinite product of `1 - X^(k+1)`. -/
theorem euler_eq_infProd : (euler : PowerSeries R) = infProd fun k => 1 - X ^ (k + 1) := by
  ext d
  rw [euler, coeff_mk, infProd, coeff_mk, qFactorial_eq_prod]

theorem expand_two_euler :
    expand 2 two_ne_zero (euler : PowerSeries R) = evenEuler := by
  rw [euler_eq_infProd, expand_infProd 2 two_ne_zero prodFactors_euler, evenEuler]
  apply infProd_congr
  intro k
  rw [map_sub, map_one, map_pow, expand_X, ← pow_mul]
  ring_nf

theorem evenEuler_mul_expand_reciprocalEuler :
    (evenEuler : PowerSeries R) * expand 2 two_ne_zero reciprocalEuler = 1 := by
  rw [← expand_two_euler, ← map_mul, euler_mul_reciprocal, map_one]

/-- The centered finite Gauss identity
`∑_{k ≤ 2n} x^{(k-n)²} [2n,k]_{x²} = (∏_{i<n} (1 + x^{2i+1}))²`. -/
theorem gauss_finite (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1),
        X ^ (((k : ℤ) - n).natAbs ^ 2) * gaussian (X ^ 2 : PowerSeries R) (2 * n) k) =
      (∏ i ∈ Finset.range n, (1 + X ^ (2 * i + 1))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gaussian]
  have h := finite_qBinomial_homog (X ^ 2 : PowerSeries R) (X ^ (2 * n - 1)) 1 (2 * n)
  -- the product side
  have hprod : (∏ j ∈ Finset.range (2 * n), (X ^ (2 * n - 1) + 1 * (X ^ 2) ^ j :
      PowerSeries R)) = X ^ (n * (n - 1) + n * (2 * n - 1)) *
        (∏ i ∈ Finset.range n, (1 + X ^ (2 * i + 1))) ^ 2 := by
    rw [show Finset.range (2 * n) = Finset.range (n + n) by rw [two_mul],
      Finset.prod_range_add]
    have hA : (∏ j ∈ Finset.range n, (X ^ (2 * n - 1) + 1 * (X ^ 2) ^ j : PowerSeries R)) =
        X ^ (n * (n - 1)) * ∏ i ∈ Finset.range n, (1 + X ^ (2 * i + 1)) := by
      rw [← Finset.prod_range_reflect (fun i => (1 + X ^ (2 * i + 1) : PowerSeries R)) n]
      have hsum : (∑ j ∈ Finset.range n, 2 * j) = n * (n - 1) := by
        rw [← Finset.mul_sum, mul_comm, Finset.sum_range_id_mul_two]
      rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [one_mul, ← pow_mul, mul_add, mul_one, ← pow_add, add_comm]
      congr 2
      omega
    have hB : (∏ j ∈ Finset.range n, (X ^ (2 * n - 1) + 1 * (X ^ 2) ^ (n + j) :
        PowerSeries R)) = X ^ (n * (2 * n - 1)) * ∏ i ∈ Finset.range n, (1 + X ^ (2 * i + 1)) := by
      have hc : (∏ _j ∈ Finset.range n, (X ^ (2 * n - 1) : PowerSeries R)) =
          X ^ (n * (2 * n - 1)) := by
        rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm]
      rw [← hc, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      rw [one_mul, ← pow_mul, mul_add (X ^ (2 * n - 1) : PowerSeries R), mul_one, ← pow_add]
      congr 2
      omega
    rw [hA, hB]
    ring
  rw [hprod] at h
  apply X_pow_mul_cancel (n * (n - 1) + n * (2 * n - 1))
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * n := by have := Finset.mem_range.mp hk; omega
  rw [weightedGaussian_eq, one_pow, mul_one, ← pow_mul]
  have hexp : n * (n - 1) + n * (2 * n - 1) + ((k : ℤ) - n).natAbs ^ 2 =
      2 * k.choose 2 + (2 * n - 1) * (2 * n - k) := by
    have h1 := two_mul_choose_two_add k
    have h2 := Int.natAbs_sq ((k : ℤ) - n)
    zify [hk', show 1 ≤ n by omega, show 1 ≤ 2 * n by omega] at h1 h2 ⊢
    nlinarith [h1, h2]
  rw [← mul_assoc, ← pow_add, hexp, pow_add]
  ring

/-- The stable range of the Gaussian coefficients, in the form needed below. -/
theorem agreeTo_gaussian_reciprocalEuler (n k : ℕ) (hk : k ≤ n) :
    AgreeTo (min k (n - k) + 1) (gaussian (X : PowerSeries R) n k) reciprocalEuler := by
  apply AgreeTo.of_coeff
  intro d hd
  rw [coeff_gaussian_eq_reciprocalQFactorial n k d (by omega),
    coeff_reciprocalEuler d k (by omega)]

theorem expand_gaussian (n k : ℕ) :
    expand 2 two_ne_zero (gaussian (X : PowerSeries R) n k) = gaussian (X ^ 2) n k := by
  have := map_gaussian (expand 2 two_ne_zero : PowerSeries R →ₐ[R] PowerSeries R).toRingHom
    (X : PowerSeries R) n k
  simpa [expand_X] using this

/-- Gauss: `φ(x) / (x²;x²)_∞ = (-x;x²)_∞²`. -/
theorem thetaPhi_mul_reciprocal :
    (thetaPhi : PowerSeries R) * expand 2 two_ne_zero reciprocalEuler = oddPlus ^ 2 := by
  apply eq_of_agreeTo
  intro n
  set R₂ : PowerSeries R := expand 2 two_ne_zero reciprocalEuler
  -- truncate the theta series
  have hφ : AgreeTo (n + 1) (thetaPhi : PowerSeries R)
      (∑ j ∈ Finset.Icc (-(n : ℤ)) n, C (1 : R) * X ^ (j.natAbs ^ 2)) := by
    apply agreeTo_zSeries
    · intro j
      have := Nat.le_self_pow two_ne_zero j.natAbs
      omega
    · intro j hj
      have := Nat.le_self_pow two_ne_zero j.natAbs
      simp only [Finset.mem_Icc]
      omega
  have hreindex : (∑ j ∈ Finset.Icc (-(n : ℤ)) n, C (1 : R) * X ^ (j.natAbs ^ 2)) =
      ∑ k ∈ Finset.range (2 * n + 1), (X ^ (((k : ℤ) - n).natAbs ^ 2) : PowerSeries R) := by
    apply Finset.sum_nbij' (fun (j : ℤ) => (j + n).toNat) (fun (k : ℕ) => (k : ℤ) - n)
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
      rw [map_one, one_mul]
      congr 3
      omega
  -- each Gaussian term agrees with `1/(x²;x²)_∞` far enough
  have hterm : ∀ k ∈ Finset.range (2 * n + 1),
      AgreeTo (n + 1)
        (X ^ (((k : ℤ) - n).natAbs ^ 2) * gaussian (X ^ 2 : PowerSeries R) (2 * n) k)
        (X ^ (((k : ℤ) - n).natAbs ^ 2) * R₂) := by
    intro k hk
    have hk' : k ≤ 2 * n := by have := Finset.mem_range.mp hk; omega
    have h1 := (agreeTo_gaussian_reciprocalEuler (R := R) (2 * n) k hk').expand 2 two_ne_zero
    rw [expand_gaussian] at h1
    have h2 := h1.X_pow_mul (((k : ℤ) - n).natAbs ^ 2)
    apply h2.mono
    have hmin : min k (2 * n - k) + ((k : ℤ) - n).natAbs = n := by omega
    have hsq := Nat.le_self_pow two_ne_zero ((k : ℤ) - n).natAbs
    generalize ((k : ℤ) - n).natAbs ^ 2 = s at hsq ⊢
    omega
  have hsum := AgreeTo.finset_sum _ hterm
  rw [gauss_finite, ← Finset.sum_mul] at hsum
  have hprod := (agreeTo_infProd (prodFactors_oddPlus (R := R)) n).pow 2
  rw [← oddPlus] at hprod
  have h3 := hφ.mul_right R₂
  rw [hreindex] at h3
  exact (h3.trans hsum.symm).trans hprod.symm

/-- **Gauss's product** `φ(x) = (x²;x²)_∞ (-x;x²)_∞²`. -/
theorem thetaPhi_eq : (thetaPhi : PowerSeries R) = evenEuler * oddPlus ^ 2 := by
  calc (thetaPhi : PowerSeries R)
      = thetaPhi * (expand 2 two_ne_zero reciprocalEuler * evenEuler) := by
        rw [mul_comm (expand 2 two_ne_zero reciprocalEuler), evenEuler_mul_expand_reciprocalEuler,
          mul_one]
    _ = evenEuler * oddPlus ^ 2 := by
        rw [← mul_assoc, thetaPhi_mul_reciprocal, mul_comm]

theorem rescale_neg_one_evenEuler :
    rescale (-1 : R) (evenEuler : PowerSeries R) = evenEuler := by
  rw [evenEuler, rescale_infProd _ prodFactors_evenEuler]
  apply infProd_congr
  intro k
  rw [map_sub, map_one, rescale_X_pow, show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
  simp

theorem rescale_neg_one_oddPlus :
    rescale (-1 : R) (oddPlus : PowerSeries R) = oddMinus := by
  rw [oddPlus, rescale_infProd _ prodFactors_oddPlus, oddMinus]
  apply infProd_congr
  intro k
  rw [map_add, map_one, rescale_X_pow, pow_succ, pow_mul]
  simp [sub_eq_add_neg]

/-- **Gauss's product at `-x`**: `φ(-x) = (x²;x²)_∞ (x;x²)_∞²`. -/
theorem rescale_thetaPhi_eq :
    rescale (-1 : R) (thetaPhi : PowerSeries R) = evenEuler * oddMinus ^ 2 := by
  rw [thetaPhi_eq, map_mul, map_pow, rescale_neg_one_evenEuler, rescale_neg_one_oddPlus]

end Gauss

end

end VOA.QSeries.JTP
