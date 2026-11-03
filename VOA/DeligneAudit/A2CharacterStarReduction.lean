/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CharacterStarChain
import VOA.Commutative.QBinomialFiniteSum

/-!
# Proof of `StarReduction`

`(q)_∞ F = ∑_v q^v U_{2v}`.  Ingredients:

* `qbinom_eq_gaussian`: the Gaussian binomials of `GaussianTransform` and of `QBinomial` agree;
* `gaussian_vandermonde`: q-Vandermonde, `[a+b, j] = ∑_{k ≤ j} q^{(a-k)(j-k)} [a,k][b,j-k]`;
* truncation modulo `X^{N+1}` (`trunc`), in which every positive-order sum is a finite box sum;
* Euler's sum `∑_u q^{u(v+1)}/(q)_u = (q)_v/(q)_∞` (`QSeries.eulerSum_eq`).
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.QSeries VOA.DeligneGaussian

noncomputable section

local notation "q" => (PowerSeries.X : PowerSeries ℤ)

/-! ## Gaussian binomials -/

theorem qbinom_eq_gaussian {R : Type*} [CommRing R] (x : R) :
    ∀ n k, qbinom x n k = gaussian x n k
  | n, 0 => by simp
  | 0, k + 1 => rfl
  | n + 1, k + 1 => by
      rw [qbinom_succ_succ, gaussian_succ_succ, qbinom_eq_gaussian x n k,
        qbinom_eq_gaussian x n (k + 1)]
      ring

theorem gaussian_zero_left {R : Type*} [CommRing R] (x : R) (m : ℕ) :
    gaussian x 0 m = if m = 0 then 1 else 0 := by
  cases m <;> rfl

/-- **q-Vandermonde.** -/
theorem gaussian_vandermonde {R : Type*} [CommRing R] (x : R) (a : ℕ) :
    ∀ b j, gaussian x (a + b) j =
      ∑ k ∈ Finset.range (j + 1), x ^ ((a - k) * (j - k)) * gaussian x a k * gaussian x b (j - k)
  | 0, j => by
      rw [Finset.sum_range_succ, Finset.sum_eq_zero]
      · simp
      · intro k hk
        rw [Finset.mem_range] at hk
        rw [gaussian_zero_left, if_neg (by omega), mul_zero]
  | b + 1, 0 => by simp
  | b + 1, j + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega, gaussian_succ_succ,
        gaussian_vandermonde x a b (j + 1), gaussian_vandermonde x a b j,
        Finset.sum_range_succ (fun k => x ^ ((a - k) * (j + 1 - k)) * gaussian x a k *
          gaussian x (b + 1) (j + 1 - k)),
        Finset.sum_range_succ (fun k => x ^ ((a - k) * (j + 1 - k)) * gaussian x a k *
          gaussian x b (j + 1 - k))]
      simp only [Nat.sub_self, mul_zero, pow_zero, one_mul, gaussian_zero_right, mul_one]
      have hsplit : ∀ k ∈ Finset.range (j + 1),
          x ^ ((a - k) * (j + 1 - k)) * gaussian x a k * gaussian x (b + 1) (j + 1 - k) =
            x ^ ((a - k) * (j + 1 - k)) * gaussian x a k * gaussian x b (j + 1 - k) +
              x ^ (a + b - j) * (x ^ ((a - k) * (j - k)) * gaussian x a k *
                gaussian x b (j - k)) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [show j + 1 - k = (j - k) + 1 by omega, gaussian_succ_succ]
        by_cases hka : k ≤ a
        · by_cases hjb : j - k ≤ b
          · have he : (a - k) * (j - k + 1) + (b - (j - k)) = a + b - j + (a - k) * (j - k) := by
              rw [mul_add, mul_one]; omega
            calc _ = x ^ ((a - k) * (j - k + 1)) * gaussian x a k * gaussian x b (j - k + 1) +
                  x ^ ((a - k) * (j - k + 1) + (b - (j - k))) * gaussian x a k *
                    gaussian x b (j - k) := by rw [pow_add]; ring
              _ = _ := by rw [he, pow_add]; ring
          · rw [gaussian_eq_zero_of_lt x (show b < j - k by omega),
              gaussian_eq_zero_of_lt x (show b < j - k + 1 by omega)]
            ring
        · rw [gaussian_eq_zero_of_lt x (show a < k by omega)]
          ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-! ## Truncation modulo `X^{N+1}` -/

/-- Reduction modulo `X^{N+1}`. -/
abbrev trunc (N : ℕ) : PowerSeries ℤ →+* PowerSeries ℤ ⧸ Ideal.span {q ^ (N + 1)} :=
  Ideal.Quotient.mk _

theorem trunc_eq_iff (N : ℕ) (φ ψ : PowerSeries ℤ) :
    trunc N φ = trunc N ψ ↔ ∀ d ≤ N, coeff d φ = coeff d ψ := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, X_pow_dvd_iff]
  constructor
  · intro h d hd
    have := h d (by omega)
    rwa [map_sub, sub_eq_zero] at this
  · intro h d hd
    rw [map_sub, sub_eq_zero]
    exact h d (by omega)

theorem eq_of_trunc (φ ψ : PowerSeries ℤ) (h : ∀ N, trunc N φ = trunc N ψ) : φ = ψ := by
  ext d
  exact (trunc_eq_iff d φ ψ).mp (h d) d le_rfl

theorem trunc_X_pow_mul (N m : ℕ) (hm : N < m) (φ : PowerSeries ℤ) :
    trunc N (q ^ m * φ) = 0 := by
  rw [← map_zero (trunc N), trunc_eq_iff]
  intro d hd
  rw [coeff_X_pow_mul', if_neg (by omega), map_zero]

/-- Box versus simplex, modulo `X^{N+1}`. -/
theorem trunc_diag (N : ℕ) (f : ℕ → ℕ → PowerSeries ℤ)
    (hf : ∀ a b, N < a + b → trunc N (f a b) = 0) :
    trunc N (∑ n ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1), f i (n - i)) =
      trunc N (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), f a b) := by
  rw [Finset.sum_range_diag_flip, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [map_sum, map_sum]
  refine Finset.sum_subset (fun b hb => by simp only [Finset.mem_range] at hb ⊢; omega) ?_
  intro b hb hnb
  simp only [Finset.mem_range] at hb hnb
  exact hf a b (by omega)

/-- Positive-order sums are finite box sums modulo `X^{N+1}`. -/
theorem trunc_powerShiftSum (N A : ℕ) (hA : 0 < A) (B : ℕ → PowerSeries ℤ) :
    trunc N (powerShiftSum A B) =
      trunc N (∑ j ∈ Finset.range (N + 1), q ^ (A * j) * B j) := by
  rw [trunc_eq_iff]
  intro d hd
  exact coeff_powerShiftSum A hA B d N hd

/-! ## Reciprocal factorials -/

local notation "cc" => (reciprocalQFactorial : ℕ → PowerSeries ℤ)

theorem gauss_mul_c (n k : ℕ) (hk : k ≤ n) :
    gaussian q n k * cc n = cc k * cc (n - k) := by
  rw [gaussian_eq_qFactorial_ratio n k hk]
  calc _ = (qFactorial q n * cc n) * cc k * cc (n - k) := by ring
    _ = _ := by rw [qFactorial_mul_reciprocal, one_mul]

theorem poch_eq_qFactorial (n : ℕ) : poch n = qFactorial q n := by
  rw [poch, qFactorial_eq_prod]

theorem partSeries_eq (n : ℕ) : partSeries n = cc n := by
  have h1 := partSeries_mul_poch n
  have h2 : qFactorial q n * cc n = 1 := qFactorial_mul_reciprocal n
  rw [poch_eq_qFactorial] at h1
  calc partSeries n = partSeries n * (qFactorial q n * cc n) := by rw [h2, mul_one]
    _ = (partSeries n * qFactorial q n) * cc n := by ring
    _ = cc n := by rw [h1, one_mul]

/-- `G_s / (q)_s = ∑_{r ≤ s} 1/((q)_r (q)_{s-r})`. -/
theorem rogersSzego_mul_c (s : ℕ) :
    rogersSzego s * cc s = ∑ r ∈ Finset.range (s + 1), cc r * cc (s - r) := by
  rw [rogersSzego, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [qbinom_eq_gaussian, gauss_mul_c s r (by simp only [Finset.mem_range] at hr; omega)]

/-! ## `F` modulo `X^{N+1}` -/

theorem trunc_starF (N : ℕ) :
    trunc N starF = trunc N (∑ n ∈ Finset.range (N + 1), q ^ n * (demazurePoly n * cc n)) := by
  rw [trunc_eq_iff]
  intro d hd
  rw [starF, coeff_mk, ← coeff_starLHS d, starLHS, map_sum, map_sum]
  simp only [partSeries_eq]
  refine Finset.sum_subset (fun n hn => by simp only [Finset.mem_range] at hn ⊢; omega) ?_
  intro n hn hnd
  simp only [Finset.mem_range] at hn hnd
  rw [coeff_X_pow_mul', if_neg (by omega)]

/-! ## Step 1: the Demazure sum over two splittings -/

/-- `f a b = q^{a+b}/((q)_a (q)_b) ∑_j [a+b,j] G_{b+j}`. -/
def stepF (a b : ℕ) : PowerSeries ℤ :=
  q ^ (a + b) * (cc a * cc b *
    ∑ j ∈ Finset.range (a + b + 1), gaussian q (a + b) j * rogersSzego (b + j))

theorem step1 (n : ℕ) :
    q ^ n * (demazurePoly n * cc n) = ∑ i ∈ Finset.range (n + 1), stepF i (n - i) := by
  simp only [demazurePoly, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := by simp only [Finset.mem_range] at hi; omega
  rw [stepF, show i + (n - i) = n by omega, ← gauss_mul_c n i hin, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qbinom_eq_gaussian, qbinom_eq_gaussian]
  ring

/-! ## Step 2: Vandermonde inside `stepF` -/

/-- The four-index summand `q^{k+u+v+w+uv} G_{k+2v+w}/((q)_k(q)_u(q)_v(q)_w)`. -/
def phi (k u v w : ℕ) : PowerSeries ℤ :=
  q ^ (k + u) * (q ^ (v + w) * (q ^ (u * v) * (cc k * cc u * cc v * cc w) *
    rogersSzego (k + 2 * v + w)))

theorem step2 (a b : ℕ) :
    stepF a b = ∑ k ∈ Finset.range (a + 1), ∑ v ∈ Finset.range (b + 1),
      phi k (a - k) v (b - v) := by
  -- expand with Vandermonde and flip the diagonal
  set H : ℕ → ℕ → PowerSeries ℤ := fun k v =>
    q ^ ((a - k) * v) * gaussian q a k * gaussian q b v * rogersSzego (b + k + v) with hH
  have hV : (∑ j ∈ Finset.range (a + b + 1), gaussian q (a + b) j * rogersSzego (b + j)) =
      ∑ k ∈ Finset.range (a + 1), ∑ v ∈ Finset.range (b + 1), H k v := by
    have h1 : (∑ j ∈ Finset.range (a + b + 1), gaussian q (a + b) j * rogersSzego (b + j)) =
        ∑ j ∈ Finset.range (a + b + 1), ∑ k ∈ Finset.range (j + 1), H k (j - k) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [gaussian_vandermonde, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      rw [hH]
      dsimp only
      rw [show b + k + (j - k) = b + j by omega]
    rw [h1, Finset.sum_range_diag_flip (a + b + 1) H]
    symm
    calc (∑ k ∈ Finset.range (a + 1), ∑ v ∈ Finset.range (b + 1), H k v)
        = ∑ k ∈ Finset.range (a + 1), ∑ v ∈ Finset.range (a + b + 1 - k), H k v := by
          refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.mem_range] at hk
          refine Finset.sum_subset (fun v hv => by simp only [Finset.mem_range] at hv ⊢; omega) ?_
          intro v _ hv
          simp only [Finset.mem_range] at hv
          rw [hH]; dsimp only
          rw [gaussian_eq_zero_of_lt q (show b < v by omega)]; ring
      _ = _ := by
          refine Finset.sum_subset (fun k hk => by simp only [Finset.mem_range] at hk ⊢; omega) ?_
          intro k _ hk
          simp only [Finset.mem_range] at hk
          refine Finset.sum_eq_zero fun v _ => ?_
          rw [hH]; dsimp only
          rw [gaussian_eq_zero_of_lt q (show a < k by omega)]; ring
  rw [stepF, hV, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp only [Finset.mem_range] at hv
  have hk' := gauss_mul_c a k (by omega)
  have hv' := gauss_mul_c b v (by omega)
  rw [phi, show k + 2 * v + (b - v) = b + k + v by omega, hH]
  dsimp only
  calc _ = q ^ (a + b) * (q ^ ((a - k) * v) * (gaussian q a k * cc a) *
        (gaussian q b v * cc b) * rogersSzego (b + k + v)) := by ring
    _ = _ := by
      rw [hk', hv', show q ^ (a + b) = q ^ (k + (a - k)) * q ^ (v + (b - v)) by
        rw [← pow_add]; congr 1; omega]
      ring

/-! ## Step 3: four free indices -/

/-- The four-index box sum. -/
def boxS2 (N : ℕ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (N + 1), ∑ u ∈ Finset.range (N + 1),
    ∑ v ∈ Finset.range (N + 1), ∑ w ∈ Finset.range (N + 1), phi k u v w

theorem trunc_phi_left (N k u v w : ℕ) (h : N < k + u) : trunc N (phi k u v w) = 0 :=
  trunc_X_pow_mul N _ h _

theorem trunc_phi_right (N k u v w : ℕ) (h : N < v + w) : trunc N (phi k u v w) = 0 := by
  rw [show phi k u v w = q ^ (v + w) * (q ^ (k + u) * (q ^ (u * v) *
    (cc k * cc u * cc v * cc w) * rogersSzego (k + 2 * v + w))) by rw [phi]; ring]
  exact trunc_X_pow_mul N _ h _

theorem trunc_starF_eq_box (N : ℕ) : trunc N starF = trunc N (boxS2 N) := by
  rw [trunc_starF]
  simp only [step1]
  rw [trunc_diag N stepF (fun a b h => by rw [stepF]; exact trunc_X_pow_mul N _ h _)]
  simp only [step2]
  -- move `k` outside `b`
  have hcomm : (∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1),
      ∑ k ∈ Finset.range (a + 1), ∑ v ∈ Finset.range (b + 1), phi k (a - k) v (b - v)) =
      ∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (a + 1),
        (fun k u => ∑ b ∈ Finset.range (N + 1), ∑ v ∈ Finset.range (b + 1),
          phi k u v (b - v)) k (a - k) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [hcomm]
  -- the outer diagonal, then the inner diagonal
  have houter := trunc_diag N (fun k u => ∑ b ∈ Finset.range (N + 1),
      ∑ v ∈ Finset.range (b + 1), phi k u v (b - v)) (fun k u h => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => by
      rw [map_sum]; exact Finset.sum_eq_zero fun v _ => trunc_phi_left N k u v _ h)
  have houter' : trunc N (∑ a ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (a + 1),
      (fun k u => ∑ b ∈ Finset.range (N + 1), ∑ v ∈ Finset.range (b + 1),
        phi k u v (b - v)) k (a - k)) = _ := houter
  rw [houter', boxS2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact trunc_diag N (fun v w => phi k u v w) (fun v w h => trunc_phi_right N k u v w h)

/-! ## Step 4: Euler's sum removes `u` -/

theorem trunc_euler_sum (N v : ℕ) :
    trunc N ((euler : PowerSeries ℤ) *
      ∑ u ∈ Finset.range (N + 1), q ^ ((v + 1) * u) * cc u) = trunc N (qFactorial q v) := by
  have h1 : trunc N (∑ u ∈ Finset.range (N + 1), q ^ ((v + 1) * u) * cc u) =
      trunc N (qFactorial q v * reciprocalEuler) := by
    rw [← trunc_powerShiftSum N (v + 1) (Nat.succ_pos v), ← eulerSum, eulerSum_eq (v + 1)
      (Nat.succ_pos v), Nat.add_sub_cancel]
  rw [map_mul, h1, ← map_mul]
  congr 1
  calc (euler : PowerSeries ℤ) * (qFactorial q v * reciprocalEuler)
      = qFactorial q v * (euler * reciprocalEuler) := by ring
    _ = qFactorial q v := by rw [euler_mul_reciprocal, mul_one]

/-- The three-index sum left after removing `u`. -/
def boxS3 (N : ℕ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (N + 1), ∑ v ∈ Finset.range (N + 1), ∑ w ∈ Finset.range (N + 1),
    q ^ (k + v + w) * (cc k * cc w * rogersSzego (k + 2 * v + w))

theorem trunc_euler_box (N : ℕ) :
    trunc N ((euler : PowerSeries ℤ) * boxS2 N) = trunc N (boxS3 N) := by
  have hS2 : boxS2 N = ∑ k ∈ Finset.range (N + 1), ∑ v ∈ Finset.range (N + 1),
      ∑ w ∈ Finset.range (N + 1),
        (q ^ (k + v + w) * (cc k * cc v * cc w * rogersSzego (k + 2 * v + w))) *
          ∑ u ∈ Finset.range (N + 1), q ^ ((v + 1) * u) * cc u := by
    rw [boxS2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [phi]; ring
  rw [hS2, Finset.mul_sum, map_sum, boxS3, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_left_comm, map_mul, trunc_euler_sum, ← map_mul]
  congr 1
  calc q ^ (k + v + w) * (cc k * cc v * cc w * rogersSzego (k + 2 * v + w)) * qFactorial q v
      = q ^ (k + v + w) * (cc k * cc w * rogersSzego (k + 2 * v + w)) *
          (qFactorial q v * cc v) := by ring
    _ = _ := by rw [qFactorial_mul_reciprocal, mul_one]

/-! ## Step 5: the right side -/

theorem trunc_shiftedU (N m : ℕ) :
    trunc N (shiftedU m) = trunc N (∑ k ∈ Finset.range (N + 1), ∑ w ∈ Finset.range (N + 1),
      q ^ (k + w) * (cc k * cc w * rogersSzego (k + w + m))) := by
  rw [shiftedU, trunc_powerShiftSum N 1 one_pos]
  have h : (∑ s ∈ Finset.range (N + 1), q ^ (1 * s) *
      (rogersSzego s * rogersSzego (s + m) * cc s)) =
      ∑ s ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (s + 1),
        (fun k w => q ^ (k + w) * (cc k * cc w * rogersSzego (k + w + m))) r (s - r) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show rogersSzego s * rogersSzego (s + m) * cc s =
      (rogersSzego s * cc s) * rogersSzego (s + m) by ring, rogersSzego_mul_c, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    simp only [Finset.mem_range] at hr
    dsimp only
    rw [show r + (s - r) = s by omega, one_mul]
  rw [h]
  exact trunc_diag N (fun k w => q ^ (k + w) * (cc k * cc w * rogersSzego (k + w + m)))
    (fun k w hkw => trunc_X_pow_mul N (k + w) hkw _)

/-- **`StarReduction` holds.** -/
theorem starReduction : StarReduction := by
  refine ⟨eq_of_trunc _ _ fun N => ?_⟩
  rw [map_mul, trunc_starF_eq_box, ← map_mul, trunc_euler_box,
    trunc_powerShiftSum N 1 one_pos, boxS3]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, trunc_shiftedU, ← map_mul, Finset.mul_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rw [show k + w + 2 * v = k + 2 * v + w by omega, show k + v + w = 1 * v + (k + w) by omega,
    pow_add]
  ring

/-- `StarIdentity` rests only on `ShiftedMehler` and `FourTriangular`. -/
theorem starIdentity_of_mehler_triangular (hM : ShiftedMehler) (hT : FourTriangular) :
    StarIdentity :=
  starIdentity_of_chain starReduction hM hT

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.gaussian_vandermonde
#print axioms VOA.DeligneAudit.A2.trunc_diag
#print axioms VOA.DeligneAudit.A2.starReduction
#print axioms VOA.DeligneAudit.A2.starIdentity_of_mehler_triangular
end AxiomAudit
