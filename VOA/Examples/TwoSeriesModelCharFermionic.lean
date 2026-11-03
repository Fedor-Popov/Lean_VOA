/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.JetFermionicIdentity

/-!
# The Chern–Tran–Wakhare fermionic series of the boundary `sl₂` levels, at every `n`

For `n ≥ 0` let `β^{(n)}` be the Bailey chain started at the unit sequence,

  `β^{(0)}_N = δ_{N,0}`,   `β^{(n+1)}_N = Σ_{k ≤ N} q^{k² + k} β^{(n)}_k / (q)_{N-k}`,

so that `β^{(n)}_N = Σ_{N ≥ N_1 ≥ ⋯ ≥ N_{n-1} ≥ 0} q^{Σ_s (N_s² + N_s)} / Π_s (q)_{N_s - N_{s+1}}`
(`N_0 = N`): the Gordon colour-profile sum of Chern–Tran–Wakhare, a profile `(r_0, …, r_{n-1})`
having `N_s = r_s + ⋯ + r_{n-1}`.  The fermionic series is

  `fermSeries n = Σ_N q^N (Σ_{k ≤ 2N} [2N, k]_q) β^{(n)}_N`.

* `newton_sum` — the terminating identity
  `Σ_m [M, m]_q (-1)^m q^{C(M-m, 2)} (x; q)_m = q^{C(M, 2)} x^M` (over any commutative ring);
* `cTr_eq` — the Bailey transform of `β^{(n)}` is a pure power:
  `Σ_N (-1)^N q^{C(j-N,2)} (q)_{j+N} β^{(n)}_N / (q)_{j-N} = q^{n j (j+1) + C(j, 2)}`
  (induction on `n`; each step is `newton_sum`);
* `euler_cube_mul_fermSeries` — `(q;q)_∞³ · fermSeries n = (q^{2n+1}; q^{2n+1})_∞³`, by the
  proved moment identity `euler_cube_mul_pairSum`, `cTr_eq`, and Jacobi's cube identity;
* `fermSeries_eq_product` — **`fermSeries n` is the Arakawa–Dai boundary product
  `AffineSl2BoundaryCharacter.product n`, for every `n`**;
* `fermSeries_one` — at `n = 1` it is the level-one `jetSeries` (consistency check).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open VOA.QSeries VOA.LocallyFinitePowerSeriesSum VOA.JetProduct VOA.JetFermionic
open scoped BigOperators

noncomputable section

/-! ### A terminating `q`-Newton identity -/

section Newton

variable {R : Type*} [CommRing R]

theorem choose_two_succ' (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

/-- The summand `(-1)^m q^{C(M-m,2)} (x;q)_m`. -/
def nwt (q x : R) (M m : ℕ) : R := (-1) ^ m * q ^ ((M - m).choose 2) * pochhammer x q m

/-- `Σ_m [M, m]_q (-1)^m q^{C(M-m,2)} (x;q)_m = q^{C(M,2)} x^M`. -/
theorem newton_sum (q x : R) (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), gaussian q M m * nwt q x M m = q ^ (M.choose 2) * x ^ M := by
  induction M with
  | zero => simp [nwt]
  | succ M ih =>
    have hterm : ∀ k ∈ Finset.range (M + 1),
        gaussian q M k * nwt q x (M + 1) k +
            q ^ (M - k) * gaussian q M k * nwt q x (M + 1) (k + 1) =
          x * q ^ M * (gaussian q M k * nwt q x M k) := by
      intro k hk
      have hkM : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have e1 : M + 1 - k = (M - k) + 1 := by omega
      have e2 : M + 1 - (k + 1) = M - k := by omega
      have hq : q ^ (M - k) * q ^ k = q ^ M := by rw [← pow_add, Nat.sub_add_cancel hkM]
      simp only [nwt, e1, e2, choose_two_succ', pochhammer_succ, pow_add, pow_succ]
      linear_combination (gaussian q M k * (-1) ^ k * q ^ ((M - k).choose 2) *
        pochhammer x q k * x) * hq
    have hsplit : ∑ m ∈ Finset.range (M + 1 + 1), gaussian q (M + 1) m * nwt q x (M + 1) m =
        ∑ k ∈ Finset.range (M + 1), (gaussian q M k * nwt q x (M + 1) k +
          q ^ (M - k) * gaussian q M k * nwt q x (M + 1) (k + 1)) := by
      rw [Finset.sum_range_succ', Finset.sum_add_distrib]
      simp only [gaussian_succ_succ, add_mul, Finset.sum_add_distrib]
      have h2 : ∑ k ∈ Finset.range (M + 1), gaussian q M (k + 1) * nwt q x (M + 1) (k + 1) +
          gaussian q (M + 1) 0 * nwt q x (M + 1) 0 =
            ∑ k ∈ Finset.range (M + 1), gaussian q M k * nwt q x (M + 1) k := by
        rw [gaussian_zero_right, ← gaussian_zero_right q M, ← Finset.sum_range_succ'
          (fun k => gaussian q M k * nwt q x (M + 1) k), Finset.sum_range_succ,
          gaussian_eq_zero_of_lt q (Nat.lt_succ_self M), zero_mul, add_zero]
      rw [← h2]
      ring
    rw [hsplit, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih, choose_two_succ']
    ring

end Newton

/-! ### The `q`-Newton identity in reciprocal form -/

theorem rqf_zero' : (reciprocalQFactorial 0 : PowerSeries ℚ) = 1 := by
  have h := qFactorial_mul_reciprocal (R := ℚ) 0
  simpa using h

/-- `Σ_m (-1)^m q^{C(M-m,2)} (q)_{A+m} / ((q)_{M-m} (q)_m) = q^{M(A+1) + C(M,2)} (q)_A / (q)_M`. -/
theorem newton_rqf (A M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), (-1 : PowerSeries ℚ) ^ m * PowerSeries.X ^ ((M - m).choose 2) *
        qFactorial PowerSeries.X (A + m) * reciprocalQFactorial (M - m) *
          reciprocalQFactorial m =
      PowerSeries.X ^ (M * (A + 1) + M.choose 2) * qFactorial PowerSeries.X A *
        reciprocalQFactorial M := by
  have h := congrArg (fun f => f * (qFactorial PowerSeries.X A * reciprocalQFactorial M))
    (newton_sum (PowerSeries.X : PowerSeries ℚ) (PowerSeries.X ^ (A + 1)) M)
  simp only [Finset.sum_mul] at h
  have hM : qFactorial (PowerSeries.X : PowerSeries ℚ) M * reciprocalQFactorial M = 1 :=
    qFactorial_mul_reciprocal M
  rw [show PowerSeries.X ^ (M * (A + 1) + M.choose 2) * qFactorial PowerSeries.X A *
      reciprocalQFactorial M = PowerSeries.X ^ M.choose 2 * (PowerSeries.X ^ (A + 1)) ^ M *
        (qFactorial PowerSeries.X A * reciprocalQFactorial M) by ring, ← h]
  apply Finset.sum_congr rfl
  intro m hm
  have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [gaussian_eq_qFactorial_ratio M m hmM, nwt, qFactorial_add]
  linear_combination (-(-1 : PowerSeries ℚ) ^ m * PowerSeries.X ^ ((M - m).choose 2) *
    qFactorial PowerSeries.X A * pochhammer (PowerSeries.X ^ (A + 1)) PowerSeries.X m *
      reciprocalQFactorial (M - m) * reciprocalQFactorial m) * hM

/-! ### The Bailey chain -/

/-- The Bailey chain `β^{(n)}_N` started at the unit sequence. -/
def bet : ℕ → ℕ → PowerSeries ℚ
  | 0, N => if N = 0 then 1 else 0
  | n + 1, N => ∑ k ∈ Finset.range (N + 1),
      PowerSeries.X ^ (k * k + k) * reciprocalQFactorial (N - k) * bet n k

theorem bet_one (N : ℕ) : bet 1 N = reciprocalQFactorial N := by
  rw [bet, Finset.sum_eq_single 0]
  · simp [bet]
  · intro k _ hk; simp [bet, hk]
  · intro h; simp at h

/-- The Bailey-transform coefficient `(-1)^N q^{C(j-N,2)} (q)_{j+N} / (q)_{j-N}`. -/
def cCoef (j N : ℕ) : PowerSeries ℚ :=
  (-1 : PowerSeries ℚ) ^ N * PowerSeries.X ^ ((j - N).choose 2) *
    qFactorial PowerSeries.X (j + N) * reciprocalQFactorial (j - N)

/-- The Bailey transform of `β^{(n)}`. -/
def cTr (n j : ℕ) : PowerSeries ℚ := ∑ N ∈ Finset.range (j + 1), cCoef j N * bet n N

theorem sum_range_ite_le (k M : ℕ) (f : ℕ → PowerSeries ℚ) :
    ∑ N ∈ Finset.range (k + M + 1), (if k ≤ N then f N else 0) =
      ∑ m ∈ Finset.range (M + 1), f (k + m) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hf : Finset.filter (fun N => k ≤ N) (Finset.range (k + M + 1)) =
      Finset.Ico k (k + M + 1) := by
    ext N; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hf, Finset.sum_Ico_eq_sum_range, show k + M + 1 - k = M + 1 by omega]

/-- The one-step Bailey identity: for `k ≤ j`,
`Σ_{k ≤ N ≤ j} cCoef j N / (q)_{N-k} = (-1)^k q^{(j-k)(j+k+1) + C(j-k,2)} (q)_{j+k} / (q)_{j-k}`. -/
theorem bailey_step (k M : ℕ) :
    ∑ N ∈ Finset.range (k + M + 1),
        (if k ≤ N then cCoef (k + M) N * reciprocalQFactorial (N - k) else 0) =
      (-1 : PowerSeries ℚ) ^ k * PowerSeries.X ^ (M * (2 * k + M + 1) + M.choose 2) *
        qFactorial PowerSeries.X (2 * k + M) * reciprocalQFactorial M := by
  rw [sum_range_ite_le]
  have h := newton_rqf (2 * k + M) M
  rw [show (-1 : PowerSeries ℚ) ^ k * PowerSeries.X ^ (M * (2 * k + M + 1) + M.choose 2) *
      qFactorial PowerSeries.X (2 * k + M) * reciprocalQFactorial M =
    (-1 : PowerSeries ℚ) ^ k * (PowerSeries.X ^ (M * (2 * k + M + 1) + M.choose 2) *
      qFactorial PowerSeries.X (2 * k + M) * reciprocalQFactorial M) by ring, ← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  simp only [cCoef, show k + M - (k + m) = M - m by omega, show k + m - k = m by omega,
    show k + M + (k + m) = 2 * k + M + m by omega, pow_add]
  ring

/-- **The Bailey transform of `β^{(n)}` is a pure power.** -/
theorem cTr_eq (n j : ℕ) :
    cTr n j = PowerSeries.X ^ (n * (j * (j + 1)) + j.choose 2) := by
  induction n generalizing j with
  | zero =>
    rw [cTr, Finset.sum_eq_single 0]
    · simp only [bet, cCoef, pow_zero, one_mul, Nat.sub_zero, add_zero, zero_mul, zero_add]
      rw [if_pos trivial, mul_one, mul_assoc, qFactorial_mul_reciprocal, mul_one]
    · intro N _ hN; simp [bet, hN]
    · intro h; simp at h
  | succ n ih =>
    -- expand, extend the inner range, and swap
    have hexp : cTr (n + 1) j = ∑ k ∈ Finset.range (j + 1),
        PowerSeries.X ^ (k * k + k) * bet n k * ∑ N ∈ Finset.range (j + 1),
          (if k ≤ N then cCoef j N * reciprocalQFactorial (N - k) else 0) := by
      rw [cTr]
      have hin : ∀ N ∈ Finset.range (j + 1), cCoef j N * bet (n + 1) N =
          ∑ k ∈ Finset.range (j + 1), (if k ≤ N then cCoef j N *
            (PowerSeries.X ^ (k * k + k) * reciprocalQFactorial (N - k) * bet n k) else 0) := by
        intro N hN
        have hNj : N ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hN)
        rw [bet, Finset.mul_sum]
        symm
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
        · intro _ _; rfl
      rw [Finset.sum_congr rfl hin, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      split_ifs <;> ring
    have hR : (PowerSeries.X : PowerSeries ℚ) ^ ((n + 1) * (j * (j + 1)) + j.choose 2) =
        PowerSeries.X ^ (j * (j + 1)) * cTr n j := by
      rw [ih, ← pow_add]; congr 1; ring
    rw [hR, hexp, cTr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    obtain ⟨M, rfl⟩ : ∃ M, j = k + M := ⟨j - k, by omega⟩
    rw [bailey_step, cCoef, show k + M - k = M by omega, show k + M + k = 2 * k + M by omega]
    have hpow : PowerSeries.X ^ (k * k + k) * PowerSeries.X ^ (M * (2 * k + M + 1) + M.choose 2) =
        (PowerSeries.X : PowerSeries ℚ) ^ ((k + M) * (k + M + 1)) * PowerSeries.X ^ M.choose 2 := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    linear_combination ((-1 : PowerSeries ℚ) ^ k * qFactorial PowerSeries.X (2 * k + M) *
      reciprocalQFactorial M * bet n k) * hpow

/-! ### The fermionic series -/

/-- The `N`-th term `q^N (Σ_{k ≤ 2N} [2N, k]_q) β^{(n)}_N`. -/
def fermTerm (n N : ℕ) : PowerSeries ℚ :=
  PowerSeries.X ^ N * (∑ k ∈ Finset.range (2 * N + 1), gaussian PowerSeries.X (2 * N) k) *
    bet n N

/-- The Chern–Tran–Wakhare fermionic series `Σ_N q^N H_{2N}(q) β^{(n)}_N` (at `t = q`,
`z = 1`). -/
def fermSeries (n : ℕ) : PowerSeries ℚ := VOA.LocallyFinitePowerSeriesSum.sum (fermTerm n)

theorem coeff_fermTerm_eq_zero (n d N : ℕ) (h : d < N) :
    PowerSeries.coeff d (fermTerm n N) = 0 := by
  rw [fermTerm, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem fermTerm_one (N : ℕ) : fermTerm 1 N = jetTerm N := by
  rw [fermTerm, jetTerm, bet_one]

/-- At `n = 1` the fermionic series is the level-one `jetSeries`. -/
theorem fermSeries_one : fermSeries 1 = jetSeries := by
  rw [fermSeries, jetSeries]
  congr 1
  funext N
  exact fermTerm_one N

/-- The double-sum summand `(-1)^t (2N+2t+1) q^{N + C(t+1,2)} (q)_{2N+t} β^{(n)}_N / (q)_t`. -/
def fermDouble (n N t : ℕ) : PowerSeries ℚ :=
  (-1 : PowerSeries ℚ) ^ t * ((2 * N + 2 * t + 1 : ℕ) : PowerSeries ℚ) *
    PowerSeries.X ^ (N + (t + 1).choose 2) * qFactorial PowerSeries.X (2 * N + t) *
      reciprocalQFactorial t * bet n N

theorem coeff_fermDouble_eq_zero (n N t d : ℕ) (h : d < N + t) :
    PowerSeries.coeff d (fermDouble n N t) = 0 := by
  have heq : fermDouble n N t = PowerSeries.X ^ (N + (t + 1).choose 2) *
      ((-1 : PowerSeries ℚ) ^ t * ((2 * N + 2 * t + 1 : ℕ) : PowerSeries ℚ) *
        qFactorial PowerSeries.X (2 * N + t) * reciprocalQFactorial t * bet n N) := by
    unfold fermDouble
    ring
  rw [heq]
  exact coeff_X_pow_mul_eq_zero _ _ (by have := le_triangular t; omega) _

/-- The Euler cube times one term is a locally finite alternating sum. -/
theorem euler_cube_mul_fermTerm (n N : ℕ) :
    (euler : PowerSeries ℚ) ^ 3 * fermTerm n N =
      VOA.LocallyFinitePowerSeriesSum.sum (fermDouble n N) := by
  have hm := euler_cube_mul_pairSum (K := ℚ) (2 * N)
  calc
    _ = ((euler : PowerSeries ℚ) ^ 3 * pairSum (2 * N)) *
        (PowerSeries.X ^ N * qFactorial PowerSeries.X (2 * N) * bet n N) := by
      rw [fermTerm, sum_gaussian_eq_pairSum]
      ring
    _ = momentSeries (2 * N) *
        (PowerSeries.X ^ N * qFactorial PowerSeries.X (2 * N) * bet n N) := by
      rw [hm]
    _ = VOA.LocallyFinitePowerSeriesSum.sum (fun t => momentTerm (2 * N) t *
        (PowerSeries.X ^ N * qFactorial PowerSeries.X (2 * N) * bet n N)) :=
      (indexBounded_sum_mul _ (coeff_momentTerm_eq_zero (2 * N)) _).symm
    _ = _ := by
      apply VOA.LocallyFinitePowerSeriesSum.sum_congr
      intro t
      rw [momentTerm, fermDouble, gaussian_eq_qFactorial_ratio (2 * N + t) t (by omega),
        show 2 * N + t - t = 2 * N by omega, pow_add]
      have h1 : qFactorial (PowerSeries.X : PowerSeries ℚ) (2 * N) *
          reciprocalQFactorial (2 * N) = 1 := qFactorial_mul_reciprocal _
      linear_combination
        ((-1 : PowerSeries ℚ) ^ t * ((2 * N + 2 * t + 1 : ℕ) : PowerSeries ℚ) *
          PowerSeries.X ^ ((t + 1).choose 2) * qFactorial PowerSeries.X (2 * N + t) *
            reciprocalQFactorial t * PowerSeries.X ^ N * bet n N) * h1

/-- The Bailey collapse of each antidiagonal. -/
theorem fermDouble_antidiagonal (n j : ℕ) :
    ∑ N ∈ Finset.range (j + 1), fermDouble n N (j - N) =
      alternatingTerm j * PowerSeries.X ^ (n * (j * (j + 1))) := by
  have hc := cTr_eq n j
  have hA : alternatingTerm j * PowerSeries.X ^ (n * (j * (j + 1))) =
      (-1 : PowerSeries ℚ) ^ j * ((2 * j + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.X ^ j *
        PowerSeries.X ^ (n * (j * (j + 1)) + j.choose 2) := by
    unfold alternatingTerm
    rw [choose_two_succ', pow_add, pow_add]
    ring
  rw [hA, ← hc, cTr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  have hNj : N ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hN)
  obtain ⟨t, rfl⟩ : ∃ t, j = N + t := ⟨j - N, by omega⟩
  rw [fermDouble, cCoef, show N + t - N = t by omega, show 2 * N + t = N + t + N by omega,
    show 2 * N + 2 * t + 1 = 2 * (N + t) + 1 by omega, choose_two_succ' t]
  have hsign : (-1 : PowerSeries ℚ) ^ t = (-1) ^ (N + t) * (-1) ^ N := by
    rw [← pow_add, show N + t + N = t + 2 * N by omega, pow_add, pow_mul]
    simp
  rw [hsign]
  ring

/-- `(q;q)_∞³ · fermSeries n = (q^{2n+1}; q^{2n+1})_∞³`, proved outright. -/
theorem euler_cube_mul_fermSeries (n : ℕ) :
    (euler : PowerSeries ℚ) ^ 3 * fermSeries n =
      (PowerSeries.expand (2 * n + 1) (by omega) (euler : PowerSeries ℚ)) ^ 3 := by
  have hR : (PowerSeries.expand (2 * n + 1) (by omega) (euler : PowerSeries ℚ)) ^ 3 =
      VOA.LocallyFinitePowerSeriesSum.sum
        (fun r => (alternatingTerm r : PowerSeries ℚ) * PowerSeries.X ^ (n * (r * (r + 1)))) := by
    rw [← map_pow, ← jacobi_cube, sum_alternatingTerm_chain_power n]
  rw [hR, fermSeries, mul_comm, ← indexBounded_sum_mul _ (coeff_fermTerm_eq_zero n)]
  apply PowerSeries.ext
  intro d
  have hE : ∀ d N, d < N →
      PowerSeries.coeff d (fermTerm n N * (euler : PowerSeries ℚ) ^ 3) = 0 := by
    intro d N h
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [coeff_fermTerm_eq_zero n ij.1 N (by have := Finset.mem_antidiagonal.mp hij; omega),
      zero_mul]
  rw [coeff_indexBounded_sum _ hE d d le_rfl,
    coeff_indexBounded_sum _ (fun d r h => coeff_alternatingTerm_mul_eq_zero d r h _) d d le_rfl,
    map_sum, map_sum]
  simp only [← fermDouble_antidiagonal, map_sum]
  rw [sum_triangle_shift (fun N j => PowerSeries.coeff d (fermDouble n N (j - N))) d]
  apply Finset.sum_congr rfl
  intro N hN
  have hNd : N ≤ d := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hN
  rw [mul_comm, euler_cube_mul_fermTerm,
    coeff_indexBounded_sum _ (fun d t h => coeff_fermDouble_eq_zero n N t d (by omega)) d d le_rfl,
    map_sum]
  simp only [Nat.add_sub_cancel_left]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro t _ ht
  exact coeff_fermDouble_eq_zero n N t d (by simp at ht; omega)

/-- **The fermionic series is the Arakawa–Dai boundary product, for every `n`.** -/
theorem fermSeries_eq_product (n : ℕ) :
    fermSeries n = AffineSl2BoundaryCharacter.product n := by
  unfold AffineSl2BoundaryCharacter.product
  have h := congrArg (fun f => f * (reciprocalEuler : PowerSeries ℚ) ^ 3)
    (euler_cube_mul_fermSeries n)
  simp only at h
  have hinv : (euler : PowerSeries ℚ) ^ 3 * reciprocalEuler ^ 3 = 1 := by
    rw [← mul_pow, euler_mul_reciprocal, one_pow]
  calc
    fermSeries n = ((euler : PowerSeries ℚ) ^ 3 * reciprocalEuler ^ 3) * fermSeries n := by
      rw [hinv, one_mul]
    _ = _ := by
      rw [show ((euler : PowerSeries ℚ) ^ 3 * reciprocalEuler ^ 3) * fermSeries n =
        (euler ^ 3 * fermSeries n) * reciprocalEuler ^ 3 by ring, h]
      rfl

end

end VOA.TwoSeries.ModelChar
