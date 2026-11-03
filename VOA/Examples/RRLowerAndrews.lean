/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.RRLowerQBinomial

/-!
# Andrews' polynomial identity for the second Rogers–Ramanujan identity

For every `n ≥ 0`, as an identity of polynomials in `q` (Schur 1917, Andrews 1970):

`E_n := Σ_{j ≥ 0} q^{j(j+1)} [n-j, j]_q`  equals
`R_n := Σ_{k ∈ ℤ} (-1)^k q^{k(5k+3)/2} [n+1, ⌊(n-5k)/2⌋]_q`.

Everything is stated **coefficientwise** (`Ecoef n N`, `Rcoef n N` are the coefficients of `q^N`),
with the coefficient function `qc` of `RRLowerQBinomial`.

* `Ecoef_rec` — `E_{n+2} = E_{n+1} + q^{n+2} E_n` (second `q`-Pascal rule, termwise);
* `Rcoef_rec` — the same recurrence for the alternating side.  The proof: after the two
  `q`-Pascal rules, the defect of the `k`-th term is `F k - F (k-1)` for an explicit `F`
  supported on one parity class of `k` (`odd_step`, `even_step`, `defect_eq`), so the sum over
  `k` telescopes (`sum_Ico_telescope`);
* `Ecoef_eq_Rcoef` — **the polynomial identity**, by two-step induction from `E_0 = R_0 = 1`,
  `E_1 = R_1 = 1`.

All proved, no hypotheses.
-/

namespace VOA.RRLower

open Finset

noncomputable section

/-! ## §1  Exponents, signs, telescoping -/

/-- The exponent `k(5k+3)/2`. -/
def ee (k : ℤ) : ℤ := k * (5 * k + 3) / 2

theorem two_mul_ee (k : ℤ) : 2 * ee k = k * (5 * k + 3) := by
  unfold ee
  have hev : Even (k * (5 * k + 3)) := by
    have h1 : k * (5 * k + 3) = k * (k + 1) + 2 * (2 * k * k + k) := by ring
    rw [h1]
    exact (Int.even_mul_succ_self k).add (even_two_mul _)
  exact Int.mul_ediv_cancel' hev.two_dvd

theorem ee_sub_one (k : ℤ) : ee k = ee (k - 1) + (5 * k - 1) := by
  have h1 := two_mul_ee k
  have h2 := two_mul_ee (k - 1)
  have : 2 * ee k = 2 * (ee (k - 1) + (5 * k - 1)) := by rw [mul_add, h2, h1]; ring
  omega

theorem ee_nonneg (k : ℤ) : 0 ≤ ee k := by
  have h := two_mul_ee k
  have : 0 ≤ k * (5 * k + 3) := by
    rcases le_or_gt 0 k with hk | hk
    · positivity
    · nlinarith
  omega

/-- `ee k ≥ |k|`: in particular `ee k > N` once `|k| > N`. -/
theorem abs_le_ee (k : ℤ) : |k| ≤ ee k := by
  have h := two_mul_ee k
  rcases le_or_gt 0 k with hk | hk
  · rw [abs_of_nonneg hk]; nlinarith
  · rw [abs_of_neg hk]; nlinarith

/-- The sign `(-1)^k`. -/
def sgn (k : ℤ) : ℤ := if k % 2 = 0 then 1 else -1

theorem sgn_sub_one (k : ℤ) : sgn (k - 1) = - sgn k := by
  unfold sgn
  split_ifs <;> omega

theorem sum_Ico_telescope (f : ℤ → ℤ) (a : ℤ) : ∀ n : ℕ,
    ∑ k ∈ Finset.Ico a (a + n), (f k - f (k - 1)) = f (a + n - 1) - f (a - 1)
  | 0 => by simp
  | n + 1 => by
      have ih := sum_Ico_telescope f a n
      rw [show a + ((n + 1 : ℕ) : ℤ) = (a + n) + 1 by push_cast; ring,
        Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_insert_right (by omega),
        Finset.sum_insert Finset.right_notMem_Ico, ih]
      rw [show a + (n : ℤ) + 1 - 1 = a + n by ring]
      ring

/-! ## §2  The sum side `E_n` -/

/-- Coefficient of `q^N` in `E_n = Σ_j q^{j(j+1)} [n-j, j]`. -/
def Ecoef (n : ℕ) (N : ℤ) : ℤ :=
  ∑ j ∈ range (n + 1), qc (n - j) (j : ℤ) (N - (j : ℤ) * ((j : ℤ) + 1))

theorem Ecoef_rec (n : ℕ) (N : ℤ) :
    Ecoef (n + 2) N = Ecoef (n + 1) N + Ecoef n (N - ((n : ℤ) + 2)) := by
  unfold Ecoef
  rw [Finset.sum_range_succ, show n + 2 - (n + 2) = 0 by omega,
    qc_of_gt 0 _ (by push_cast; omega), add_zero]
  have hsplit : ∀ j ∈ range (n + 2),
      qc (n + 2 - j) (j : ℤ) (N - (j : ℤ) * ((j : ℤ) + 1)) =
        qc (n + 1 - j) ((j : ℤ) - 1)
            (N - (j : ℤ) * ((j : ℤ) + 1) - (((n + 1 - j : ℕ) : ℤ) + 1 - j)) +
          qc (n + 1 - j) (j : ℤ) (N - (j : ℤ) * ((j : ℤ) + 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show n + 2 - j = (n + 1 - j) + 1 by omega, qc_succ']
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, add_comm]
  congr 1
  rw [Finset.sum_range_succ', qc_of_neg_m _ _ (by norm_num), add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show n + 1 - (i + 1) = n - i by omega]
  congr 1
  · push_cast; ring
  · push_cast
    rw [Nat.cast_sub (by omega : i ≤ n)]
    ring

theorem Ecoef_zero (N : ℤ) : Ecoef 0 N = if N = 0 then 1 else 0 := by
  simp [Ecoef, qc_zero_m]

theorem Ecoef_one (N : ℤ) : Ecoef 1 N = if N = 0 then 1 else 0 := by
  simp only [Ecoef, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [qc_of_gt 0 _ (by norm_num)]
  simp [qc_zero_m]

/-! ## §3  The alternating side `R_n` -/

/-- The `k`-th term of `R_n`, coefficient of `q^N`. -/
def Rterm (n : ℕ) (k N : ℤ) : ℤ := sgn k * qc (n + 1) (((n : ℤ) - 5 * k) / 2) (N - ee k)

/-- Coefficient of `q^N` in `R_n = Σ_k (-1)^k q^{k(5k+3)/2} [n+1, ⌊(n-5k)/2⌋]`. -/
def Rcoef (n : ℕ) (N : ℤ) : ℤ := ∑ k ∈ Ico (-(n : ℤ) - 2) ((n : ℤ) + 2), Rterm n k N

theorem Rterm_eq_zero (n : ℕ) {k : ℤ} (N : ℤ) (hk : k ∉ Ico (-(n : ℤ)) ((n : ℤ) + 1)) :
    Rterm n k N = 0 := by
  rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
  unfold Rterm
  rcases hk with hk | hk
  · rw [qc_of_gt _ _ (by push_cast; omega), mul_zero]
  · rw [qc_of_neg_m _ _ (by omega), mul_zero]

theorem sum_Rterm_eq (n : ℕ) (N : ℤ) {B : ℤ} (hB : (n : ℤ) + 1 ≤ B) :
    ∑ k ∈ Ico (-B) B, Rterm n k N = ∑ k ∈ Ico (-(n : ℤ)) ((n : ℤ) + 1), Rterm n k N := by
  symm
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Ico] at hk ⊢
    omega
  · intro k _ hk
    exact Rterm_eq_zero n N hk

theorem Rcoef_eq_sum (n : ℕ) (N : ℤ) {B : ℤ} (hB : (n : ℤ) + 1 ≤ B) :
    Rcoef n N = ∑ k ∈ Ico (-B) B, Rterm n k N := by
  rw [sum_Rterm_eq n N hB, Rcoef, show -(n : ℤ) - 2 = -((n : ℤ) + 2) by ring,
    sum_Rterm_eq n N (by omega)]

/-- The `q`-Pascal step on the odd parity class. -/
theorem odd_step (n : ℕ) (m M : ℤ) :
    qc (n + 3) m M - qc (n + 2) m M - qc (n + 1) (m - 1) (M - ((n : ℤ) + 2)) =
      qc (n + 1) (m - 2) (M - ((n : ℤ) + 3 - m)) := by
  rw [qc_succ' (n + 2) m M, qc_succ (n + 1) (m - 1)]
  push_cast
  rw [show m - 1 - 1 = m - 2 by ring,
    show M - ((n : ℤ) + 2 + 1 - m) - (m - 1) = M - ((n : ℤ) + 2) by ring,
    show (n : ℤ) + 2 + 1 - m = (n : ℤ) + 3 - m by ring]
  ring

/-- The `q`-Pascal step on the even parity class. -/
theorem even_step (n : ℕ) (m M : ℤ) :
    qc (n + 3) m M - qc (n + 2) (m - 1) M - qc (n + 1) (m - 1) (M - ((n : ℤ) + 2)) =
      qc (n + 1) m (M - m) := by
  rw [qc_succ (n + 2) m M, qc_succ' (n + 1) m (M - m)]
  push_cast
  rw [show M - m - ((n : ℤ) + 1 + 1 - m) = M - ((n : ℤ) + 2) by ring]
  ring

/-- The telescoping potential. -/
def Fpot (n : ℕ) (N k : ℤ) : ℤ :=
  if ((n : ℤ) + 2 - 5 * k) % 2 = 1 then
    sgn k * qc (n + 1) (((n : ℤ) + 1 - 5 * k) / 2 - 2)
      (N - ee k - ((n : ℤ) + 3 - ((n : ℤ) + 1 - 5 * k) / 2))
  else 0

/-- The defect of the `k`-th term is a difference of potentials. -/
theorem defect_eq (n : ℕ) (N k : ℤ) :
    Rterm (n + 2) k N - Rterm (n + 1) k N - Rterm n k (N - ((n : ℤ) + 2)) =
      Fpot n N k - Fpot n N (k - 1) := by
  unfold Rterm Fpot
  push_cast
  have hee := ee_sub_one k
  by_cases hpar : ((n : ℤ) + 2 - 5 * k) % 2 = 1
  · -- odd class: `F (k-1) = 0`
    rw [if_pos hpar, if_neg (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, m = ((n : ℤ) + 1 - 5 * k) / 2 := ⟨_, rfl⟩
    rw [show ((n : ℤ) + 2 - 5 * k) / 2 = m by omega,
      show ((n : ℤ) + 1 - 5 * k) / 2 = m by omega,
      show ((n : ℤ) - 5 * k) / 2 = m - 1 by omega,
      show N - ((n : ℤ) + 2) - ee k = (N - ee k) - ((n : ℤ) + 2) by ring]
    have h := odd_step n m (N - ee k)
    rw [show n + 2 + 1 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring]
    rw [← h]
    ring
  · -- even class: `F k = 0`, `F (k-1)` is the odd-class potential of `k - 1`
    rw [if_neg hpar, if_pos (by omega), sgn_sub_one]
    obtain ⟨m, hm⟩ : ∃ m, m = ((n : ℤ) + 2 - 5 * k) / 2 := ⟨_, rfl⟩
    rw [show ((n : ℤ) + 2 - 5 * k) / 2 = m by omega,
      show ((n : ℤ) + 1 - 5 * k) / 2 = m - 1 by omega,
      show ((n : ℤ) - 5 * k) / 2 = m - 1 by omega,
      show ((n : ℤ) + 1 - 5 * (k - 1)) / 2 - 2 = m by omega,
      show N - ee (k - 1) - ((n : ℤ) + 3 - ((n : ℤ) + 1 - 5 * (k - 1)) / 2) =
        (N - ee k) - m by omega,
      show N - ((n : ℤ) + 2) - ee k = (N - ee k) - ((n : ℤ) + 2) by ring]
    have h := even_step n m (N - ee k)
    rw [show n + 2 + 1 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring]
    rw [← h]
    ring

theorem Fpot_eq_zero (n : ℕ) (N : ℤ) {k : ℤ} (hk : (n : ℤ) + 2 ≤ |k|) : Fpot n N k = 0 := by
  unfold Fpot
  split_ifs with hpar
  · rcases le_or_gt 0 k with h0 | h0
    · rw [abs_of_nonneg h0] at hk
      rw [qc_of_neg_m _ _ (by omega), mul_zero]
    · rw [abs_of_neg h0] at hk
      rw [qc_of_gt _ _ (by push_cast; omega), mul_zero]
  · rfl

/-- **The recurrence of the alternating side.** -/
theorem Rcoef_rec (n : ℕ) (N : ℤ) :
    Rcoef (n + 2) N = Rcoef (n + 1) N + Rcoef n (N - ((n : ℤ) + 2)) := by
  have hB : ((n + 2 : ℕ) : ℤ) + 1 ≤ (n : ℤ) + 4 := by push_cast; omega
  rw [Rcoef_eq_sum (n + 2) N hB, Rcoef_eq_sum (n + 1) N (B := (n : ℤ) + 4) (by push_cast; omega),
    Rcoef_eq_sum n _ (B := (n : ℤ) + 4) (by omega)]
  rw [← sub_eq_iff_eq_add', ← sub_eq_zero, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun k _ => by
    rw [show Rterm (n + 2) k N - Rterm (n + 1) k N - Rterm n k (N - ((n : ℤ) + 2)) =
      Fpot n N k - Fpot n N (k - 1) from defect_eq n N k])]
  have hIco : Ico (-((n : ℤ) + 4)) ((n : ℤ) + 4) =
      Ico (-((n : ℤ) + 4)) (-((n : ℤ) + 4) + ((2 * (n + 4) : ℕ) : ℤ)) := by
    congr 1; push_cast; ring
  rw [hIco, sum_Ico_telescope]
  rw [Fpot_eq_zero n N (by rw [abs_of_nonneg (by push_cast; omega)]; push_cast; omega),
    Fpot_eq_zero n N (by rw [abs_of_neg (by omega)]; omega)]
  simp

theorem Rcoef_zero (N : ℤ) : Rcoef 0 N = if N = 0 then 1 else 0 := by
  unfold Rcoef
  rw [Finset.sum_eq_single (0 : ℤ)]
  · simp [Rterm, sgn, ee, qc_zero_m]
  · intro k hk hk0
    rw [Finset.mem_Ico] at hk
    unfold Rterm
    rcases lt_or_gt_of_ne hk0 with h | h
    · rw [qc_of_gt _ _ (by push_cast; omega), mul_zero]
    · rw [qc_of_neg_m _ _ (by omega), mul_zero]
  · intro h; exfalso; apply h; rw [Finset.mem_Ico]; norm_num

theorem Rcoef_one (N : ℤ) : Rcoef 1 N = if N = 0 then 1 else 0 := by
  unfold Rcoef
  rw [Finset.sum_eq_single (0 : ℤ)]
  · simp only [Rterm, sgn, ee]
    norm_num
    rw [qc_zero_m]
  · intro k hk hk0
    rw [Finset.mem_Ico] at hk
    unfold Rterm
    rcases lt_or_gt_of_ne hk0 with h | h
    · rw [qc_of_gt _ _ (by push_cast; omega), mul_zero]
    · rw [qc_of_neg_m _ _ (by push_cast; omega), mul_zero]
  · intro h; exfalso; apply h; rw [Finset.mem_Ico]; norm_num

/-- **Andrews' polynomial identity** (coefficientwise): `E_n = R_n`. -/
theorem Ecoef_eq_Rcoef : ∀ (n : ℕ) (N : ℤ), Ecoef n N = Rcoef n N
  | 0, N => by rw [Ecoef_zero, Rcoef_zero]
  | 1, N => by rw [Ecoef_one, Rcoef_one]
  | n + 2, N => by
      rw [Ecoef_rec, Rcoef_rec, Ecoef_eq_Rcoef (n + 1) N, Ecoef_eq_Rcoef n]

end

end VOA.RRLower
