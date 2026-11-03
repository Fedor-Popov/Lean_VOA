/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# Gaussian binomial coefficients, coefficientwise, and partitions with bounded parts

This is the first layer of the Rogers–Ramanujan side of the Lee–Yang character problem.  Every
object is an **integer-valued coefficient function**; no power series, no infinite products, no
analysis.

* `qc n m N` — the coefficient of `q^N` in the Gaussian binomial `[n, m]_q`, defined by the first
  `q`-Pascal rule `[n+1, m] = [n, m-1] + q^m [n, m]`, uniformly for **all** integers `m`, `N`
  (it vanishes for `m < 0`, `m > n`, `N < 0`).
* `qc_succ'` — the **second** `q`-Pascal rule `[n+1, m] = q^{n+1-m} [n, m-1] + [n, m]`,
  again uniform in `m, N` (no boundary cases).
* `pc j M` — the number of partitions of `M` into parts `≤ j` (zero for `M < 0`), with the
  two-term recursion `pc_succ_eq : pc (j+1) M = pc j M + pc (j+1) (M - (j+1))`.
* `qc_box` — **box stabilisation**: `qc (j + b) j M = pc j M` whenever `M ≤ b`.
* `pp M := pc M M` — the partition number `p(M)` (zero for `M < 0`), and `pc_eq_pp` :
  `pc j M = p(M)` once `M ≤ j`.

All proved, no hypotheses.
-/

namespace VOA.RRLower

open Finset

/-! ## §1  Gaussian binomial coefficients -/

/-- The coefficient of `q^N` in the Gaussian binomial `[n, m]_q`. -/
def qc : ℕ → ℤ → ℤ → ℤ
  | 0, m, N => if m = 0 ∧ N = 0 then 1 else 0
  | n + 1, m, N => qc n (m - 1) N + qc n m (N - m)

theorem qc_zero (m N : ℤ) : qc 0 m N = if m = 0 ∧ N = 0 then 1 else 0 := rfl

theorem qc_succ (n : ℕ) (m N : ℤ) : qc (n + 1) m N = qc n (m - 1) N + qc n m (N - m) := rfl

theorem qc_of_neg_m : ∀ (n : ℕ) {m : ℤ} (N : ℤ), m < 0 → qc n m N = 0
  | 0, m, N, h => by rw [qc_zero, if_neg]; omega
  | n + 1, m, N, h => by
      rw [qc_succ, qc_of_neg_m n N (by omega), qc_of_neg_m n (N - m) h, add_zero]

theorem qc_of_gt : ∀ (n : ℕ) {m : ℤ} (N : ℤ), (n : ℤ) < m → qc n m N = 0
  | 0, m, N, h => by rw [qc_zero, if_neg]; push_cast at h; omega
  | n + 1, m, N, h => by
      push_cast at h
      rw [qc_succ, qc_of_gt n N (by omega), qc_of_gt n (N - m) (by omega), add_zero]

theorem qc_of_neg_N : ∀ (n : ℕ) (m : ℤ) {N : ℤ}, N < 0 → qc n m N = 0
  | 0, m, N, h => by rw [qc_zero, if_neg]; omega
  | n + 1, m, N, h => by
      rw [qc_succ, qc_of_neg_N n (m - 1) h]
      rcases lt_or_ge m 0 with hm | hm
      · rw [qc_of_neg_m n _ hm, add_zero]
      · rw [qc_of_neg_N n m (by omega), add_zero]

theorem qc_zero_m : ∀ (n : ℕ) (N : ℤ), qc n 0 N = if N = 0 then 1 else 0
  | 0, N => by rw [qc_zero]; simp
  | n + 1, N => by
      rw [qc_succ, qc_of_neg_m n N (by norm_num), zero_add, sub_zero, qc_zero_m n N]

/-- **The second `q`-Pascal rule**, uniform in `m` and `N`:
`[n+1, m] = q^{n+1-m} [n, m-1] + [n, m]`. -/
theorem qc_succ' : ∀ (n : ℕ) (m N : ℤ),
    qc (n + 1) m N = qc n (m - 1) (N - ((n : ℤ) + 1 - m)) + qc n m N
  | 0, m, N => by
      simp only [qc_succ, qc_zero]
      push_cast
      split_ifs <;> omega
  | n + 1, m, N => by
      have h1 := qc_succ' n (m - 1) N
      have h2 := qc_succ' n m (N - m)
      rw [qc_succ (n + 1) m N, h1, h2, qc_succ n (m - 1), qc_succ n m N]
      push_cast
      have e1 : N - ((n : ℤ) + 1 - (m - 1)) = N - ((n : ℤ) + 1 + 1 - m) := by ring
      have e2 : N - m - ((n : ℤ) + 1 - m) = N - ((n : ℤ) + 1 + 1 - m) - (m - 1) := by ring
      rw [e1, e2]
      ring

/-! ## §2  Partitions with bounded parts -/

/-- The number of partitions of `M` into parts `≤ j` (zero for `M < 0`). -/
def pc : ℕ → ℤ → ℤ
  | 0, M => if M = 0 then 1 else 0
  | j + 1, M => ∑ t ∈ range (M.toNat + 1), pc j (M - ((j : ℤ) + 1) * t)

theorem pc_of_neg : ∀ (j : ℕ) {M : ℤ}, M < 0 → pc j M = 0
  | 0, M, h => by simp only [pc]; rw [if_neg]; omega
  | j + 1, M, h => by
      simp only [pc]
      refine Finset.sum_eq_zero fun t _ => pc_of_neg j ?_
      have : (0 : ℤ) ≤ ((j : ℤ) + 1) * t := by positivity
      omega

/-- The defining sum may be taken over any range `B ≥ M`. -/
theorem pc_succ_range (j : ℕ) (M : ℤ) (B : ℕ) (hB : M ≤ B) :
    pc (j + 1) M = ∑ t ∈ range (B + 1), pc j (M - ((j : ℤ) + 1) * t) := by
  rcases lt_or_ge M 0 with hM | hM
  · rw [pc_of_neg _ hM]
    refine (Finset.sum_eq_zero fun t _ => pc_of_neg j ?_).symm
    have : (0 : ℤ) ≤ ((j : ℤ) + 1) * t := by positivity
    omega
  · simp only [pc]
    apply Finset.sum_subset
    · intro t ht
      simp only [Finset.mem_range] at ht ⊢
      omega
    · intro t ht hnt
      simp only [Finset.mem_range] at ht hnt
      apply pc_of_neg
      have : (t : ℤ) ≥ M.toNat + 1 := by exact_mod_cast (by omega : t ≥ M.toNat + 1)
      have h2 : ((j : ℤ) + 1) * t ≥ 1 * t := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [(Nat.cast_nonneg j : (0:ℤ) ≤ j)]
      omega

/-- The two-term recursion of partitions into parts `≤ j + 1`. -/
theorem pc_succ_eq (j : ℕ) (M : ℤ) : pc (j + 1) M = pc j M + pc (j + 1) (M - ((j : ℤ) + 1)) := by
  rcases lt_or_ge M 0 with hM | hM
  · rw [pc_of_neg _ hM, pc_of_neg _ hM, pc_of_neg _ (by omega)]; simp
  · obtain ⟨B, hB⟩ : ∃ B : ℕ, (B : ℤ) = M := ⟨M.toNat, Int.toNat_of_nonneg hM⟩
    rw [pc_succ_range j M B hB.ge, pc_succ_range j (M - ((j : ℤ) + 1)) B (by
      have : (0 : ℤ) ≤ j := Nat.cast_nonneg j
      omega), Finset.sum_range_succ', Finset.sum_range_succ]
    have hlast : pc j (M - ((j : ℤ) + 1) - ((j : ℤ) + 1) * (B : ℕ)) = 0 := by
      apply pc_of_neg
      have : (0 : ℤ) ≤ j := Nat.cast_nonneg j
      nlinarith
    rw [hlast, add_zero]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    push_cast
    ring

theorem pc_zero (M : ℤ) : pc 0 M = if M = 0 then 1 else 0 := rfl

/-- Parts `≤ j` and parts `≤ j + 1` give the same count once `M ≤ j`. -/
theorem pc_succ_of_le (j : ℕ) {M : ℤ} (h : M ≤ j) : pc (j + 1) M = pc j M := by
  rw [pc_succ_eq, pc_of_neg (j + 1) (M := M - ((j : ℤ) + 1)) (by omega), add_zero]

/-- The partition number `p(M)` (zero for `M < 0`). -/
def pp (M : ℤ) : ℤ := pc M.toNat M

theorem pc_eq_pp : ∀ (j : ℕ) {M : ℤ}, M ≤ j → pc j M = pp M := by
  intro j M h
  rcases lt_or_ge M 0 with hM | hM
  · rw [pp, pc_of_neg _ hM, pc_of_neg _ hM]
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, j = M.toNat + d := ⟨j - M.toNat, by omega⟩
    subst hd
    unfold pp
    induction d with
    | zero => rfl
    | succ d ih =>
        rw [← Nat.add_assoc, pc_succ_of_le _ (by push_cast; omega)]
        exact ih (by push_cast; omega)

theorem pp_of_neg {M : ℤ} (h : M < 0) : pp M = 0 := pc_of_neg _ h

/-! ## §3  Box stabilisation -/

/-- **Box stabilisation**: the coefficient of `q^M` in `[j + b, j]` is the number of
partitions of `M` into parts `≤ j`, as soon as `M ≤ b`. -/
theorem qc_box : ∀ (j b : ℕ) (M : ℤ), M ≤ b → qc (j + b) j M = pc j M
  | 0, b, M, _ => by rw [zero_add, Nat.cast_zero, qc_zero_m, pc_zero]
  | j + 1, b, M, h => by
      induction b generalizing M with
      | zero =>
          have h0 : M ≤ 0 := by simpa using h
          rw [show j + 1 + 0 = j + 1 from rfl, qc_succ]
          push_cast
          rw [show ((j : ℤ) + 1 - 1) = j by ring,
            qc_of_gt j (M - ((j : ℤ) + 1)) (by omega : (j : ℤ) < (j : ℤ) + 1), add_zero]
          have h3 := qc_box j 0 M (by simpa using h)
          simp only [Nat.add_zero] at h3
          rw [h3, pc_succ_eq, pc_of_neg (j + 1) (M := M - ((j : ℤ) + 1)) (by omega), add_zero]
      | succ b ih =>
          rw [show j + 1 + (b + 1) = (j + b + 1) + 1 by ring, qc_succ]
          push_cast
          rw [show ((j : ℤ) + 1 - 1) = j by ring, show j + b + 1 = j + (b + 1) by ring,
            qc_box j (b + 1) M h, show j + (b + 1) = (j + 1) + b by ring]
          have h4 := ih (M - ((j : ℤ) + 1)) (by push_cast at h ⊢; omega)
          push_cast at h4
          rw [h4, ← pc_succ_eq]

end VOA.RRLower
