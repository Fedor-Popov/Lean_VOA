/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Ring.GeomSum

/-!
# Ramanujan sums and rational traces of finite-order operators

Let `A` be an endomorphism of a finite-dimensional vector space over a field `K` of characteristic
zero with `A^N = 1`, and suppose `tr(A^u) = tr(A)` for every `u` coprime to `N` (Galois invariance
of the trace). Then `tr A ∈ ℚ` (`exists_rat_trace_of_trace_pow_coprime`).

The proof uses no eigenvalues. Möbius inversion of the coprimality indicator gives
(`sum_coprime_eq_sum_divisors_moebius`)

  `Σ_{u < N, (u,N) = 1} A^u = Σ_{e ∣ N} μ(e) Σ_{k < N/e} (A^e)^k`,

and for `B^M = 1` the averaging sum `P = Σ_{k < M} B^k` satisfies `P² = M·P`, so `P/M` is an
idempotent and `tr P = M · rank(P/M)` is `M` times a natural number
(`exists_trace_geom_sum_eq_of_pow_eq_one`).
Hence `φ(N) · tr A = Σ_{u coprime} tr(A^u)` is an integer, and `tr A ∈ ℚ`.

(`Notes/monster_aut/RATIONALITY.md`, §2.4, steps 3c–3e; the eigenvalue form of the Ramanujan sum
`Σ_{u coprime} λ^u ∈ ℤ` is the same identity read on an eigenvector.)

## Main results
* `sum_divisors_moebius_eq_ite`, `filter_divisors_dvd_eq_divisors_gcd`,
  ⭐ `sum_coprime_eq_sum_divisors_moebius`.
* `exists_trace_eq_mul_natCast_of_mul_self`, ⭐ `exists_trace_geom_sum_eq_of_pow_eq_one`.
* ⭐ `exists_rat_trace_of_trace_pow_coprime`.
-/

namespace VOA.Moonshine.Rationality

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## Möbius inversion of the coprimality indicator -/

/-- `Σ_{e ∣ n} μ(e) = [n = 1]`. -/
theorem sum_divisors_moebius_eq_ite (n : ℕ) :
    ∑ e ∈ n.divisors, μ e = if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only at h
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- For `n ≠ 0`, the divisors of `n` dividing `u` are the divisors of `gcd(n, u)`. -/
theorem filter_divisors_dvd_eq_divisors_gcd (n u : ℕ) (hn : n ≠ 0) :
    n.divisors.filter (· ∣ u) = (n.gcd u).divisors := by
  ext e
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left u (Nat.pos_of_ne_zero hn)).ne'⟩
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨⟨h1, hn⟩, h2⟩

/-- For `e ∣ N`, `e > 0`: the multiples of `e` below `N` are `e·k`, `k < N/e`. -/
theorem sum_filter_dvd_range_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) {N e : ℕ}
    (he : 0 < e) (hdvd : e ∣ N) :
    ∑ u ∈ (range N).filter (e ∣ ·), f u = ∑ k ∈ range (N / e), f (e * k) := by
  refine Finset.sum_nbij' (fun u => u / e) (fun k => e * k) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
    exact Nat.div_lt_div_of_lt_of_dvd hdvd hu.1
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    refine ⟨?_, Dvd.intro k rfl⟩
    calc e * k < e * (N / e) := Nat.mul_lt_mul_of_pos_left hk he
      _ = N := Nat.mul_div_cancel' hdvd
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact Nat.mul_div_cancel' hu.2
  · intro k _
    exact Nat.mul_div_cancel_left k he
  · intro u hu
    rw [Finset.mem_filter] at hu
    change f u = f (e * (u / e))
    rw [Nat.mul_div_cancel' hu.2]

/-- ⭐ **Möbius inversion of coprimality**: for every `f : ℕ → M`,
`Σ_{u < N, (N,u) = 1} f(u) = Σ_{e ∣ N} μ(e) Σ_{k < N/e} f(e·k)`. -/
theorem sum_coprime_eq_sum_divisors_moebius {M : Type*} [AddCommGroup M] (f : ℕ → M) (N : ℕ) :
    ∑ u ∈ (range N).filter N.Coprime, f u
      = ∑ e ∈ N.divisors, μ e • ∑ k ∈ range (N / e), f (e * k) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : N ≠ 0 := hN.ne'
  calc ∑ u ∈ (range N).filter N.Coprime, f u
      = ∑ u ∈ range N, ∑ e ∈ N.divisors.filter (· ∣ u), μ e • f u := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.sum_smul, filter_divisors_dvd_eq_divisors_gcd N u hN0,
          sum_divisors_moebius_eq_ite]
        by_cases h : N.gcd u = 1
        · have hc : N.Coprime u := h
          simp [hc]
        · have hc : ¬ N.Coprime u := h
          simp [hc]
    _ = ∑ e ∈ N.divisors, ∑ u ∈ (range N).filter (e ∣ ·), μ e • f u := by
        refine Finset.sum_comm' fun u e => ?_
        simp only [Finset.mem_range, Finset.mem_filter]
        tauto
    _ = ∑ e ∈ N.divisors, μ e • ∑ k ∈ range (N / e), f (e * k) := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [← Finset.smul_sum, sum_filter_dvd_range_eq f (Nat.pos_of_mem_divisors he)
          (Nat.dvd_of_mem_divisors he)]

/-! ## Traces of averaging sums are natural numbers -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- For `B^M = 1`, `B` fixes the averaging sum: `B · Σ_{k<M} B^k = Σ_{k<M} B^k`. -/
theorem mul_geom_sum_eq_of_pow_eq_one (B : Module.End K V) {M : ℕ} (hB : B ^ M = 1) :
    B * ∑ k ∈ range M, B ^ k = ∑ k ∈ range M, B ^ k := by
  have h := mul_geom_sum B M
  rw [hB, sub_self, sub_mul, one_mul, sub_eq_zero] at h
  exact h

omit [FiniteDimensional K V] in
theorem pow_mul_geom_sum_eq_of_pow_eq_one (B : Module.End K V) {M : ℕ} (hB : B ^ M = 1)
    (j : ℕ) : B ^ j * ∑ k ∈ range M, B ^ k = ∑ k ∈ range M, B ^ k := by
  induction j with
  | zero => rw [pow_zero, one_mul]
  | succ j ih => rw [pow_succ', mul_assoc, ih, mul_geom_sum_eq_of_pow_eq_one B hB]

omit [FiniteDimensional K V] in
/-- For `B^M = 1`, the averaging sum `P = Σ_{k<M} B^k` satisfies `P² = M·P`. -/
theorem geom_sum_mul_geom_sum_of_pow_eq_one (B : Module.End K V) {M : ℕ} (hB : B ^ M = 1) :
    (∑ k ∈ range M, B ^ k) * ∑ k ∈ range M, B ^ k = (M : K) • ∑ k ∈ range M, B ^ k := by
  rw [Finset.sum_mul]
  simp_rw [pow_mul_geom_sum_eq_of_pow_eq_one B hB]
  rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]

/-- If `P² = c·P` with `c ≠ 0`, then `tr P = c · rank(P/c)` is `c` times a natural number. -/
theorem exists_trace_eq_mul_natCast_of_mul_self (P : Module.End K V) {c : K} (hc : c ≠ 0)
    (hP : P * P = c • P) : ∃ m : ℕ, LinearMap.trace K V P = c * m := by
  have hQ : IsIdempotentElem (c⁻¹ • P) := by
    change (c⁻¹ • P) * (c⁻¹ • P) = c⁻¹ • P
    rw [smul_mul_smul_comm, hP, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  refine ⟨Module.finrank K (LinearMap.range (c⁻¹ • P)), ?_⟩
  have htr := LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hQ)
  rw [map_smul, smul_eq_mul] at htr
  rw [← htr, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- ⭐ For `B^M = 1`, `M > 0`, over a field of characteristic zero, the trace of the averaging sum
`Σ_{k<M} B^k` is `M` times a natural number (the dimension of the fixed space). -/
theorem exists_trace_geom_sum_eq_of_pow_eq_one [CharZero K] (B : Module.End K V) {M : ℕ}
    (hM : 0 < M) (hB : B ^ M = 1) :
    ∃ m : ℕ, LinearMap.trace K V (∑ k ∈ range M, B ^ k) = ((M * m : ℕ) : K) := by
  obtain ⟨m, hm⟩ := exists_trace_eq_mul_natCast_of_mul_self _
    (Nat.cast_ne_zero.2 hM.ne' : (M : K) ≠ 0) (geom_sum_mul_geom_sum_of_pow_eq_one B hB)
  exact ⟨m, by rw [hm, Nat.cast_mul]⟩

/-! ## Rationality of Galois-invariant traces -/

/-- ⭐ **Galois-invariant traces of finite-order operators are rational.** Over a field of
characteristic zero, if `A^N = 1` (`N > 0`) and `tr(A^u) = tr(A)` for every `u` coprime to `N`,
then `tr A` is a rational number: `φ(N) · tr A = Σ_{e ∣ N} μ(e) · tr(Σ_{k<N/e} A^{ek}) ∈ ℤ`. -/
theorem exists_rat_trace_of_trace_pow_coprime [CharZero K] (A : Module.End K V) {N : ℕ}
    (hN : 0 < N) (hA : A ^ N = 1)
    (hgal : ∀ u : ℕ, N.Coprime u → LinearMap.trace K V (A ^ u) = LinearMap.trace K V A) :
    ∃ r : ℚ, LinearMap.trace K V A = r := by
  classical
  have hsum : ∑ u ∈ (range N).filter N.Coprime, LinearMap.trace K V (A ^ u)
      = ∑ e ∈ N.divisors, μ e • ∑ k ∈ range (N / e), LinearMap.trace K V (A ^ (e * k)) :=
    sum_coprime_eq_sum_divisors_moebius (fun u => LinearMap.trace K V (A ^ u)) N
  have hL : ∑ u ∈ (range N).filter N.Coprime, LinearMap.trace K V (A ^ u)
      = (Nat.totient N : K) * LinearMap.trace K V A := by
    rw [Finset.sum_congr rfl fun u hu => hgal u (Finset.mem_filter.1 hu).2, Finset.sum_const,
      ← Nat.totient_eq_card_coprime, nsmul_eq_mul]
  have hblock : ∀ e ∈ N.divisors, ∃ z : ℤ,
      ∑ k ∈ range (N / e), LinearMap.trace K V (A ^ (e * k)) = (z : K) := by
    intro e he
    have hpos : 0 < N / e := Nat.div_pos (Nat.divisor_le he) (Nat.pos_of_mem_divisors he)
    have hpow : (A ^ e) ^ (N / e) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he), hA]
    obtain ⟨m, hm⟩ := exists_trace_geom_sum_eq_of_pow_eq_one (A ^ e) hpos hpow
    refine ⟨((N / e * m : ℕ) : ℤ), ?_⟩
    simp_rw [pow_mul]
    rw [← map_sum, hm, Int.cast_natCast]
  choose! z hz using hblock
  have hR : ∑ e ∈ N.divisors, μ e • ∑ k ∈ range (N / e), LinearMap.trace K V (A ^ (e * k))
      = ((∑ e ∈ N.divisors, μ e * z e : ℤ) : K) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hz e he, zsmul_eq_mul, Int.cast_mul]
  rw [hL, hR] at hsum
  have hφ : (Nat.totient N : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.totient_pos.2 hN).ne'
  refine ⟨((∑ e ∈ N.divisors, μ e * z e : ℤ) : ℚ) / (Nat.totient N : ℚ), ?_⟩
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hφ, ← hsum]
  ring

end VOA.Moonshine.Rationality
