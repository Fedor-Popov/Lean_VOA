/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeCoeff

/-!
# Serre–Stark S3-3: the coefficient operators `T(p²)` commute

`heckeCoeff_comm`: for distinct primes `p, q`, Shimura's coefficient operators commute:
`T(p²) T(q²) a = T(q²) T(p²) a` for every sequence `a : ℕ → ℂ` (pure algebra with Legendre
symbols).
-/

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

theorem legendre_sq_mul (hpq : p ≠ q) (n : ℤ) :
    legendreSym p ((q : ℤ) ^ 2 * n) = legendreSym p n := by
  rw [legendreSym.mul, legendreSym.sq_one', one_mul]
  intro h
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
  have : p ∣ q := by exact_mod_cast this
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).1 this)

theorem coprime_sq (hpq : p ≠ q) : Nat.Coprime (p ^ 2) (q ^ 2) :=
  ((Nat.coprime_primes hp.out hq.out).2 hpq).pow 2 2

theorem sq_dvd_sq_mul_iff (hpq : p ≠ q) (n : ℕ) : p ^ 2 ∣ q ^ 2 * n ↔ p ^ 2 ∣ n :=
  ⟨fun h => (coprime_sq hpq).dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h _⟩

theorem sq_dvd_div_iff (hpq : p ≠ q) {n : ℕ} (hqn : q ^ 2 ∣ n) :
    p ^ 2 ∣ n / q ^ 2 ↔ p ^ 2 ∣ n := by
  obtain ⟨m, rfl⟩ := hqn
  rw [Nat.mul_div_cancel_left _ (pow_pos hq.out.pos 2), sq_dvd_sq_mul_iff hpq]

theorem legendre_div (hpq : p ≠ q) {n : ℕ} (hqn : q ^ 2 ∣ n) :
    legendreSym p ((n / q ^ 2 : ℕ) : ℤ) = legendreSym p (n : ℤ) := by
  obtain ⟨m, rfl⟩ := hqn
  rw [Nat.mul_div_cancel_left _ (pow_pos hq.out.pos 2)]
  push_cast
  rw [legendre_sq_mul hpq]

/-- **Commutation of Shimura's coefficient operators** (distinct primes). -/
theorem heckeCoeff_comm {N : ℕ} (χ : DirichletCharacter ℂ N) (hpq : p ≠ q) (a : ℕ → ℂ)
    (n : ℕ) :
    heckeCoeff χ p (heckeCoeff χ q a) n = heckeCoeff χ q (heckeCoeff χ p a) n := by
  have hqp : q ≠ p := hpq.symm
  have hP : 0 < p ^ 2 := pow_pos hp.out.pos 2
  have hQ : 0 < q ^ 2 := pow_pos hq.out.pos 2
  simp only [heckeCoeff]
  -- normalise the arguments
  have e1 : q ^ 2 * (p ^ 2 * n) = p ^ 2 * (q ^ 2 * n) := by ring
  rw [e1]
  have l1 : legendreSym q ((p ^ 2 * n : ℕ) : ℤ) = legendreSym q (n : ℤ) := by
    push_cast; exact legendre_sq_mul hqp _
  have l2 : legendreSym p ((q ^ 2 * n : ℕ) : ℤ) = legendreSym p (n : ℤ) := by
    push_cast; exact legendre_sq_mul hpq _
  rw [l1, l2, if_congr (sq_dvd_sq_mul_iff hqp n) rfl rfl,
    if_congr (sq_dvd_sq_mul_iff hpq n) rfl rfl]
  by_cases hpn : p ^ 2 ∣ n <;> by_cases hqn : q ^ 2 ∣ n
  · rw [if_pos hpn, if_pos hqn, if_pos hpn, if_pos hqn, if_pos hqn, if_pos hpn,
      if_pos ((sq_dvd_div_iff hqp hpn).2 hqn), if_pos ((sq_dvd_div_iff hpq hqn).2 hpn),
      legendre_div hqp hpn, legendre_div hpq hqn]
    have d1 : p ^ 2 * n / q ^ 2 = p ^ 2 * (n / q ^ 2) := Nat.mul_div_assoc _ hqn
    have d2 : q ^ 2 * n / p ^ 2 = q ^ 2 * (n / p ^ 2) := Nat.mul_div_assoc _ hpn
    have d3 : n / p ^ 2 / q ^ 2 = n / q ^ 2 / p ^ 2 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    rw [d1, d2, d3]
    ring
  · rw [if_pos hpn, if_neg hqn, if_pos hpn, if_neg hqn, if_neg hqn, if_pos hpn,
      if_neg (fun h => hqn ((sq_dvd_div_iff hqp hpn).1 h)), legendre_div hqp hpn]
    have d2 : q ^ 2 * n / p ^ 2 = q ^ 2 * (n / p ^ 2) := Nat.mul_div_assoc _ hpn
    rw [d2]
    ring
  · rw [if_neg hpn, if_pos hqn, if_neg hpn, if_pos hqn, if_pos hqn, if_neg hpn,
      if_neg (fun h => hpn ((sq_dvd_div_iff hpq hqn).1 h)), legendre_div hpq hqn]
    have d1 : p ^ 2 * n / q ^ 2 = p ^ 2 * (n / q ^ 2) := Nat.mul_div_assoc _ hqn
    rw [d1]
    ring
  · rw [if_neg hpn, if_neg hqn, if_neg hpn, if_neg hqn, if_neg hqn, if_neg hpn]
    ring

end SSHecke

end VOA.Classification.COne
