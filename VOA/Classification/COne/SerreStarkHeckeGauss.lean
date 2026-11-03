/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeCoset

/-!
# Serre–Stark S3-1b: quadratic Gauss sums with a linear term

Finite exponential sums over `ℤ/m` used for the Weil-representation computation of Shimura's
`T(p²)` (`SerreStarkHeckeWeil`):

* `sum_E_lin`: `Σ_{z mod m} e(kz/m) = m·[m ∣ k]`;
* `gsl_complete`: completing the square, `Σ_z e((a z² + k z)/m) = e(−β k²/m) g(m, a)` when
  `4aβ ≡ 1 (mod m)`;
* `gsl_p_mul`: the degenerate case `a = p a₁` modulo `p²`;
* `gs_p_one_ne_zero`: `g(p, 1) ≠ 0` (from Gauss's sign theorem `gaussG_one` and CRT).
-/

open Complex
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

open WeilGalois

/-- `Σ_{z mod m} e((a z² + k z)/m)`. -/
def gsl (m : ℕ) (a k : ℤ) : ℂ := ∑ z : Fin m, E m (a * ((z : ℕ) : ℤ) ^ 2 + k * ((z : ℕ) : ℤ))

theorem E_periodic_quad {m : ℕ} (hm : 0 < m) (a k x : ℤ) :
    E m (a * (x + m) ^ 2 + k * (x + m)) = E m (a * x ^ 2 + k * x) := by
  rw [← E_period hm (a * x ^ 2 + k * x) (2 * a * x + a * m + k)]
  congr 1; ring

/-- Shift invariance of a sum over `ℤ/m`. -/
theorem sum_shift {m : ℕ} (hm : 0 < m) (F : ℤ → ℂ) (hF : ∀ x, F (x + m) = F x) (t : ℤ) :
    ∑ z : Fin m, F (((z : ℕ) : ℤ) + t) = ∑ z : Fin m, F ((z : ℕ) : ℤ) := by
  refine resid_sum hm F hF (by simp) (fun z : Fin m => ((z : ℕ) : ℤ) + t) ?_
  intro i j h
  exact fin_eq_of_modEq (Int.ModEq.add_right_cancel' t h)

/-- Orthogonality: `Σ_{z mod m} e(kz/m) = m [m ∣ k]`. -/
theorem sum_E_lin {m : ℕ} (hm : 0 < m) (k : ℤ) :
    ∑ z : Fin m, E m (k * ((z : ℕ) : ℤ)) = if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    have : ∀ z : Fin m, E m ((m : ℤ) * q * ((z : ℕ) : ℤ)) = 1 := fun z => by
      rw [mul_assoc]; exact E_mul_self hm _
    simp [this]
  · exact sum_E_eq_zero hm h

/-- **Completing the square.** If `4aβ ≡ 1 (mod m)` then
`Σ_z e((a z² + k z)/m) = e(−β k²/m) g(m, a)`. -/
theorem gsl_complete {m : ℕ} (hm : 0 < m) {a β : ℤ} (hβ : 4 * a * β ≡ 1 [ZMOD m]) (k : ℤ) :
    gsl m a k = E m (-(β * k ^ 2)) * gs m a := by
  have key : ∀ x : ℤ, E m (a * x ^ 2 + k * x) =
      E m (-(β * k ^ 2)) * E m (a * (x + 2 * β * k) ^ 2) := by
    intro x
    rw [← E_add]
    apply E_congr hm
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.1 hβ.symm
    refine Int.modEq_iff_dvd.2 ⟨(k * x + β * k ^ 2) * t, ?_⟩
    linear_combination (k * x + β * k ^ 2) * ht
  unfold gsl gs
  simp_rw [key]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_shift hm (fun x => E m (a * x ^ 2)) (fun x => gs_periodic hm a x) (2 * β * k)

/-- The degenerate case modulo `p²`: `Σ_{z mod p²} e((p a₁ z² + k z)/p²) = p [p ∣ k] g_l(p, a₁, k/p)`. -/
theorem gsl_p_mul {p : ℕ} (hp : 0 < p) (a₁ k : ℤ) :
    gsl (p ^ 2) (p * a₁) k = if (p : ℤ) ∣ k then (p : ℂ) * gsl p a₁ (k / p) else 0 := by
  have hP : 0 < p ^ 2 := pow_pos hp 2
  unfold gsl
  have hs := sum_split (m := p) (n := p) (by ring) hP
    (fun x : ℤ => E (p ^ 2) (p * a₁ * x ^ 2 + k * x)) (E_periodic_quad hP _ _)
  simp only at hs
  rw [hs]
  have inner : ∀ y : ℤ, ∑ z : Fin p, E (p ^ 2) (p * a₁ * (y + p * ((z : ℕ) : ℤ)) ^ 2 +
      k * (y + p * ((z : ℕ) : ℤ))) =
      E (p ^ 2) (p * a₁ * y ^ 2 + k * y) * (if (p : ℤ) ∣ k then (p : ℂ) else 0) := by
    intro y
    have e : ∀ z : ℤ, E (p ^ 2) (p * a₁ * (y + p * z) ^ 2 + k * (y + p * z)) =
        E (p ^ 2) (p * a₁ * y ^ 2 + k * y) * E p (k * z) := by
      intro z
      rw [show p * a₁ * (y + p * z) ^ 2 + k * (y + p * z) =
          (p * a₁ * y ^ 2 + k * y) + ((p ^ 2 : ℕ) : ℤ) * (2 * a₁ * y * z + a₁ * p * z ^ 2)
            + p * (k * z) by push_cast; ring, E_add, E_add, E_mul_self hP, mul_one,
        show p ^ 2 = p * p by ring, E_mul_left hp]
    simp_rw [e]
    rw [← Finset.mul_sum, sum_E_lin hp]
  simp_rw [inner]
  split_ifs with hk
  · obtain ⟨k₁, rfl⟩ := hk
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0),
      show p * a₁ * ((y : ℕ) : ℤ) ^ 2 + p * k₁ * ((y : ℕ) : ℤ) =
        p * (a₁ * ((y : ℕ) : ℤ) ^ 2 + k₁ * ((y : ℕ) : ℤ)) by ring,
      show p ^ 2 = p * p by ring, E_mul_left hp]
  · simp

/-- `g(p², a) = p` for `p ∤ a`, `p` an odd prime. -/
theorem gs_p_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    gs (p ^ 2) a = p := by
  have := gs_p2 hp hp2 one_pos ha
  rw [mul_one] at this
  rw [this, gs_one_mod, mul_one]

/-- `g(p, 1) ≠ 0` for an odd prime `p`. -/
theorem gs_p_one_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : gs p 1 ≠ 0 := by
  have hp0 := hp.pos
  have h4p : gs (4 * p) 1 ≠ 0 := by
    rw [gs_four_mul hp0, gaussG_one hp0]
    refine mul_ne_zero two_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) ?_)
    have : (0 : ℝ) < Real.sqrt (2 * p) := Real.sqrt_pos.2 (by positivity)
    exact_mod_cast this.ne'
  have hcop : Nat.Coprime 4 p := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hp).2 hp2.symm)
  rw [gs_crt (by norm_num) hp0 hcop] at h4p
  have h4 : gs p (1 * 4) ≠ 0 := right_ne_zero_of_mul h4p
  haveI : Fact p.Prime := ⟨hp⟩
  have hu : ((1 * 4 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
    have h2 : (p : ℤ) ∣ 2 ^ 2 := by simpa using this
    have := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h2
    have : p ∣ 2 := by exact_mod_cast this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  rw [gs_prime hp2 hu] at h4
  exact right_ne_zero_of_mul h4

end SSHecke

end VOA.Classification.COne
