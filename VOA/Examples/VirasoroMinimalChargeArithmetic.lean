/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVOA

/-!
# Arithmetic separation of minimal-model charges

Equal charges force the same ratio p/q or its reciprocal. For a coprime pair,
all positive integral labels at that charge are multiples of that pair or its
swap. Consequently the first candidate singular level is unique up to swapping
p and q. This is only the arithmetic part of a Kac determinant argument: no
factorization of the actual partition determinant is assumed or proved here.
-/
namespace VOA.VirMinimalArithmetic

/-- Equality of positive-label minimal charges factors into equality of the
label ratios or their reciprocals. Clearing the nonzero denominators gives
(p s-q r)(p r-q s)=0 over the rationals. -/
theorem charge_eq_iff_cross {p q r s : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s) :
    minimalCentralCharge p q = minimalCentralCharge r s ↔
      p*s = q*r ∨ p*r = q*s := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hr0 : (r:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hs0 : (s:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  constructor
  · intro h
    unfold minimalCentralCharge at h
    field_simp at h
    have hh : ((p:ℚ)*s-q*r)*((p:ℚ)*r-q*s) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hh with hh | hh
    · left; exact_mod_cast sub_eq_zero.mp hh
    · right; exact_mod_cast sub_eq_zero.mp hh
  · intro h
    unfold minimalCentralCharge
    field_simp
    rcases h with h | h
    · have hh : (p:ℚ)*s = q*r := by exact_mod_cast h
      have hh0 : ((p:ℚ)*s-q*r)*((p:ℚ)*r-q*s) = 0 := by rw [hh]; simp
      nlinarith [hh0]
    · have hh : (p:ℚ)*r = q*s := by exact_mod_cast h
      have hh0 : ((p:ℚ)*s-q*r)*((p:ℚ)*r-q*s) = 0 := by rw [hh]; simp
      nlinarith [hh0]

/-- A positive integral pair with the same ratio as a coprime pair is a
positive integral multiple of it. Coprimality removes the possible denominator
in that proportionality factor. -/
theorem exists_scale_of_cross {p q r s : ℕ} (hp : 0 < p) (hr : 0 < r)
    (hpq : p.Coprime q) (h : p*s = q*r) :
    ∃ k : ℕ, 0 < k ∧ r = k*p ∧ s = k*q := by
  have hd : p ∣ r := hpq.dvd_of_dvd_mul_left (by rw [← h]; exact dvd_mul_right _ _)
  obtain ⟨k, hk⟩ := hd
  have hsk : s = k*q := Nat.eq_of_mul_eq_mul_left hp (by nlinarith [h, hk])
  refine ⟨k, ?_, by simpa only [Nat.mul_comm] using hk, hsk⟩
  by_contra hn
  have : k = 0 := by omega
  simp [this] at hk
  omega

/-- Every positive integral label at a primitive minimal charge is a positive
multiple of its defining pair, possibly with the two labels interchanged. -/
theorem charge_eq_scales {p q r s : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (hpq : p.Coprime q) (h : minimalCentralCharge p q = minimalCentralCharge r s) :
    (∃ k : ℕ, 0 < k ∧ r = k*p ∧ s = k*q) ∨
      (∃ k : ℕ, 0 < k ∧ s = k*p ∧ r = k*q) := by
  rcases (charge_eq_iff_cross hp hq hr hs).mp h with h | h
  · exact Or.inl (exists_scale_of_cross hp hr hpq h)
  · exact Or.inr (exists_scale_of_cross hp hs hpq h)

/-- Multiplying both labels by an integer greater than one strictly increases
the candidate singular level (p-1)(q-1), when both labels are at least two. -/
theorem scaled_level_strict {p q k : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 1 < k) :
    (p-1)*(q-1) < (k*p-1)*(k*q-1) := by
  have hp' : p < k*p := by nlinarith
  have hq' : q ≤ k*q := by nlinarith
  have h1 : p-1 < k*p-1 := by omega
  have h2 : q-1 ≤ k*q-1 := by omega
  have h3 : 0 < q-1 := by omega
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 h3) (Nat.mul_le_mul_left _ h2)

/-- At or below the first candidate singular level, no other positive labels
have the same minimal charge, except the pair with its order reversed. This
rules out arithmetic collisions once a determinant factorization is supplied. -/
theorem first_level_labels_unique {p q r s : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 0 < r) (hs : 0 < s)
    (hpq : p.Coprime q) (h : minimalCentralCharge p q = minimalCentralCharge r s)
    (hlevel : (r-1)*(s-1) ≤ (p-1)*(q-1)) :
    (r=p ∧ s=q) ∨ (r=q ∧ s=p) := by
  rcases charge_eq_scales (by omega) (by omega) hr hs hpq h with h | h
  · obtain ⟨k, hk, rfl, rfl⟩ := h
    have hk1 : k = 1 := by
      by_contra hn
      exact (not_lt_of_ge hlevel) (scaled_level_strict hp hq (by omega))
    simp [hk1]
  · obtain ⟨k, hk, rfl, rfl⟩ := h
    have hk1 : k = 1 := by
      by_contra hn
      have hh := scaled_level_strict hp hq (show 1 < k by omega)
      rw [Nat.mul_comm (k*p-1) (k*q-1)] at hh
      exact (not_lt_of_ge hlevel) hh
    simp [hk1]

end VOA.VirMinimalArithmetic
