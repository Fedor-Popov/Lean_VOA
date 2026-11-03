/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalChargeArithmetic

/-!
# The first weight-zero and weight-one Kac labels

For primitive minimal-model parameters, the arithmetic Kac weight has only
two possible zero labels up to the first vacuum singular level: the universal
level-one relation and the minimal-model label. Weight-one labels occur
strictly later. These are unconditional number-theoretic statements, not a
proof that the actual Verma determinants have Kac's factorization.
-/
namespace VOA.VirMinimalArithmetic

/-- The rational highest-weight expression at minimal-model charge. The
orientation is fixed so the first vacuum label is (q - 1,p - 1); its product is
independent of this ordering convention. -/
def minimalKacWeight (p q r s : ℕ) : ℚ :=
  (((p : ℚ) * r-q * s)^2-((p : ℚ)-q)^2)/(4 * p * q)

/-- Vanishing of the rational Kac weight is precisely either of two linear
Diophantine equations. This also avoids truncated natural subtraction. -/
theorem minimalKacWeight_zero_iff {p q r s : ℕ} (hp : 0 < p) (hq : 0 < q) :
    minimalKacWeight p q r s = 0 ↔
      p * r + q = q * s + p ∨ p * r + p = q * s + q := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  unfold minimalKacWeight
  rw [div_eq_zero_iff]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, hp0, hq0, or_false]
  constructor
  · intro h
    have he : ((p : ℚ) * r-q * s-((p : ℚ)-q)) *
        ((p : ℚ) * r-q * s + ((p : ℚ)-q)) = 0 := by nlinarith
    rcases mul_eq_zero.mp he with he | he
    · left
      exact_mod_cast (show (p : ℚ) * r + q = q * s + p by linarith)
    · right
      exact_mod_cast (show (p : ℚ) * r + p = q * s + q by linarith)
  · rintro (he | he)
    · have he' : (p : ℚ) * r + q = q * s + p := by exact_mod_cast he
      nlinarith
    · have he' : (p : ℚ) * r + p = q * s + q := by exact_mod_cast he
      nlinarith

/-- Highest weight one has the analogous two linear equations, with
p + q in place of p-q. These describe candidate Verma factors only. -/
theorem minimalKacWeight_one_iff {p q r s : ℕ} (hp : 0 < p) (hq : 0 < q) :
    minimalKacWeight p q r s = 1 ↔
      p * r = q * s + p + q ∨ p * r + p + q = q * s := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  unfold minimalKacWeight
  rw [div_eq_one_iff_eq (by positivity : (4 : ℚ) * p * q ≠ 0)]
  constructor
  · intro h
    have he : ((p : ℚ) * r-q * s-((p : ℚ) + q)) *
        ((p : ℚ) * r-q * s + ((p : ℚ) + q)) = 0 := by nlinarith
    rcases mul_eq_zero.mp he with he | he
    · left
      exact_mod_cast (show (p : ℚ) * r = q * s + p + q by linarith)
    · right
      exact_mod_cast (show (p : ℚ) * r + p + q = q * s by linarith)
  · rintro (he | he)
    · have he' : (p : ℚ) * r = q * s + p + q := by exact_mod_cast he
      nlinarith
    · have he' : (p : ℚ) * r + p + q = q * s := by exact_mod_cast he
      nlinarith

/-- Among positive labels at or below the first vacuum singular level,
the zero-weight Kac equation allows only the level-one vacuum relation or
exactly the minimal-model label. Coprimality fixes the integral scale. -/
theorem minimalKacWeight_zero_first_labels {p q r s : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 0 < r) (hs : 0 < s)
    (hcop : p.Coprime q) (hzero : minimalKacWeight p q r s = 0)
    (hle : r * s ≤ (p - 1) * (q - 1)) :
    (r = 1 ∧ s = 1) ∨ (r = q - 1 ∧ s = p - 1) := by
  rcases (minimalKacWeight_zero_iff (by omega) (by omega)).mp hzero with he | he
  · by_cases hr1 : r = 1
    · left
      subst r
      constructor
      · rfl
      · nlinarith
    · have hr' : 0 < r - 1 := by omega
      have hcross : q * (s - 1) = p * (r - 1) := by
        have hrsub : r - 1 + 1 = r := by omega
        have hssub : s - 1 + 1 = s := by omega
        nlinarith
      obtain ⟨k,hk,hkr,hks⟩ := exists_scale_of_cross (by omega : 0 < q) hr'
        hcop.symm hcross
      have hrl : q + 1 ≤ r := by
        have hrsub : r - 1 + 1 = r := by omega
        nlinarith
      have hsl : p + 1 ≤ s := by
        have hssub : s - 1 + 1 = s := by omega
        nlinarith
      have hm := Nat.mul_le_mul hrl hsl
      have hp' : p - 1 + 1 = p := by omega
      have hq' : q - 1 + 1 = q := by omega
      nlinarith
  · have hcross : q * (s + 1) = p * (r + 1) := by nlinarith
    obtain ⟨k,hk,hkr,hks⟩ := exists_scale_of_cross (by omega : 0 < q)
      (by omega : 0 < r + 1) hcop.symm hcross
    have hk1 : k = 1 := by
      by_contra hn
      have hstrict := scaled_level_strict hp hq (by omega : 1 < k)
      have hr' : r = k * q - 1 := by omega
      have hs' : s = k * p - 1 := by omega
      rw [hr',hs',Nat.mul_comm] at hle
      omega
    right
    simp only [hk1,one_mul] at hkr hks
    omega

/-- Every positive weight-one Kac label has level at least
(p + 1)(q - 1), when p > q. Both signs are handled and the smaller of their
possible first products is selected explicitly. -/
theorem minimalKacWeight_one_level_bound {p q r s : ℕ}
    (hq : 2 ≤ q) (hpq : q < p) (hr : 0 < r) (hs : 0 < s)
    (hcop : p.Coprime q) (hone : minimalKacWeight p q r s = 1) :
    (p + 1) * (q - 1) ≤ r * s := by
  rcases (minimalKacWeight_one_iff (by omega) (by omega)).mp hone with he | he
  · have hr' : 0 < r - 1 := by
      have : p < p * r := by nlinarith
      by_contra hn
      have : r = 1 := by omega
      simp [this] at *
    have hcross : q * (s + 1) = p * (r - 1) := by
      have hrsub : r - 1 + 1 = r := by omega
      nlinarith
    obtain ⟨k,hk,hkr,hks⟩ := exists_scale_of_cross (by omega : 0 < q) hr'
      hcop.symm hcross
    have hrl : q + 1 ≤ r := by
      have hrsub : r - 1 + 1 = r := by omega
      nlinarith
    have hsl : p - 1 ≤ s := by
      have hp' : p - 1 + 1 = p := by omega
      nlinarith
    have hm := Nat.mul_le_mul hrl hsl
    have hp' : p - 1 + 1 = p := by omega
    have hq' : q - 1 + 1 = q := by omega
    nlinarith
  · have hs' : 0 < s - 1 := by
      have : q < q * s := by nlinarith
      by_contra hn
      have : s = 1 := by omega
      simp [this] at *
    have hcross : q * (s - 1) = p * (r + 1) := by
      have hssub : s - 1 + 1 = s := by omega
      nlinarith
    obtain ⟨k,hk,hkr,hks⟩ := exists_scale_of_cross (by omega : 0 < q)
      (by omega : 0 < r + 1) hcop.symm hcross
    have hrl : q - 1 ≤ r := by
      have hq' : q - 1 + 1 = q := by omega
      nlinarith
    have hsl : p + 1 ≤ s := by
      have hssub : s - 1 + 1 = s := by omega
      nlinarith
    simpa only [Nat.mul_comm] using Nat.mul_le_mul hrl hsl

/-- The weight-one Verma factors cannot occur at or before the first vacuum
singular absolute weight. Applying this arithmetic fact to an actual Verma
determinant still requires a proved Kac factorization. -/
theorem minimalKacWeight_one_above_vacuum_level {p q r s : ℕ}
    (hq : 2 ≤ q) (hpq : q < p) (hr : 0 < r) (hs : 0 < s)
    (hcop : p.Coprime q) (hone : minimalKacWeight p q r s = 1) :
    (p - 1) * (q - 1) < 1 + r * s := by
  have h := minimalKacWeight_one_level_bound hq hpq hr hs hcop hone
  have hp' : p - 1 + 1 = p := by omega
  have hq' : q - 1 + 1 = q := by omega
  nlinarith


/-- The first minimal-model candidate actually satisfies the zero-weight
Kac equation. This is a rational identity, not singular-vector existence. -/
theorem minimalKacWeight_minimal_label {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    minimalKacWeight p q (q - 1) (p - 1) = 0 := by
  apply (minimalKacWeight_zero_iff (by omega) (by omega)).mpr
  right
  have hp' : p - 1 + 1 = p := by omega
  have hq' : q - 1 + 1 = q := by omega
  nlinarith

/-- The lower bound for the first weight-one Kac label is attained. It is
therefore the exact arithmetic threshold.  Actual Verma singular states at these labels are
supplied by `VirasoroScreening.screening_nonreal_kac_singular`. -/
theorem minimalKacWeight_first_one_label {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    minimalKacWeight p q (q - 1) (p + 1) = 1 := by
  apply (minimalKacWeight_one_iff (by omega) (by omega)).mpr
  right
  have hq' : q - 1 + 1 = q := by omega
  nlinarith

/-- Strictly before the first vacuum singular weight, the only positive
zero-weight Kac label is (1,1), the translation relation already removed
by the actual Verma-to-vacuum exact sequence. -/
theorem minimalKacWeight_zero_before_first {p q r s : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 0 < r) (hs : 0 < s)
    (hcop : p.Coprime q) (hzero : minimalKacWeight p q r s = 0)
    (hlt : r * s < (p - 1) * (q - 1)) : r = 1 ∧ s = 1 := by
  rcases minimalKacWeight_zero_first_labels hp hq hr hs hcop hzero hlt.le with h | h
  · exact h
  · obtain ⟨rfl,rfl⟩ := h
    rw [Nat.mul_comm] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)

end VOA.VirMinimalArithmetic
