/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalChargeArithmetic

/-!
# First affine real-root resonance at admissible sl₂ levels

At k+2=p/q, the real-root equations for mδ−α and mδ+α are
mp=q(r+1) and mp+q=qr respectively. Coprimality classifies their
positive solutions. The first possible energy is q(p−1), uniquely
from m=q, r=p−1 in the minus family. This proves arithmetic only,
not an affine determinant formula or existence of a singular state.
-/
namespace VOA.AffineSl2AdmissibleArithmetic

/-- Every positive minus-root resonance is a positive integral multiple
of the admissible denominator: m=lq and r+1=lp. -/
theorem minus_resonance_scale {p q m r : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hcop : p.Coprime q) (he : m*p = q*(r+1)) :
    ∃ l : ℕ, 0 < l ∧ m = l*q ∧ r+1 = l*p := by
  exact VirMinimalArithmetic.exists_scale_of_cross hq hm hcop.symm (by simpa [Nat.mul_comm] using he.symm)

/-- Increasing the scale above one strictly raises the minus-root energy
above q(p−1). All subtraction here is justified by p≥2. -/
theorem minus_scaled_energy_strict {p q l : ℕ} (hp : 2 ≤ p) (hq : 0 < q)
    (hl : 1 < l) : q*(p-1) < (l*q)*(l*p-1) := by
  have hq' : q < l*q := by nlinarith
  have hp' : p-1 ≤ l*p-1 := Nat.sub_le_sub_right (by nlinarith) 1
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hq' (by omega))
    (Nat.mul_le_mul_left _ hp')

/-- At or below the first candidate energy, the only minus-root resonance
has precisely m=q and r=p−1. No representation-theoretic input is used. -/
theorem first_minus_resonance_unique {p q m r : ℕ} (hp : 2 ≤ p) (hq : 0 < q)
    (hm : 0 < m) (hcop : p.Coprime q) (he : m*p = q*(r+1))
    (hbound : m*r ≤ q*(p-1)) : m=q ∧ r=p-1 := by
  obtain ⟨l, hl, hm', hr⟩ := minus_resonance_scale hq hm hcop he
  have hr' : r = l*p-1 := by omega
  have hle : l ≤ 1 := by
    by_contra hn
    have hs := minus_scaled_energy_strict hp hq (show 1 < l by omega)
    rw [hm', hr'] at hbound
    omega
  have : l=1 := by omega
  subst l
  simpa using And.intro hm' hr'

/-- Every plus-root resonance has m=lq and r=lp+1. In particular its
energy exceeds the first minus-root candidate. -/
theorem plus_resonance_scale {p q m r : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hm : 0 < m) (hcop : p.Coprime q) (he : m*p+q=q*r) :
    ∃ l : ℕ, 0 < l ∧ m=l*q ∧ r=l*p+1 := by
  have hr : 1 ≤ r := by nlinarith
  have he' : m*p=q*(r-1) := by
    have := Nat.sub_add_cancel hr
    nlinarith
  obtain ⟨l, hl, hm', hr'⟩ :=
    VirMinimalArithmetic.exists_scale_of_cross hq hm hcop.symm (by simpa [Nat.mul_comm] using he'.symm)
  exact ⟨l, hl, hm', by omega⟩

/-- A plus-root resonance cannot occur at or below q(p−1). This rules
out the other real-root family at the first candidate energy. -/
theorem plus_resonance_energy_gt {p q m r : ℕ} (hp : 2 ≤ p) (hq : 0 < q)
    (hm : 0 < m) (hcop : p.Coprime q) (he : m*p+q=q*r) :
    q*(p-1) < m*r := by
  obtain ⟨l, hl, hm', hr⟩ := plus_resonance_scale (by omega) hq hm hcop he
  have hmq : q ≤ m := by nlinarith
  have hpr : p-1 < r := by
    have hpl : p ≤ l*p := by nlinarith
    omega
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hpr hq)
    (Nat.mul_le_mul_right r hmq)

end VOA.AffineSl2AdmissibleArithmetic
