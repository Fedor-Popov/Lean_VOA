import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic

/-! Uniform static triangle relations from an actual differential ideal.
The two differentiated nil-power relations cancel their common term.
No dimension or presentation premise is used. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem cancel_nat_factor (I : Ideal A) (n : ℕ) (hn : n ≠ 0) {p : A}
    (h : (n : A) * p ∈ I) : p ∈ I := by
  have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hs : (n : ℂ) • p ∈ I := by
    simpa only [Algebra.smul_def, map_natCast] using h
  exact (Submodule.smul_mem_iff (I.restrictScalars ℂ) hc).mp hs

theorem deriv_pow_succ (D : Derivation ℂ A A) (u : A) (k : ℕ) :
    D (u ^ (k + 1)) = ((k + 1 : ℕ) : A) * u ^ k * D u := by
  rw [Derivation.leibniz_pow, show k + 1 - 1 = k by omega]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem triangle_identity (D₁ D₂ D₃ : Derivation ℂ A A) (u x y z t : A)
    (h₁ : D₁ u = x) (h₂ : D₂ u = y) (h₃ : D₃ u = z) (h₂₁ : D₂ x = t) (k : ℕ) :
    z * D₂ (D₁ (u ^ (k + 2))) - t * D₃ (u ^ (k + 2)) =
      (((k + 2) * (k + 1) : ℕ) : A) * (u ^ k * x * y * z) := by
  have hfirst : D₁ (u ^ (k + 2)) = ((k + 2 : ℕ) : A) * u ^ (k + 1) * x := by
    rw [deriv_pow_succ, h₁]
  rw [hfirst]
  simp only [Derivation.leibniz, Derivation.map_natCast, deriv_pow_succ,
    h₂, h₃, h₂₁, smul_eq_mul]
  simp only [pow_succ]
  push_cast
  ring

theorem triangle_mem (I : Ideal A) (D₁ D₂ D₃ : Derivation ℂ A A)
    (hI₁ : ∀ p ∈ I, D₁ p ∈ I) (hI₂ : ∀ p ∈ I, D₂ p ∈ I)
    (hI₃ : ∀ p ∈ I, D₃ p ∈ I) (u x y z t : A)
    (h₁ : D₁ u = x) (h₂ : D₂ u = y) (h₃ : D₃ u = z) (h₂₁ : D₂ x = t)
    (k : ℕ) (hpow : u ^ (k + 2) ∈ I) : u ^ k * x * y * z ∈ I := by
  have hrow : z * D₂ (D₁ (u ^ (k + 2))) - t * D₃ (u ^ (k + 2)) ∈ I :=
    I.sub_mem (I.mul_mem_left _ (hI₂ _ (hI₁ _ hpow)))
      (I.mul_mem_left _ (hI₃ _ hpow))
  rw [triangle_identity D₁ D₂ D₃ u x y z t h₁ h₂ h₃ h₂₁ k] at hrow
  exact cancel_nat_factor I _ (by positivity) hrow

/-- One Leibniz step transfers a factor of u to its derivative v. -/
theorem power_transfer_step (I : Ideal A) (D : Derivation ℂ A A)
    (hI : ∀ p ∈ I, D p ∈ I) (u v : A) (hu : D u = v) (hv : D v = 0)
    (k n : ℕ) (h : u ^ (k + 1) * v ^ n ∈ I) : u ^ k * v ^ (n + 1) ∈ I := by
  have hd := hI _ h
  have he : D (u ^ (k + 1) * v ^ n) = ((k + 1 : ℕ) : A) * (u ^ k * v ^ (n + 1)) := by
    rw [Derivation.leibniz, deriv_pow_succ, hu]
    have hz : D (v ^ n) = 0 := by simp only [Derivation.leibniz_pow, hv, smul_zero]
    simp only [hz, smul_eq_mul, pow_succ]
    ring
  rw [he] at hd
  exact cancel_nat_factor I (k + 1) (by omega) hd

/-- Exact nil-power transfer along a two-step derivation string.
This avoids assuming an opposite-root source relation. -/
theorem power_transfer (I : Ideal A) (D : Derivation ℂ A A)
    (hI : ∀ p ∈ I, D p ∈ I) (u v : A) (hu : D u = v) (hv : D v = 0)
    (n : ℕ) (h : u ^ n ∈ I) : v ^ n ∈ I := by
  have hall : ∀ k a : ℕ, u ^ k * v ^ a ∈ I → v ^ (k + a) ∈ I := by
    intro k
    induction k with
    | zero => intro a ha; simpa only [pow_zero, one_mul, Nat.zero_add] using ha
    | succ k ih =>
        intro a ha
        have hs := power_transfer_step I D hI u v hu hv k a ha
        have hh := ih (a + 1) hs
        simpa only [Nat.succ_add, Nat.add_succ] using hh
  simpa only [Nat.add_zero] using hall n 0 (by simpa only [pow_zero, mul_one] using h)

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.triangle_mem
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.power_transfer
