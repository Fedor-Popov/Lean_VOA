import VOA.Moonshine.MoonshineCNOscillators
import VOA.Examples.HeisenbergNVertex
import Mathlib.Data.Fin.Rev

/-! # The isotropic polynomial Fock model

We reuse `FockN 2 = MvPolynomial (ℕ × Fin 2) ℂ`; `(j,0)` is `a_(j+1)`
and `(j,1)` is `b_(j+1)`. This is the blueprint's variable set with the
two product factors reversed. Positive modes differentiate the opposite
family, whereas negative modes multiply the named family.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open HeisenbergN MvPolynomial

abbrev hypFock := FockN 2

/-- One isotropic oscillator family with arbitrary scalar zero mode. -/
def hypOscillator (a : Fin 2) (q : ℂ) (n : ℤ) : Module.End ℂ hypFock :=
  if n < 0 then oscN 2 1 a n
  else if 0 < n then oscN 2 1 a.rev n
  else q • LinearMap.id

abbrev hypOscA (κ : ℂ) := hypOscillator 0 κ
abbrev hypOscB (ell : ℂ) := hypOscillator 1 ell

theorem hypOscillator_neg (a : Fin 2) (q : ℂ) (n : ℤ) (hn : n < 0) :
    hypOscillator a q n = oscN 2 1 a n := by simp [hypOscillator, hn]

theorem hypOscillator_pos (a : Fin 2) (q : ℂ) (n : ℤ) (hn : 0 < n) :
    hypOscillator a q n = oscN 2 1 a.rev n := by
  simp [hypOscillator, hn, show ¬n < 0 by omega]

@[simp] theorem hypOscillator_zero (a : Fin 2) (q : ℂ) :
    hypOscillator a q 0 = q • LinearMap.id := by simp [hypOscillator]

theorem hypOscillator_negative_apply (a : Fin 2) (q : ℂ) (j : ℕ) (p : hypFock) :
    hypOscillator a q (-(j + 1 : ℤ)) p = X (j, a) * p := by
  rw [hypOscillator_neg _ _ _ (by omega), oscN_apply_neg _ _ _ (by omega)]
  rw [show (-(-(j + 1 : ℤ)) - 1).toNat = j from by omega]

theorem hypOscillator_positive_apply (a : Fin 2) (q : ℂ) (j : ℕ) (p : hypFock) :
    hypOscillator a q (j + 1 : ℤ) p = (j + 1 : ℂ) • pderiv (j, a.rev) p := by
  rw [hypOscillator_pos _ _ _ (by omega), oscN_apply_pos _ _ _ (by omega)]
  simp

/-- The full hyperbolic Heisenberg relation, including both scalar zero modes. -/
theorem hypOscillator_comm (a b : Fin 2) (q r : ℂ) (m n : ℤ) :
    hypOscillator a q m * hypOscillator b r n -
      hypOscillator b r n * hypOscillator a q m =
    (if a = b.rev ∧ m + n = 0 then (m : ℂ) else 0) • LinearMap.id := by
  by_cases hm : m = 0
  · subst m
    ext p
    simp [Module.End.mul_apply]
  by_cases hn : n = 0
  · subst n
    ext p
    simp [Module.End.mul_apply, hm]
  rcases lt_or_gt_of_ne hm with hm | hm
  · rcases lt_or_gt_of_ne hn with hn | hn
    · rw [hypOscillator_neg _ _ _ hm, hypOscillator_neg _ _ _ hn, oscN_comm]
      simp [show m + n ≠ 0 by omega]
    · rw [hypOscillator_neg _ _ _ hm, hypOscillator_pos _ _ _ hn, oscN_comm]
      simp
  · rcases lt_or_gt_of_ne hn with hn | hn
    · rw [hypOscillator_pos _ _ _ hm, hypOscillator_neg _ _ _ hn, oscN_comm]
      simp [Fin.rev_eq_iff]
    · rw [hypOscillator_pos _ _ _ hm, hypOscillator_pos _ _ _ hn, oscN_comm]
      simp [show m + n ≠ 0 by omega]

theorem hypOscA_comm (κ : ℂ) (m n : ℤ) :
    hypOscA κ m * hypOscA κ n - hypOscA κ n * hypOscA κ m = 0 := by
  simpa using hypOscillator_comm 0 0 κ κ m n

theorem hypOscB_comm (ell : ℂ) (m n : ℤ) :
    hypOscB ell m * hypOscB ell n - hypOscB ell n * hypOscB ell m = 0 := by
  simpa using hypOscillator_comm 1 1 ell ell m n

theorem hypOscAB_comm (κ ell : ℂ) (m n : ℤ) :
    hypOscA κ m * hypOscB ell n - hypOscB ell n * hypOscA κ m =
      (if m + n = 0 then (m : ℂ) else 0) • LinearMap.id := by
  simpa using hypOscillator_comm 0 1 κ ell m n

/-- Integer level grading, independent of momentum. -/
def hypLevel (N : ℤ) : Submodule ℂ hypFock := gradingZN 2 N

theorem hypLevel_isInternal : DirectSum.IsInternal hypLevel := gradingZN_isInternal 2

theorem hypLevel_finiteDimensional (N : ℤ) : FiniteDimensional ℂ (hypLevel N) :=
  gradingZN_finrank 2 N

theorem hypLevel_negative (N : ℤ) (hN : N < 0) : hypLevel N = ⊥ := gradingZN_of_neg hN

theorem hypLevel_zero : hypLevel 0 = ℂ ∙ (1 : hypFock) := gradingZN_zero_eq_span_vacuum 2

theorem hypOscillator_mem_level (a : Fin 2) (q : ℂ) (n N : ℤ) (p : hypFock)
    (hp : p ∈ hypLevel N) : hypOscillator a q n p ∈ hypLevel (N - n) := by
  by_cases hN : 0 ≤ N
  · have hp' : p ∈ gradingWN 2 N.toNat := by
      simpa only [hypLevel, gradingZN_of_nonneg hN] using hp
    have hos (b : Fin 2) : oscN 2 1 b n p ∈ hypLevel (N - n) := by
      simpa only [Int.toNat_of_nonneg hN] using oscN_mem_gradingZN 2 1 b n hp'
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · rw [hypOscillator_neg _ _ _ hn]; exact hos a
    · simpa using (hypLevel N).smul_mem q hp
    · rw [hypOscillator_pos _ _ _ hn]; exact hos a.rev
  · have hp0 : p = 0 := by
      rw [hypLevel_negative N (by omega)] at hp
      exact hp
    rw [hp0, map_zero]
    exact Submodule.zero_mem _

theorem hypOscillator_vacuum (a : Fin 2) (q : ℂ) (n : ℤ) (hn : 0 < n) :
    hypOscillator a q n (1 : hypFock) = 0 := by
  rw [hypOscillator_pos _ _ _ hn]
  exact oscN_vacuum 2 1 a.rev n (by omega)

end VOA.Moonshine.ConwayNorton
