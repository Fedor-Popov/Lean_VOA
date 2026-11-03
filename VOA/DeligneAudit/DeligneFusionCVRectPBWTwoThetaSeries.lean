import VOA.DeligneAudit.DeligneFusionCVRectPBWTwoThetaPolarization
import VOA.DeligneAudit.DeligneFusionCVRectPBWBoundary

/-!
# Removing a finite low prefix from a two-theta coefficient

The high/high term is supplied by polarization. A low/full term is
killed by actual one-theta coefficients; the low/low term is killed by
actual simple-root coefficients. The reconstruction identity then
recovers the full two-theta coefficient, without a PBW ideal premise.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWTwoTheta

open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.Garland
open VOA.DeligneAudit.A2.CVPolarization
open VOA.DeligneAudit.A2.CVRectPolynomial
open VOA.DeligneAudit.A2.CVRectPBWBoundary

noncomputable section

theorem square_tail_reconstruction {A : Type*} [Ring A] {T L H : A}
    (hT : T = L + H) (hLT : L * T = T * L) :
    T ^ 2 = H ^ 2 + 2 • (L * T) - L ^ 2 := by
  have hH : T - L = H := by rw [hT]; abel
  calc
    T ^ 2 = (T - L) ^ 2 + L * T + T * L - L ^ 2 := by noncomm_ring
    _ = H ^ 2 + 2 • (L * T) - L ^ 2 := by rw [hH, ← hLT, two_nsmul]; abel

theorem shifted_square_mul {A : Type*} [Semiring A]
    (S T : PowerSeries A) (N : ℕ) :
    (PowerSeries.X ^ N * S) ^ 2 * T = PowerSeries.X ^ (2 * N) * (S ^ 2 * T) := by
  have hc : Commute (PowerSeries.X ^ N) S := PowerSeries.X_pow_mul
  rw [hc.mul_pow, ← pow_mul, show N * 2 = 2 * N by omega, mul_assoc]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem prefix_commutes (Θ : ℕ → Module.End ℂ V)
    (hΘ : ∀ i j, Θ i * Θ j = Θ j * Θ i) (N : ℕ) :
    (finiteCurrent N Θ : PowerSeries (Module.End ℂ V)) * Fs Θ =
      Fs Θ * (finiteCurrent N Θ : PowerSeries (Module.End ℂ V)) := by
  have hp : (finiteCurrent N Θ : PowerSeries (Module.End ℂ V)) =
      Fs (fun i => if i < N then Θ i else 0) := by
    apply PowerSeries.ext
    intro i
    rw [Polynomial.coeff_coe]
    simp only [Fs, PowerSeries.coeff_mk]
    by_cases hi : i < N
    · rw [if_pos hi, finiteCurrent_coeff_lt N Θ i hi]
    · rw [if_neg hi, finiteCurrent_coeff_ge N Θ i (by omega)]
  rw [hp]
  apply current_series_commute
  intro i j
  split_ifs
  · exact hΘ i j
  · simp only [zero_mul, mul_zero]

theorem prefix_times_mixed_zero (Θ F : ℕ → Module.End ℂ V) (w : V) (N r s : ℕ)
    (hone : ∀ i, i < N → i ≤ s → mixedCoeff Θ F 1 r (s - i) w = 0) :
    PowerSeries.coeff s
      ((finiteCurrent N Θ : PowerSeries (Module.End ℂ V)) * (Fs Θ * Fs F ^ r)) w = 0 := by
  rw [PowerSeries.coeff_mul, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hsum : i + j = s := Finset.mem_antidiagonal.mp hij
  rw [Module.End.mul_apply, Polynomial.coeff_coe]
  by_cases hi : i < N
  · rw [finiteCurrent_coeff_lt N Θ i hi]
    have hz : PowerSeries.coeff j (Fs Θ * Fs F ^ r) w = 0 := by
      simpa only [mixedCoeff, pow_one, show s - i = j by omega] using
        hone i hi (by omega)
    rw [hz, map_zero]
  · rw [finiteCurrent_coeff_ge N Θ i (by omega), LinearMap.zero_apply]

theorem prefix_square_times_power_zero (Θ F : ℕ → Module.End ℂ V)
    (w : V) (N r s : ℕ)
    (hsimple : ∀ i j, i < N → j < N → i + j ≤ s → Q F r (s - i - j) w = 0) :
    (PowerSeries.coeff s
      ((finiteCurrent N Θ : PowerSeries (Module.End ℂ V)) ^ 2 * Fs F ^ r) :
        Module.End ℂ V) w = 0 := by
  rw [pow_two, mul_assoc, PowerSeries.coeff_mul, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hsum : i + j = s := Finset.mem_antidiagonal.mp hij
  rw [Module.End.mul_apply, Polynomial.coeff_coe]
  by_cases hi : i < N
  · rw [finiteCurrent_coeff_lt N Θ i hi]
    have hz : PowerSeries.coeff j
        ((finiteCurrent N Θ : PowerSeries (Module.End ℂ V)) * Fs F ^ r) w = 0 := by
      rw [PowerSeries.coeff_mul, LinearMap.sum_apply]
      apply Finset.sum_eq_zero
      rintro ⟨k, l⟩ hkl
      have hsum' : k + l = j := Finset.mem_antidiagonal.mp hkl
      rw [Module.End.mul_apply, Polynomial.coeff_coe]
      by_cases hk : k < N
      · rw [finiteCurrent_coeff_lt N Θ k hk]
        have hF : Q F r l w = 0 := by
          simpa only [show s - i - k = l by omega] using hsimple i k hi hk (by omega)
        change Θ k (Q F r l w) = 0
        rw [hF, map_zero]
      · rw [finiteCurrent_coeff_ge N Θ k (by omega), LinearMap.zero_apply]
    rw [hz, map_zero]
  · rw [finiteCurrent_coeff_ge N Θ i (by omega), LinearMap.zero_apply]

/-- The exact finite-prefix square reconstruction. Every lower term
is controlled by a one-theta or simple-root source coefficient. -/
theorem mixedCoeff_two_zero_of_tail_and_lower
    (Θ F : ℕ → Module.End ℂ V) (w : V) (N r s : ℕ)
    (hΘ : ∀ i j, Θ i * Θ j = Θ j * Θ i)
    (htail : 2 * N ≤ s → mixedCoeff (fun k => Θ (N + k)) F 2 r (s - 2 * N) w = 0)
    (hone : ∀ i, i < N → i ≤ s → mixedCoeff Θ F 1 r (s - i) w = 0)
    (hsimple : ∀ i j, i < N → j < N → i + j ≤ s → Q F r (s - i - j) w = 0) :
    mixedCoeff Θ F 2 r s w = 0 := by
  let L : PowerSeries (Module.End ℂ V) := finiteCurrent N Θ
  let H : PowerSeries (Module.End ℂ V) := PowerSeries.X ^ N * Fs (fun k => Θ (N + k))
  have hsplit : Fs Θ = L + H := series_prefix_tail Θ N
  have hcomm : L * Fs Θ = Fs Θ * L := prefix_commutes Θ hΘ N
  have hhigh : (PowerSeries.coeff s (H ^ 2 * Fs F ^ r) : Module.End ℂ V) w = 0 := by
    dsimp only [H]
    rw [shifted_square_mul, PowerSeries.coeff_X_pow_mul']
    split_ifs with hs
    · exact htail hs
    · exact LinearMap.zero_apply w
  have hlowone : PowerSeries.coeff s (L * Fs Θ * Fs F ^ r) w = 0 := by
    rw [mul_assoc]
    exact prefix_times_mixed_zero Θ F w N r s hone
  have hlowsq : (PowerSeries.coeff s (L ^ 2 * Fs F ^ r) : Module.End ℂ V) w = 0 :=
    prefix_square_times_power_zero Θ F w N r s hsimple
  have hid : Fs Θ ^ 2 * Fs F ^ r = H ^ 2 * Fs F ^ r +
      2 • (L * Fs Θ * Fs F ^ r) - L ^ 2 * Fs F ^ r := by
    rw [square_tail_reconstruction hsplit hcomm, sub_mul, add_mul, smul_mul_assoc]
  have he := congrArg (fun P : PowerSeries (Module.End ℂ V) => PowerSeries.coeff s P w) hid
  simp only [map_sub, map_add, map_nsmul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, hhigh, hlowone, hlowsq, smul_zero, add_zero, sub_zero] at he
  exact he

end

end VOA.DeligneAudit.A2.CVRectPBWTwoTheta

#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.square_tail_reconstruction
#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.mixedCoeff_two_zero_of_tail_and_lower
