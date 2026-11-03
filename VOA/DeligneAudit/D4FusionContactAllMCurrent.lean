import VOA.DeligneAudit.D4FusionContactAllMSource
import VOA.DeligneAudit.D4FusionContactPolynomialDerivations

/-!
# Grouped current coefficients in the actual contact PBW annihilator

The finite variables have their actual current modes.  Coefficient sums
are transported as whole homogeneous sums into the restricted graded
cyclic span; no ambient-quotient commutativity or source FD is used.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllM

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V) (w : V)

theorem power_coefficient_symbol (a : Fin 9) (r s : ℕ) :
    (((PowerSeries.coeff s (Garland.Fs (grOp R w a) ^ r)) (grGenerator R w)) :
      AmbientGr R w) = symbol R w r
        ((PowerSeries.coeff s (Garland.Fs (R.op (radIndex a)) ^ r)) w) := by
  induction r generalizing s with
  | zero =>
      simp only [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · rfl
      · simp
  | succ r ih =>
      simp only [pow_succ', PowerSeries.coeff_mul, Garland.Fs, PowerSeries.coeff_mk,
        LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply, Submodule.coe_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x hx
      change ambientOp R w a x.1
          (((PowerSeries.coeff x.2 (Garland.Fs (grOp R w a) ^ r))
            (grGenerator R w)) : AmbientGr R w) = _
      rw [ih, ambientOp_symbol]
      rfl

theorem power_coefficient_zero (a : Fin 9) (r s : ℕ)
    (hzero : (PowerSeries.coeff s (Garland.Fs (R.op (radIndex a)) ^ r)) w = 0) :
    (PowerSeries.coeff s (Garland.Fs (grOp R w a) ^ r)) (grGenerator R w) = 0 := by
  apply Subtype.ext
  rw [power_coefficient_symbol, hzero, map_zero]
  rfl

/-- The finite forward current, with direct current-mode variables. -/
def current (m : ℕ) (a : Fin 9) : PowerSeries (MvPolynomial (Vars m) ℂ) :=
  PowerSeries.mk (modeX m a)

theorem map_current {m : ℕ}
    (hhigh : ∀ i q, m ≤ q → R.op (radIndex i) q w = 0) (a : Fin 9) :
    PowerSeries.map (polyAlg R w (modeLetter m)).toRingHom (current m a) =
      Garland.Fs (grOp R w a) := by
  apply PowerSeries.ext
  intro q
  simp only [current, Garland.Fs, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact polyAlg_modeX hhigh a q

theorem current_coefficient_eval {m : ℕ}
    (hhigh : ∀ i q, m ≤ q → R.op (radIndex i) q w = 0) (a : Fin 9) (r s : ℕ) :
    polyEval R w (modeLetter m) (PowerSeries.coeff s (current m a ^ r)) =
      (PowerSeries.coeff s (Garland.Fs (grOp R w a) ^ r)) (grGenerator R w) := by
  change ((polyAlg R w (modeLetter m)).toRingHom
    (PowerSeries.coeff s (current m a ^ r))) (grGenerator R w) = _
  rw [← PowerSeries.coeff_map, map_pow, map_current R w hhigh]

variable {R w} {m : ℕ}
variable {R : CurrentModule D4sector.f V}

theorem source_simple_coefficient_mem_ann (hm : 1 ≤ m)
    (h : LocalWeylRelG D4sector R w m) (r s : ℕ) (hr : 1 ≤ r) (hs : m < r + s) :
    PowerSeries.coeff s (current m 0 ^ r) ∈ annIdeal R w (modeLetter m) := by
  change polyEval R w (modeLetter m) _ = 0
  rw [current_coefficient_eval R w
    (fun i q hq => localWeyl_high_kills hm h (radIndex i) q hq)]
  apply power_coefficient_zero
  exact D4FusionContact.AllM.simple_coefficient h r s hr hs

theorem source_center_coefficient_mem_ann (hm : 1 ≤ m)
    (h : LocalWeylRelG D4sector R w m) (r s : ℕ) (hr : 1 ≤ r) (hs : 2 * m < r + s) :
    PowerSeries.coeff s (current m 8 ^ r) ∈ annIdeal R w (modeLetter m) := by
  change polyEval R w (modeLetter m) _ = 0
  rw [current_coefficient_eval R w
    (fun i q hq => localWeyl_high_kills hm h (radIndex i) q hq)]
  apply power_coefficient_zero
  exact D4FusionContact.AllM.center_coefficient h r s hr hs

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllM

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.power_coefficient_symbol
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.source_simple_coefficient_mem_ann
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.source_center_coefficient_mem_ann
