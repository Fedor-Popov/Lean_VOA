import VOA.DeligneAudit.DeligneFusionCVRectFilteredReflection
import VOA.DeligneAudit.DeligneFusionCVRectFilteredCoeff
import VOA.DeligneAudit.DeligneFusionCVRectStarBase
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Canonical reversed STAR coefficients evaluated in the actual PBW module

STAR variable i acts by source current mode i. The exponent reversal already
belongs to the canonical polynomial current. Fixed-degree polynomial
reflection identifies a coefficient at j with the full graded current
coefficient at its complementary index, using the actual high-mode cutoff.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVRectStarBase

noncomputable section

/- The generic finite-current construction is kept here, separate from the
old one-orientation current-module imports. These are the same prescribed
degree identities, over an arbitrary coefficient semiring. -/
section Finite

variable {A : Type*} [Semiring A]

def finiteCurrent (N : ℕ) (F : ℕ → A) : Polynomial A := by
  classical
  exact Polynomial.ofFn N (fun i => F i.val)

theorem finiteCurrent_natDegree_le (N : ℕ) (F : ℕ → A) :
    (finiteCurrent N F).natDegree ≤ N - 1 := by
  classical
  cases N with
  | zero => simp [finiteCurrent]
  | succ N => exact Nat.le_pred_of_lt (Polynomial.ofFn_natDegree_lt (by omega) _)

theorem finiteCurrent_series (N : ℕ) (F : ℕ → A) (hF : ∀ j, N ≤ j → F j = 0) :
    (finiteCurrent N F : PowerSeries A) = PowerSeries.mk F := by
  classical
  apply PowerSeries.ext
  intro j
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
  change (Polynomial.ofFn N (fun i => F i.val)).coeff j = F j
  by_cases hj : j < N
  · exact Polynomial.ofFn_coeff_eq_val_of_lt _ hj
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega), hF j (by omega)]

private theorem reflect_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial A) (d : ℕ) :
    Polynomial.reflect d (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, Polynomial.reflect_add, ih]

theorem reflect_finiteCurrent_series (N : ℕ) (F : ℕ → A) :
    (Polynomial.reflect (N - 1) (finiteCurrent N F) : PowerSeries A) =
      ∑ i : Fin N, PowerSeries.C (F i.val) * PowerSeries.X ^ (N - 1 - i.val) := by
  classical
  have hp : Polynomial.reflect (N - 1) (finiteCurrent N F) =
      ∑ i : Fin N, Polynomial.C (F i.val) * Polynomial.X ^ (N - 1 - i.val) := by
    unfold finiteCurrent
    rw [Polynomial.ofFn_eq_sum_monomial, reflect_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow,
      Polynomial.revAt_le (by omega : i.val ≤ N - 1)]
  rw [hp]
  change Polynomial.coeToPowerSeries.ringHom (∑ i : Fin N,
    Polynomial.C (F i.val) * Polynomial.X ^ (N - 1 - i.val)) = _
  rw [map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]

end Finite

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

theorem map_starX (Nx Ny Nz : ℕ) :
    PowerSeries.map (polyAlg R w (modeLetter Nx Ny Nz)).toRingHom (starX Nx Ny Nz) =
      (Polynomial.reflect (Nx - 1) (finiteCurrent Nx (grOp R w 0)) :
        PowerSeries (Module.End ℂ (Gr R w))) := by
  have hφ (i : Vars Nx Ny Nz) :
      (polyAlg R w (modeLetter Nx Ny Nz)).toRingHom (MvPolynomial.X i) =
        polyOp R w (modeLetter Nx Ny Nz) i := polyAlg_X R w _ i
  rw [reflect_finiteCurrent_series]
  unfold starX
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    hφ, polyOp, modeLetter]

theorem map_starY (Nx Ny Nz : ℕ) :
    PowerSeries.map (polyAlg R w (modeLetter Nx Ny Nz)).toRingHom (starY Nx Ny Nz) =
      (Polynomial.reflect (Ny - 1) (finiteCurrent Ny (grOp R w 1)) :
        PowerSeries (Module.End ℂ (Gr R w))) := by
  have hφ (i : Vars Nx Ny Nz) :
      (polyAlg R w (modeLetter Nx Ny Nz)).toRingHom (MvPolynomial.X i) =
        polyOp R w (modeLetter Nx Ny Nz) i := polyAlg_X R w _ i
  rw [reflect_finiteCurrent_series]
  unfold starY
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    hφ, polyOp, modeLetter]

theorem map_starZ (Nx Ny Nz : ℕ) :
    PowerSeries.map (polyAlg R w (modeLetter Nx Ny Nz)).toRingHom (starZ Nx Ny Nz) =
      (Polynomial.reflect (Nz - 1) (finiteCurrent Nz (grOp R w 2)) :
        PowerSeries (Module.End ℂ (Gr R w))) := by
  have hφ (i : Vars Nx Ny Nz) :
      (polyAlg R w (modeLetter Nx Ny Nz)).toRingHom (MvPolynomial.X i) =
        polyOp R w (modeLetter Nx Ny Nz) i := polyAlg_X R w _ i
  rw [reflect_finiteCurrent_series]
  unfold starZ
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    hφ, polyOp, modeLetter]

def reverseDegree (Nx Ny Nz p q r : ℕ) : ℕ :=
  (Nx - 1) * p + (Ny - 1) * q + (Nz - 1) * r

theorem map_starCoeff (Nx Ny Nz p q r j : ℕ) :
    polyAlg R w (modeLetter Nx Ny Nz)
        (PowerSeries.coeff j (starX Nx Ny Nz ^ p * starY Nx Ny Nz ^ q * starZ Nx Ny Nz ^ r)) =
      (Polynomial.reflect (Nx - 1) (finiteCurrent Nx (grOp R w 0)) ^ p *
        Polynomial.reflect (Ny - 1) (finiteCurrent Ny (grOp R w 1)) ^ q *
        Polynomial.reflect (Nz - 1) (finiteCurrent Nz (grOp R w 2)) ^ r).coeff j := by
  change (polyAlg R w (modeLetter Nx Ny Nz)).toRingHom
    (PowerSeries.coeff j (starX Nx Ny Nz ^ p * starY Nx Ny Nz ^ q * starZ Nx Ny Nz ^ r)) = _
  rw [← PowerSeries.coeff_map]
  simp only [map_mul, map_pow, map_starX, map_starY, map_starZ]
  rw [← Polynomial.coe_pow, ← Polynomial.coe_pow, ← Polynomial.coe_pow,
    ← Polynomial.coe_mul, ← Polynomial.coe_mul, Polynomial.coeff_coe]

theorem finite_gr_series (a : Fin 3) (N : ℕ)
    (hN : ∀ t, N ≤ t → R.op (negRoot a) t w = 0) :
    (finiteCurrent N (grOp R w a) : PowerSeries (Module.End ℂ (Gr R w))) =
      Garland.Fs (grOp R w a) :=
  finiteCurrent_series N (grOp R w a)
    (fun t ht => grOp_zero_of_source_zero R w a t (hN t ht))

/-- Exact canonical STAR evaluation inside its prescribed reverse degree. -/
theorem starCoeff_eval (Nx Ny Nz p q r j : ℕ)
    (hx : ∀ t, Nx ≤ t → R.op 3 t w = 0)
    (hy : ∀ t, Ny ≤ t → R.op 5 t w = 0)
    (hz : ∀ t, Nz ≤ t → R.op 4 t w = 0)
    (hj : j ≤ reverseDegree Nx Ny Nz p q r) :
    polyEval R w (modeLetter Nx Ny Nz)
      (PowerSeries.coeff j (starX Nx Ny Nz ^ p * starY Nx Ny Nz ^ q * starZ Nx Ny Nz ^ r)) =
        gradedOrderedCoeff R w p q r (reverseDegree Nx Ny Nz p q r - j) := by
  change (polyAlg R w (modeLetter Nx Ny Nz) _) (grGenerator R w) = _
  rw [map_starCoeff]
  rw [coeff_reflect_three _ _ _ _ _ _ p q r j
    (finiteCurrent_natDegree_le _ _) (finiteCurrent_natDegree_le _ _)
    (finiteCurrent_natDegree_le _ _) hj]
  unfold gradedOrderedCoeff
  rw [← finite_gr_series R w 0 Nx hx, ← finite_gr_series R w 1 Ny hy,
    ← finite_gr_series R w 2 Nz hz, ← Polynomial.coe_pow, ← Polynomial.coe_pow,
    ← Polynomial.coe_pow, ← Polynomial.coe_mul, ← Polynomial.coe_mul,
    Polynomial.coeff_coe]
  rfl

/-- Beyond the prescribed degree, the canonical coefficient evaluates to
zero without a source annihilation premise. -/
theorem starCoeff_eval_high (Nx Ny Nz p q r j : ℕ)
    (hj : reverseDegree Nx Ny Nz p q r < j) :
    polyEval R w (modeLetter Nx Ny Nz)
      (PowerSeries.coeff j (starX Nx Ny Nz ^ p * starY Nx Ny Nz ^ q * starZ Nx Ny Nz ^ r)) = 0 := by
  change (polyAlg R w (modeLetter Nx Ny Nz) _) (grGenerator R w) = _
  rw [map_starCoeff, coeff_reflect_three_high _ _ _ _ _ _ p q r j
    (finiteCurrent_natDegree_le _ _) (finiteCurrent_natDegree_le _ _)
    (finiteCurrent_natDegree_le _ _) hj]
  rfl

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.starCoeff_eval
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.starCoeff_eval_high
