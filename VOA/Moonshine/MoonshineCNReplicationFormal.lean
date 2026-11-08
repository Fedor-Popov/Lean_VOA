import VOA.Moonshine.MoonshineLRFaber
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Formal replication from the twisted denominator identity

Two-variable series are `PowerSeries (PowerSeries ℂ)`: the outer variable is `p`, the inner one `q`.
Exponents are recorded in *height coordinates*: the root `(a, b)` of the positive cone contributes
`p^a q^(a+b)`.  In these coordinates the twisted denominator identity of a coefficient family
`c k n` (`c k` the coefficients of the `k`-th replicate) is the logarithm-free statement

  `D ũ = (1 − ũ) · P̃`,   `D = p ∂/∂p`,

with `ũ = Σ_{a,b ≥ 1} c₁(a+b−1) p^a q^(a+b)` and
`P̃ = Σ_{k ≥ 1} Σ_{a,b ≥ 1} a c_k(ab) p^(ak) q^((a+b)k)` (`TwistedDenominatorIdentity`).

Main result (`faberPoly_replication`): under this identity the Faber polynomial `F_m` of
`f = q⁻¹ + Σ_{n ≥ 1} c₁(n) qⁿ` (`M8.faberPoly`) satisfies

  `q^m F_m(f) = 1 + Σ_{r ≥ 1} (Σ_{a ∣ m, a ∣ r} (m/a) c_a(mr/a²)) q^(m+r)`,

i.e. the replication formulas.  The proof is logarithm-free: with
`Φ(p, X) = 1 − Xp + Σ_{n ≥ 1} c₁(n) p^(n+1)` and `Σ_m Q_m p^m = −DΦ/Φ`, the substitution
`X ↦ f`, `p ↦ pq` sends `Φ` to `(1 − p)(1 − ũ)`; the identity then forces
`Σ_m q^m Q_m(f) p^m = Σ_{k ≥ 1} p^k + P̃`, and the principal parts identify `Q_m` with `F_m`.

No vertex algebra is used in this file.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open Polynomial

/-! ### The Euler derivation `p d/dp` -/

section Euler

variable {R : Type*} [CommRing R]

/-- The Euler derivation `p d/dp`: the coefficient of `pⁿ` is multiplied by `n`. -/
def eulerDeriv (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => (n : R) * PowerSeries.coeff n F

@[simp] theorem coeff_eulerDeriv (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (eulerDeriv F) = (n : R) * PowerSeries.coeff n F :=
  PowerSeries.coeff_mk _ _

theorem eulerDeriv_add (F G : PowerSeries R) :
    eulerDeriv (F + G) = eulerDeriv F + eulerDeriv G := by
  ext n
  simp [mul_add]

theorem eulerDeriv_sub (F G : PowerSeries R) :
    eulerDeriv (F - G) = eulerDeriv F - eulerDeriv G := by
  ext n
  simp [mul_sub]

theorem eulerDeriv_neg (F : PowerSeries R) : eulerDeriv (-F) = -eulerDeriv F := by
  ext n
  simp

theorem eulerDeriv_one : eulerDeriv (1 : PowerSeries R) = 0 := by
  ext n
  rw [coeff_eulerDeriv, PowerSeries.coeff_one, map_zero]
  split_ifs with h <;> simp [h]

theorem eulerDeriv_X : eulerDeriv (PowerSeries.X : PowerSeries R) = PowerSeries.X := by
  ext n
  rw [coeff_eulerDeriv, PowerSeries.coeff_X]
  split_ifs with h <;> simp [h]

/-- The Leibniz rule. -/
theorem eulerDeriv_mul (F G : PowerSeries R) :
    eulerDeriv (F * G) = eulerDeriv F * G + F * eulerDeriv G := by
  ext n
  simp only [coeff_eulerDeriv, map_add, PowerSeries.coeff_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [← hij]
  push_cast
  ring

theorem eulerDeriv_map {S : Type*} [CommRing S] (φ : R →+* S) (F : PowerSeries R) :
    eulerDeriv (PowerSeries.map φ F) = PowerSeries.map φ (eulerDeriv F) := by
  ext n
  simp [map_mul, map_natCast]

theorem eulerDeriv_rescale (a : R) (F : PowerSeries R) :
    eulerDeriv (PowerSeries.rescale a F) = PowerSeries.rescale a (eulerDeriv F) := by
  ext n
  simp only [coeff_eulerDeriv, PowerSeries.coeff_rescale]
  ring

end Euler

/-! ### The two-variable series -/

/-- `ũ = Σ_{a ≥ 1, b ≥ 1} c(a+b−1) p^a q^(a+b)`: the coefficient of `p^a q^N` is `c(N − 1)` when
`1 ≤ a < N`. -/
def twistedUnitSeries (c : ℕ → ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun a => PowerSeries.mk fun N => if 1 ≤ a ∧ a < N then c (N - 1) else 0

/-- `P̃ = Σ_{k ≥ 1} Σ_{a, b ≥ 1} a c_k(ab) p^(ak) q^((a+b)k)`, written coefficientwise: the
coefficient of `p^A q^N` sums over the divisors `k` of `A` that divide `N`, with `A < N`. -/
def twistedPowerSum (c : ℕ → ℕ → ℂ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun A => PowerSeries.mk fun N =>
    ∑ k ∈ A.divisors,
      if k ∣ N ∧ A < N then ((A / k : ℕ) : ℂ) * c k (A / k * ((N - A) / k)) else 0

/-- **The twisted denominator identity** of a replicate family `c k n`, logarithm-free and in
height coordinates: `D ũ = (1 − ũ) P̃`. -/
def TwistedDenominatorIdentity (c : ℕ → ℕ → ℂ) : Prop :=
  eulerDeriv (twistedUnitSeries (c 1)) = (1 - twistedUnitSeries (c 1)) * twistedPowerSum c

/-- `Σ_{k ≥ 1} p^k`. -/
def positiveGeometricSeries : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun k => if k = 0 then 0 else 1

theorem one_sub_X_mul_positiveGeometricSeries :
    (1 - PowerSeries.X) * positiveGeometricSeries = PowerSeries.X := by
  refine PowerSeries.ext fun n => ?_
  rw [sub_mul, one_mul, map_sub]
  rcases n with _ | n
  · simp [positiveGeometricSeries, PowerSeries.coeff_X]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X]
    rcases n with _ | n <;> simp [positiveGeometricSeries]

/-- The coefficient of `p^A q^N` in `P̃` vanishes for `N ≤ A`. -/
theorem coeff_coeff_twistedPowerSum_of_le (c : ℕ → ℕ → ℂ) {A N : ℕ} (h : N ≤ A) :
    PowerSeries.coeff N (PowerSeries.coeff A (twistedPowerSum c)) = 0 := by
  simp only [twistedPowerSum, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun k _ => if_neg fun hk => absurd hk.2 (not_lt.mpr h)

/-- The replication coefficient `Σ_{a ∣ m, a ∣ r} (m/a) c_a((m/a)(r/a))`. -/
def replicationCoeff (c : ℕ → ℕ → ℂ) (m r : ℕ) : ℂ :=
  ∑ a ∈ m.divisors, if a ∣ r then ((m / a : ℕ) : ℂ) * c a (m / a * (r / a)) else 0

theorem coeff_coeff_twistedPowerSum_add (c : ℕ → ℕ → ℂ) (m r : ℕ) (hr : 0 < r) :
    PowerSeries.coeff (m + r) (PowerSeries.coeff m (twistedPowerSum c)) =
      replicationCoeff c m r := by
  simp only [twistedPowerSum, PowerSeries.coeff_mk, replicationCoeff]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ham : a ∣ m := Nat.dvd_of_mem_divisors ha
  have hiff : a ∣ m + r ∧ m < m + r ↔ a ∣ r :=
    ⟨fun h => (Nat.dvd_add_right ham).mp h.1, fun h => ⟨dvd_add ham h, by omega⟩⟩
  simp only [hiff, Nat.add_sub_cancel_left]

/-! ### The Faber generating function -/

/-- `Φ(p, X) = 1 − X p + Σ_{n ≥ 1} c(n) p^(n+1)` in `ℂ[X][[p]]`. -/
def faberGenerating (c : ℕ → ℂ) : PowerSeries ℂ[X] :=
  PowerSeries.mk fun n => if n = 0 then 1 else if n = 1 then -X else C (c (n - 1))

theorem constantCoeff_faberGenerating (c : ℕ → ℂ) :
    PowerSeries.constantCoeff (faberGenerating c) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [faberGenerating]

/-- `Σ_m Q_m(X) p^m = −DΦ / Φ`. -/
def faberLogDerivSeries (c : ℕ → ℂ) : PowerSeries ℂ[X] :=
  -eulerDeriv (faberGenerating c) * PowerSeries.invOfUnit (faberGenerating c) 1

theorem faberGenerating_mul_faberLogDerivSeries (c : ℕ → ℂ) :
    faberGenerating c * faberLogDerivSeries c = -eulerDeriv (faberGenerating c) := by
  rw [faberLogDerivSeries, mul_comm (-eulerDeriv _), ← mul_assoc,
    PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_faberGenerating, Units.val_one]), one_mul]

/-! ### Substituting `X ↦ f` and `p ↦ p q` -/

/-- `Σ_m G_m(X) p^m ↦ Σ_m q^m G_m(f) p^m`, with `f = q⁻¹ + Σ_{n ≥ 1} c(n) qⁿ`. -/
def faberEvaluation (c : ℕ → ℂ) : PowerSeries ℂ[X] →+* PowerSeries (LaurentSeries ℂ) :=
  (PowerSeries.rescale (HahnSeries.single (1 : ℤ) (1 : ℂ))).comp
    (PowerSeries.map (aeval (M8.qSeriesLaurent c)).toRingHom)

theorem coeff_faberEvaluation (c : ℕ → ℂ) (G : PowerSeries ℂ[X]) (m : ℕ) :
    PowerSeries.coeff m (faberEvaluation c G) =
      HahnSeries.single (m : ℤ) (1 : ℂ) * aeval (M8.qSeriesLaurent c) (PowerSeries.coeff m G) := by
  simp [faberEvaluation, PowerSeries.coeff_rescale, PowerSeries.coeff_map, HahnSeries.single_pow]

theorem faberEvaluation_eulerDeriv (c : ℕ → ℂ) (G : PowerSeries ℂ[X]) :
    faberEvaluation c (eulerDeriv G) = eulerDeriv (faberEvaluation c G) := by
  simp only [faberEvaluation, RingHom.coe_comp, Function.comp_apply, eulerDeriv_map,
    eulerDeriv_rescale]

/-- The embedding `ℂ[[q]][[p]] → ℂ((q))[[p]]`. -/
abbrev laurentEmbedding : PowerSeries (PowerSeries ℂ) →+* PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.map (HahnSeries.ofPowerSeries ℤ ℂ)

theorem laurentEmbedding_injective : Function.Injective laurentEmbedding := by
  intro F G h
  refine PowerSeries.ext fun n => HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) ?_
  have := congrArg (PowerSeries.coeff n) h
  simpa only [PowerSeries.coeff_map] using this

theorem coeff_one_sub_X_mul_one_sub_twistedUnitSeries (c : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n ((1 - PowerSeries.X) * (1 - twistedUnitSeries c)) =
      if n = 0 then 1 else if n = 1 then -M8.qSeriesUnit c
        else PowerSeries.C (c (n - 1)) * PowerSeries.X ^ n := by
  rw [sub_mul, one_mul, map_sub]
  match n with
  | 0 =>
    rw [PowerSeries.coeff_zero_X_mul, sub_zero, if_pos rfl]
    refine PowerSeries.ext fun N => ?_
    simp [twistedUnitSeries, PowerSeries.coeff_one]
  | 1 =>
    rw [PowerSeries.coeff_succ_X_mul, if_neg one_ne_zero, if_pos rfl]
    refine PowerSeries.ext fun N => ?_
    match N with
    | 0 => simp [twistedUnitSeries, M8.qSeriesUnit, PowerSeries.coeff_one]
    | 1 => simp [twistedUnitSeries, M8.qSeriesUnit, PowerSeries.coeff_one]
    | N + 2 => simp [twistedUnitSeries, M8.qSeriesUnit, PowerSeries.coeff_one]
  | n + 2 =>
    rw [PowerSeries.coeff_succ_X_mul, if_neg (show n + 2 ≠ 0 by omega),
      if_neg (show n + 2 ≠ 1 by omega)]
    refine PowerSeries.ext fun N => ?_
    simp only [map_sub, PowerSeries.coeff_one, show n + 2 ≠ 0 by omega,
      show n + 1 ≠ 0 by omega, ↓reduceIte, map_zero, twistedUnitSeries, PowerSeries.coeff_mk,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> first | (exfalso; omega) | ring1 |
      (rw [show N - 1 = n + 2 - 1 by omega]; ring)

theorem algebraMap_laurentSeries (a : ℂ) :
    algebraMap ℂ (LaurentSeries ℂ) a = HahnSeries.single 0 a := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

/-- Under the substitution, `Φ` becomes `(1 − p)(1 − ũ)`. -/
theorem faberEvaluation_faberGenerating (c : ℕ → ℂ) :
    faberEvaluation c (faberGenerating c) =
      laurentEmbedding ((1 - PowerSeries.X) * (1 - twistedUnitSeries c)) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_faberEvaluation, PowerSeries.coeff_map,
    coeff_one_sub_X_mul_one_sub_twistedUnitSeries]
  simp only [faberGenerating, PowerSeries.coeff_mk]
  match n with
  | 0 => simp
  | 1 =>
    simp only [one_ne_zero, ↓reduceIte, map_neg, aeval_X, mul_neg, M8.qSeriesLaurent,
      Nat.cast_one]
    rw [← mul_assoc, HahnSeries.single_mul_single, one_mul, add_neg_cancel,
      HahnSeries.single_zero_one, one_mul]
  | n + 2 =>
    simp only [show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega, ↓reduceIte,
      aeval_C, algebraMap_laurentSeries, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, HahnSeries.single_mul_single, one_mul,
      mul_one, add_zero, zero_add]

/-! ### Formal replication -/

section Replication

variable (c : ℕ → ℕ → ℂ)

/-- The twisted denominator identity solves the Faber recursion with `Σ_{k ≥ 1} p^k + P̃`. -/
theorem twistedFaberRecursion (hTD : TwistedDenominatorIdentity c) :
    (1 - PowerSeries.X) * (1 - twistedUnitSeries (c 1)) *
        (positiveGeometricSeries + twistedPowerSum c) =
      -eulerDeriv ((1 - PowerSeries.X) * (1 - twistedUnitSeries (c 1))) := by
  have hTD' : eulerDeriv (twistedUnitSeries (c 1)) =
      (1 - twistedUnitSeries (c 1)) * twistedPowerSum c := hTD
  rw [eulerDeriv_mul, eulerDeriv_sub, eulerDeriv_sub, eulerDeriv_one, eulerDeriv_X, hTD']
  linear_combination (1 - twistedUnitSeries (c 1)) * one_sub_X_mul_positiveGeometricSeries

theorem faberEvaluation_faberLogDerivSeries (hTD : TwistedDenominatorIdentity c) :
    faberEvaluation (c 1) (faberLogDerivSeries (c 1)) =
      laurentEmbedding (positiveGeometricSeries + twistedPowerSum c) := by
  have h := congrArg (faberEvaluation (c 1)) (faberGenerating_mul_faberLogDerivSeries (c 1))
  rw [map_mul, map_neg, faberEvaluation_eulerDeriv, faberEvaluation_faberGenerating,
    eulerDeriv_map, ← map_neg laurentEmbedding, ← twistedFaberRecursion c hTD,
    map_mul laurentEmbedding ((1 - PowerSeries.X) * (1 - twistedUnitSeries (c 1)))] at h
  have hne : laurentEmbedding ((1 - PowerSeries.X) * (1 - twistedUnitSeries (c 1))) ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff 0) h0
    rw [PowerSeries.coeff_map, coeff_one_sub_X_mul_one_sub_twistedUnitSeries, if_pos rfl,
      map_one, map_zero] at h1
    exact one_ne_zero h1
  exact mul_left_cancel₀ hne h

/-- The coefficientwise form: `q^m Q_m(f) = [p^m](Σ_{k ≥ 1} p^k + P̃)`. -/
theorem faberLogDerivSeries_coeff_eval (hTD : TwistedDenominatorIdentity c) (m : ℕ) :
    HahnSeries.single (m : ℤ) (1 : ℂ) *
        aeval (M8.qSeriesLaurent (c 1)) (PowerSeries.coeff m (faberLogDerivSeries (c 1))) =
      HahnSeries.ofPowerSeries ℤ ℂ
        (PowerSeries.coeff m (positiveGeometricSeries + twistedPowerSum c)) := by
  have h := congrArg (PowerSeries.coeff m) (faberEvaluation_faberLogDerivSeries c hTD)
  rwa [coeff_faberEvaluation, PowerSeries.coeff_map] at h

/-- The polynomial `Q_m` is the Faber polynomial `F_m`, for `m ≥ 1`. -/
theorem faberLogDerivSeries_coeff_eq_faberPoly (hTD : TwistedDenominatorIdentity c) (m : ℕ)
    (hm : 0 < m) :
    PowerSeries.coeff m (faberLogDerivSeries (c 1)) = M8.faberPoly (c 1) m := by
  apply M8.eq_faberPoly_of_coeff
  intro k hk
  have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (k + m))
    (faberLogDerivSeries_coeff_eval c hTD m)
  simp only [HahnSeries.coeff_single_mul, add_sub_cancel_right, one_mul] at h
  rw [h, PowerSeries.coeff_coe]
  by_cases hneg : k + m < 0
  · rw [if_pos hneg, if_neg (show k ≠ -(m : ℤ) by omega)]
  · rw [if_neg hneg]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, k + m = j := ⟨(k + m).toNat, by omega⟩
    rw [hj, Int.natAbs_natCast, map_add, map_add,
      coeff_coeff_twistedPowerSum_of_le c (show j ≤ m by omega), add_zero]
    simp only [positiveGeometricSeries, PowerSeries.coeff_mk, if_neg hm.ne']
    rw [PowerSeries.coeff_one]
    by_cases hj0 : j = 0
    · rw [if_pos hj0, if_pos (show k = -(m : ℤ) by omega)]
    · rw [if_neg hj0, if_neg (show k ≠ -(m : ℤ) by omega)]

/-- **Formal replication.** If the twisted denominator identity holds, the Faber polynomial `F_m`
of `f = q⁻¹ + Σ_{n ≥ 1} c₁(n) qⁿ` satisfies `q^m F_m(f) = 1 + [p^m] P̃`, i.e.
`F_m(f) = q^{−m} + Σ_{r ≥ 1} replicationCoeff c m r · q^r`. -/
theorem faberPoly_replication (hTD : TwistedDenominatorIdentity c) (m : ℕ) (hm : 0 < m) :
    HahnSeries.single (m : ℤ) (1 : ℂ) * aeval (M8.qSeriesLaurent (c 1)) (M8.faberPoly (c 1) m) =
      HahnSeries.ofPowerSeries ℤ ℂ (1 + PowerSeries.coeff m (twistedPowerSum c)) := by
  rw [← faberLogDerivSeries_coeff_eq_faberPoly c hTD m hm, faberLogDerivSeries_coeff_eval c hTD m]
  congr 1
  rw [map_add]
  congr 1
  simp [positiveGeometricSeries, hm.ne']

end Replication

/-! ### Homogenized evaluation of polynomials -/

/-- `q^m P(f)` for `deg P ≤ m`, as a power series: `Σ_{j ≤ m} P_j q^(m−j) u^j` with `u = q f`. -/
def homogenizedEval (c : ℕ → ℂ) (m : ℕ) (P : ℂ[X]) : PowerSeries ℂ :=
  ∑ j ∈ Finset.range (m + 1),
    PowerSeries.C (P.coeff j) * PowerSeries.X ^ (m - j) * M8.qSeriesUnit c ^ j

theorem ofPowerSeries_homogenizedEval (c : ℕ → ℂ) (m : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ m) :
    HahnSeries.ofPowerSeries ℤ ℂ (homogenizedEval c m P) =
      HahnSeries.single (m : ℤ) (1 : ℂ) * aeval (M8.qSeriesLaurent c) P := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum, homogenizedEval, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hs : HahnSeries.single ((m - j : ℕ) : ℤ) (1 : ℂ) =
      HahnSeries.single (m : ℤ) (1 : ℂ) * HahnSeries.single (-(j : ℤ)) 1 := by
    rw [HahnSeries.single_mul_single, one_mul,
      show (m : ℤ) + -(j : ℤ) = ((m - j : ℕ) : ℤ) by omega]
  rw [M8.qSeriesLaurent_pow, Algebra.smul_def, algebraMap_laurentSeries, map_mul, map_mul,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, hs]
  ring

/-- **Formal replication, power-series form**: `q^m F_m(f) = 1 + [p^m] P̃` in `ℂ[[q]]`. -/
theorem homogenizedEval_faberPoly (c : ℕ → ℕ → ℂ) (hTD : TwistedDenominatorIdentity c) (m : ℕ)
    (hm : 0 < m) :
    homogenizedEval (c 1) m (M8.faberPoly (c 1) m) =
      1 + PowerSeries.coeff m (twistedPowerSum c) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  rw [ofPowerSeries_homogenizedEval _ _ _ (M8.faberPoly_natDegree _ _).le,
    faberPoly_replication c hTD m hm]

end VOA.Moonshine.ConwayNorton
