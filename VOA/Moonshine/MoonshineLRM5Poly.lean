import VOA.Moonshine.MoonshineLRM5Hecke
import VOA.Moonshine.MoonshineLRFaberGenerating

/-!
# Polynomials of `q`-series

For a `J`-dominated `c` with `f = qSeriesFun c` and a polynomial `P` of degree `D`, the function
`τ ↦ P(f(τ))` has the `q`-expansion given by the formal Laurent series `P(f) ∈ ℂ((q))`
(`MoonshineLRFaber`):
`q^D · P(f(τ)) = Σ_{n ≥ 0} [q^{n−D}] P(f) · qⁿ` (`hasSum_mul_eval_qSeriesFun`).
Blueprint: polynomial evaluation of `q`-series in `Notes/moonshine/MOON_BKM.md`.

Method. Absolutely convergent power-series evaluation (`PowerSeriesAbsConv`, `powerSeriesEval`) is
compatible with sums and products (Cauchy product). Then `q f(τ) = U(q)` for the unit part
`U = qSeriesUnit c`, and `q^D P(f) = W(q)` with `W = Σ_j p_j X^{D−j} Uʲ`. On the formal side,
`P(f) = q^{−D} · W` (`aeval_qSeriesLaurent_eq_single_mul`).
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real Polynomial

/-- The power series `φ` converges absolutely at `z`. -/
def PowerSeriesAbsConv (φ : PowerSeries ℂ) (z : ℂ) : Prop :=
  Summable fun n => ‖PowerSeries.coeff n φ * z ^ n‖

/-- The value `Σ' n, [zⁿ]φ · zⁿ` of a power series at `z`. -/
noncomputable def powerSeriesEval (φ : PowerSeries ℂ) (z : ℂ) : ℂ :=
  ∑' n, PowerSeries.coeff n φ * z ^ n

theorem PowerSeriesAbsConv.add {φ ψ : PowerSeries ℂ} {z : ℂ} (hφ : PowerSeriesAbsConv φ z)
    (hψ : PowerSeriesAbsConv ψ z) : PowerSeriesAbsConv (φ + ψ) z := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (Summable.add hφ hψ)
  rw [map_add, add_mul]
  exact norm_add_le _ _

theorem powerSeriesEval_add {φ ψ : PowerSeries ℂ} {z : ℂ} (hφ : PowerSeriesAbsConv φ z)
    (hψ : PowerSeriesAbsConv ψ z) :
    powerSeriesEval (φ + ψ) z = powerSeriesEval φ z + powerSeriesEval ψ z := by
  simp only [powerSeriesEval, map_add, add_mul]
  exact (Summable.of_norm hφ).tsum_add (Summable.of_norm hψ)

theorem PowerSeriesAbsConv.mul {φ ψ : PowerSeries ℂ} {z : ℂ} (hφ : PowerSeriesAbsConv φ z)
    (hψ : PowerSeriesAbsConv ψ z) : PowerSeriesAbsConv (φ * ψ) z := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hφ hψ
  refine h.congr fun n => ?_
  congr 1
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

theorem powerSeriesEval_mul {φ ψ : PowerSeries ℂ} {z : ℂ} (hφ : PowerSeriesAbsConv φ z)
    (hψ : PowerSeriesAbsConv ψ z) :
    powerSeriesEval (φ * ψ) z = powerSeriesEval φ z * powerSeriesEval ψ z := by
  rw [powerSeriesEval, powerSeriesEval, powerSeriesEval,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hφ hψ]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

theorem powerSeriesAbsConv_C (a z : ℂ) : PowerSeriesAbsConv (PowerSeries.C a) z := by
  refine (hasSum_single 0 fun n hn => ?_).summable
  rw [PowerSeries.coeff_C, if_neg hn, zero_mul, norm_zero]

theorem powerSeriesEval_C (a z : ℂ) : powerSeriesEval (PowerSeries.C a) z = a := by
  rw [powerSeriesEval,
    tsum_eq_single 0 fun n hn => by rw [PowerSeries.coeff_C, if_neg hn, zero_mul]]
  simp

theorem powerSeriesAbsConv_X (z : ℂ) : PowerSeriesAbsConv PowerSeries.X z := by
  refine (hasSum_single 1 fun n hn => ?_).summable
  rw [PowerSeries.coeff_X, if_neg hn, zero_mul, norm_zero]

theorem powerSeriesEval_X (z : ℂ) : powerSeriesEval PowerSeries.X z = z := by
  rw [powerSeriesEval,
    tsum_eq_single 1 fun n hn => by rw [PowerSeries.coeff_X, if_neg hn, zero_mul]]
  simp

theorem PowerSeriesAbsConv.pow {φ : PowerSeries ℂ} {z : ℂ} (hφ : PowerSeriesAbsConv φ z) (n : ℕ) :
    PowerSeriesAbsConv (φ ^ n) z := by
  induction n with
  | zero => rw [pow_zero, ← map_one PowerSeries.C]; exact powerSeriesAbsConv_C 1 z
  | succ n ih => rw [pow_succ]; exact ih.mul hφ

theorem powerSeriesEval_pow {φ : PowerSeries ℂ} {z : ℂ} (hφ : PowerSeriesAbsConv φ z) (n : ℕ) :
    powerSeriesEval (φ ^ n) z = powerSeriesEval φ z ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← map_one PowerSeries.C, powerSeriesEval_C]
  | succ n ih => rw [pow_succ, powerSeriesEval_mul (hφ.pow n) hφ, ih, pow_succ]

theorem PowerSeriesAbsConv.sum {ι : Type*} (s : Finset ι) {φ : ι → PowerSeries ℂ} {z : ℂ}
    (h : ∀ i ∈ s, PowerSeriesAbsConv (φ i) z) : PowerSeriesAbsConv (∑ i ∈ s, φ i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, ← map_zero PowerSeries.C]
    exact powerSeriesAbsConv_C 0 z
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem powerSeriesEval_sum {ι : Type*} (s : Finset ι) {φ : ι → PowerSeries ℂ} {z : ℂ}
    (h : ∀ i ∈ s, PowerSeriesAbsConv (φ i) z) :
    powerSeriesEval (∑ i ∈ s, φ i) z = ∑ i ∈ s, powerSeriesEval (φ i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← map_zero PowerSeries.C, powerSeriesEval_C]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      powerSeriesEval_add (h i (Finset.mem_insert_self i s))
        (PowerSeriesAbsConv.sum s fun j hj => h j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

/-! ### The unit part `U = q f` -/

theorem powerSeriesAbsConv_qSeriesUnit {c : ℕ → ℂ} (hc : IsJDominated c) (τ : ℍ) :
    PowerSeriesAbsConv (qSeriesUnit c) (qPar τ) := by
  have hs := (summable_qTail_term hc τ.im_pos (norm_qPar_eq τ).le).norm
  have hs2 : Summable fun n : ℕ =>
      ‖PowerSeries.coeff (n + 2) (qSeriesUnit c) * qPar τ ^ (n + 2)‖ := by
    refine (hs.mul_left ‖qPar τ‖).congr fun n => ?_
    rw [coeff_qSeriesUnit, if_neg (by omega), if_neg (by omega), show n + 2 - 1 = n + 1 by omega,
      norm_mul, norm_mul, norm_pow, norm_pow, pow_succ _ (n + 1)]
    ring
  exact (summable_nat_add_iff 2).mp hs2

/-- `U(q) = q · f(τ)`. -/
theorem powerSeriesEval_qSeriesUnit {c : ℕ → ℂ} (hc : IsJDominated c) (τ : ℍ) :
    powerSeriesEval (qSeriesUnit c) (qPar τ) = qPar τ * qSeriesFun c τ := by
  have hsum := Summable.of_norm (powerSeriesAbsConv_qSeriesUnit hc τ)
  rw [powerSeriesEval, ← hsum.sum_add_tsum_nat_add 2]
  have htail := (summable_qTail_term hc τ.im_pos (norm_qPar_eq τ).le).hasSum
  have hq : qPar τ ≠ 0 := Function.Periodic.qParam_ne_zero _
  rw [qSeriesFun_eq_inv_add_qTailSeries, mul_add, mul_inv_cancel₀ hq, qTailSeries,
    ← tsum_mul_left]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_qSeriesUnit]
  norm_num
  refine tsum_congr fun n => ?_
  rw [if_neg (by omega)]
  ring

/-! ### Polynomials -/

/-- `W(P) = Σ_{j ≤ D} p_j X^{D−j} Uʲ`, so that `P(f) = q^{−D} W(P)` (`D = deg P`). -/
noncomputable def polyUnitSeries (c : ℕ → ℂ) (P : ℂ[X]) : PowerSeries ℂ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    PowerSeries.C (P.coeff j) * PowerSeries.X ^ (P.natDegree - j) * qSeriesUnit c ^ j

/-- Formal side: `P(f) = q^{−D} · W(P)` in `ℂ((q))`. -/
theorem aeval_qSeriesLaurent_eq_single_mul (c : ℕ → ℂ) (P : ℂ[X]) :
    aeval (qSeriesLaurent c) P = HahnSeries.single (-(P.natDegree : ℤ)) (1 : ℂ) *
      HahnSeries.ofPowerSeries ℤ ℂ (polyUnitSeries c P) := by
  rw [aeval_eq_sum_range, polyUnitSeries, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [qSeriesLaurent_pow, map_mul, map_mul, map_pow, HahnSeries.ofPowerSeries_X_pow,
    HahnSeries.ofPowerSeries_C, Algebra.smul_def]
  have halg : algebraMap ℂ (LaurentSeries ℂ) (P.coeff j) = HahnSeries.C (P.coeff j) := by
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HahnSeries.ofPowerSeries_C]
  rw [halg, ← map_pow]
  have hs : (HahnSeries.single (-(P.natDegree : ℤ)) (1 : ℂ) : LaurentSeries ℂ) *
      HahnSeries.single ((P.natDegree - j : ℕ) : ℤ) 1 = HahnSeries.single (-(j : ℤ)) 1 := by
    rw [HahnSeries.single_mul_single, one_mul]
    congr 1
    push_cast [Nat.cast_sub hjD]
    ring_nf
  calc HahnSeries.C (P.coeff j) * (HahnSeries.single (-(j : ℤ)) (1 : ℂ) *
        HahnSeries.ofPowerSeries ℤ ℂ (qSeriesUnit c ^ j))
      = HahnSeries.C (P.coeff j) * ((HahnSeries.single (-(P.natDegree : ℤ)) (1 : ℂ) *
          HahnSeries.single ((P.natDegree - j : ℕ) : ℤ) 1) *
          HahnSeries.ofPowerSeries ℤ ℂ (qSeriesUnit c ^ j)) := by rw [hs]
    _ = _ := by ring

theorem powerSeriesAbsConv_polyUnitSeries {c : ℕ → ℂ} (hc : IsJDominated c) (P : ℂ[X]) (τ : ℍ) :
    PowerSeriesAbsConv (polyUnitSeries c P) (qPar τ) :=
  PowerSeriesAbsConv.sum _ fun _ _ =>
    ((powerSeriesAbsConv_C _ _).mul ((powerSeriesAbsConv_X _).pow _)).mul
      ((powerSeriesAbsConv_qSeriesUnit hc τ).pow _)

/-- Analytic side: `q^D · P(f(τ)) = W(P)(q)`. -/
theorem powerSeriesEval_polyUnitSeries {c : ℕ → ℂ} (hc : IsJDominated c) (P : ℂ[X]) (τ : ℍ) :
    powerSeriesEval (polyUnitSeries c P) (qPar τ) =
      qPar τ ^ P.natDegree * P.eval (qSeriesFun c τ) := by
  have hU := powerSeriesAbsConv_qSeriesUnit hc τ
  rw [polyUnitSeries, powerSeriesEval_sum _ fun j _ =>
    ((powerSeriesAbsConv_C _ _).mul ((powerSeriesAbsConv_X _).pow _)).mul (hU.pow _),
    eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [powerSeriesEval_mul ((powerSeriesAbsConv_C _ _).mul ((powerSeriesAbsConv_X _).pow _))
      (hU.pow _),
    powerSeriesEval_mul (powerSeriesAbsConv_C _ _) ((powerSeriesAbsConv_X _).pow _),
    powerSeriesEval_C, powerSeriesEval_pow (powerSeriesAbsConv_X _), powerSeriesEval_X,
    powerSeriesEval_pow hU, powerSeriesEval_qSeriesUnit hc]
  conv_rhs => rw [show P.natDegree = (P.natDegree - j) + j by omega]
  ring

/-- **Polynomials of `q`-series** (blueprint: polynomial evaluation in `MOON_BKM.md`):
`q^D · P(f(τ)) = Σ_{n ≥ 0} [q^{n−D}] P(f) · qⁿ`, absolutely convergent, with `D = deg P`. -/
theorem hasSum_mul_eval_qSeriesFun {c : ℕ → ℂ} (hc : IsJDominated c) (P : ℂ[X]) (τ : ℍ) :
    HasSum (fun n : ℕ => (aeval (qSeriesLaurent c) P).coeff ((n : ℤ) - P.natDegree) * qPar τ ^ n)
      (qPar τ ^ P.natDegree * P.eval (qSeriesFun c τ)) := by
  rw [← powerSeriesEval_polyUnitSeries hc P τ]
  have h := (Summable.of_norm (powerSeriesAbsConv_polyUnitSeries hc P τ)).hasSum
  convert h using 1
  funext n
  rw [aeval_qSeriesLaurent_eq_single_mul, HahnSeries.coeff_single_mul, one_mul,
    show (n : ℤ) - P.natDegree - -(P.natDegree : ℤ) = (n : ℤ) by ring,
    HahnSeries.ofPowerSeries_apply_coeff]

end VOA.Moonshine.ConwayNorton.M8
