import VOA.Moonshine.MoonshineLRFaber
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The Faber recursion

For `f = q⁻¹ + Σ_{n ≥ 1} c(n) qⁿ` with Faber polynomials `F_m` (`MoonshineLRFaber`), this file
proves
* `coeff_one_aeval_faberPoly`: the coefficient of `q` in `F_m(f)` is `m · c(m)` for `m ≥ 1`;
* `faberPoly_recursion`: `F_{n+2} = X F_{n+1} − Σ_{j<n} c(j+1) F_{n−j} − (n+2) c(n+1)`.

The recursion is the coefficient form of the generating identity of
`Notes/moonshine/MOON_ROUTE.md`, namely `−p · d/dp G(p) = G(p) · Σ_{m ≥ 1} F_m(X) pᵐ` with
`G(p) = p (f(p) − X) = 1 − Xp + Σ_{n≥1} c(n) p^{n+1}`.

The coefficient of `q` comes from a residue argument done on power series: the coefficient of
`q⁻¹` in `fʲ · f′` vanishes for every `j` (`coeff_neg_one_pow_mul_deriv`), because `fʲ f′` is a
derivative. Here `f′ = −q⁻² u + q⁻¹ u′` is written explicitly (`qSeriesLaurentDeriv`), with
`u = q f` and `u′` the power-series derivative, so no product rule for Laurent series is needed.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open Polynomial

/-- If `x` vanishes below `a` and `y` vanishes below `b`, then `x * y` vanishes below `a + b`. -/
theorem coeff_mul_eq_zero_of_lt {x y : LaurentSeries ℂ} {a b : ℤ}
    (hx : ∀ i : ℤ, i < a → x.coeff i = 0) (hy : ∀ j : ℤ, j < b → y.coeff j = 0) {k : ℤ}
    (hk : k < a + b) : (x * y).coeff k = 0 := by
  have hxa : ((a : ℤ) : WithTop ℤ) ≤ x.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr fun j hj => hx j (by exact_mod_cast hj)
  have hyb : ((b : ℤ) : WithTop ℤ) ≤ y.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr fun j hj => hy j (by exact_mod_cast hj)
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  calc ((k : ℤ) : WithTop ℤ) < ((a + b : ℤ) : WithTop ℤ) := by exact_mod_cast hk
    _ = (a : WithTop ℤ) + (b : WithTop ℤ) := WithTop.coe_add a b
    _ ≤ x.orderTop + y.orderTop := add_le_add hxa hyb
    _ ≤ (x * y).orderTop := HahnSeries.orderTop_add_le_mul

theorem coeff_qSeriesUnit (c : ℕ → ℂ) (k : ℕ) :
    PowerSeries.coeff k (qSeriesUnit c) = if k = 0 then 1 else if k = 1 then 0 else c (k - 1) := by
  simp [qSeriesUnit]

/-- `q`-coefficients of `f` at natural indices `n ≥ 1`. -/
theorem coeff_qSeriesLaurent_natCast (c : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (qSeriesLaurent c).coeff (n : ℤ) = c n := by
  have h := coeff_qSeriesLaurent_pow c 1 n
  rw [pow_one, pow_one] at h
  rw [h, if_neg (by omega), show ((n : ℤ) + ((1 : ℕ) : ℤ)).natAbs = n + 1 by omega,
    coeff_qSeriesUnit, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]

/-- Below `q¹`, the only coefficient of `f` is the `q⁻¹` one. -/
theorem coeff_qSeriesLaurent_of_lt_one (c : ℕ → ℂ) {k : ℤ} (hk : k < 1) :
    (qSeriesLaurent c).coeff k = if k = -1 then 1 else 0 := by
  have h := coeff_qSeriesLaurent_pow c 1 k
  rw [pow_one, pow_one] at h
  rw [h]
  rcases lt_trichotomy k (-1) with hlt | heq | hgt
  · rw [if_pos (by push_cast; omega), if_neg (by omega)]
  · subst heq
    rw [if_neg (by norm_num), if_pos rfl]
    norm_num [coeff_qSeriesUnit]
  · have h0 : k = 0 := by omega
    subst h0
    rw [if_neg (by norm_num), if_neg (by norm_num)]
    norm_num [coeff_qSeriesUnit]

/-- `f′ = −q⁻² u + q⁻¹ u′` with `u = q f`; as a series, `−q⁻² + Σ_{n ≥ 1} n c(n) q^{n−1}`. -/
noncomputable def qSeriesLaurentDeriv (c : ℕ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-2 : ℤ) (-1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (qSeriesUnit c) +
    HahnSeries.single (-1 : ℤ) (1 : ℂ) *
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.derivative ℂ (qSeriesUnit c))

/-- `[qⁿ] f′ = (n+1) c(n+1)` for `n ≥ 0`. -/
theorem coeff_qSeriesLaurentDeriv_natCast (c : ℕ → ℂ) (n : ℕ) :
    (qSeriesLaurentDeriv c).coeff (n : ℤ) = (n + 1) * c (n + 1) := by
  rw [qSeriesLaurentDeriv, HahnSeries.coeff_add, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_single_mul,
    show (n : ℤ) - (-2) = ((n + 2 : ℕ) : ℤ) by push_cast; ring,
    show (n : ℤ) - (-1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
    HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_derivative, coeff_qSeriesUnit, if_neg (by omega), if_neg (by omega)]
  push_cast
  ring

/-- `f′ − (−q⁻²)` has no negative powers of `q`. -/
theorem coeff_qSeriesLaurentDeriv_sub_of_neg (c : ℕ → ℂ) {j : ℤ} (hj : j < 0) :
    (qSeriesLaurentDeriv c - HahnSeries.single (-2 : ℤ) (-1 : ℂ)).coeff j = 0 := by
  rw [qSeriesLaurentDeriv, HahnSeries.coeff_sub, HahnSeries.coeff_add,
    HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, PowerSeries.coeff_coe,
    PowerSeries.coeff_coe, HahnSeries.coeff_single]
  rcases lt_trichotomy j (-2) with hlt | heq | hgt
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]
    ring
  · subst heq
    rw [if_neg (by norm_num), if_pos (by norm_num), if_pos rfl]
    norm_num [coeff_qSeriesUnit]
  · have h1 : j = -1 := by omega
    subst h1
    rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
    norm_num [PowerSeries.coeff_derivative, coeff_qSeriesUnit]

/-- **Residue lemma.** The coefficient of `q⁻¹` in `fʲ · f′` is zero: `fʲ f′ = (f^{j+1})′/(j+1)`. -/
theorem coeff_neg_one_pow_mul_deriv (c : ℕ → ℂ) (j : ℕ) :
    (qSeriesLaurent c ^ j * qSeriesLaurentDeriv c).coeff (-1) = 0 := by
  have hprod : qSeriesLaurent c ^ j * qSeriesLaurentDeriv c =
      HahnSeries.single (-(j : ℤ) - 2) (-1 : ℂ) *
          HahnSeries.ofPowerSeries ℤ ℂ (qSeriesUnit c ^ (j + 1)) +
        HahnSeries.single (-(j : ℤ) - 1) (1 : ℂ) *
          HahnSeries.ofPowerSeries ℤ ℂ
            (qSeriesUnit c ^ j * PowerSeries.derivative ℂ (qSeriesUnit c)) := by
    have h1 : (HahnSeries.single (-(j : ℤ) - 2) (-1 : ℂ) : LaurentSeries ℂ) =
        HahnSeries.single (-(j : ℤ)) (1 : ℂ) * HahnSeries.single (-2 : ℤ) (-1 : ℂ) := by
      rw [HahnSeries.single_mul_single, one_mul]
      congr 1
    have h2 : (HahnSeries.single (-(j : ℤ) - 1) (1 : ℂ) : LaurentSeries ℂ) =
        HahnSeries.single (-(j : ℤ)) (1 : ℂ) * HahnSeries.single (-1 : ℤ) (1 : ℂ) := by
      rw [HahnSeries.single_mul_single, one_mul]
      congr 1
    rw [qSeriesLaurent_pow, qSeriesLaurentDeriv, h1, h2]
    simp only [map_mul, map_pow]
    ring
  rw [hprod, HahnSeries.coeff_add, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
    show (-1 : ℤ) - (-(j : ℤ) - 2) = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
    show (-1 : ℤ) - (-(j : ℤ) - 1) = ((j : ℕ) : ℤ) by ring,
    HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff]
  set u := qSeriesUnit c
  have hder := congrArg (PowerSeries.coeff j) (PowerSeries.derivative_pow ℂ u (j + 1))
  rw [PowerSeries.coeff_derivative, Nat.add_sub_cancel, mul_assoc] at hder
  rw [show ((j + 1 : ℕ) : PowerSeries ℂ) = PowerSeries.C ((j + 1 : ℕ) : ℂ) by
      rw [map_natCast], PowerSeries.coeff_C_mul] at hder
  have hj : ((j : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  push_cast at hder
  have : PowerSeries.coeff j (u ^ j * PowerSeries.derivative ℂ u) =
      PowerSeries.coeff (j + 1) (u ^ (j + 1)) := by
    apply mul_left_cancel₀ hj
    rw [← hder]
    ring
  rw [this]
  ring

/-- The residue lemma for any polynomial: `[q⁻¹] (P(f) · f′) = 0`. -/
theorem coeff_neg_one_aeval_mul_deriv (c : ℕ → ℂ) (P : ℂ[X]) :
    (aeval (qSeriesLaurent c) P * qSeriesLaurentDeriv c).coeff (-1) = 0 := by
  rw [aeval_eq_sum_range, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Algebra.smul_def, mul_assoc, coeff_algebraMap_mul, coeff_neg_one_pow_mul_deriv, mul_zero]

/-- `F_m(f) − q^{−m}` vanishes below `q¹`. -/
theorem coeff_aeval_faberPoly_sub_of_lt_one (c : ℕ → ℂ) (m : ℕ) {i : ℤ} (hi : i < 1) :
    (aeval (qSeriesLaurent c) (faberPoly c m) - HahnSeries.single (-(m : ℤ)) (1 : ℂ)).coeff i =
      0 := by
  rw [HahnSeries.coeff_sub, coeff_aeval_faberPoly c m (by omega), HahnSeries.coeff_single]
  split_ifs <;> simp

/-- **The coefficient of `q` in `F_m(f)` is `m · c(m)`** for `m ≥ 1`. -/
theorem coeff_one_aeval_faberPoly (c : ℕ → ℂ) {m : ℕ} (hm : 1 ≤ m) :
    (aeval (qSeriesLaurent c) (faberPoly c m)).coeff 1 = m * c m := by
  set F := aeval (qSeriesLaurent c) (faberPoly c m)
  set E := F - HahnSeries.single (-(m : ℤ)) (1 : ℂ)
  set R := qSeriesLaurentDeriv c - HahnSeries.single (-2 : ℤ) (-1 : ℂ)
  have hsplit : F * qSeriesLaurentDeriv c =
      HahnSeries.single (-(m : ℤ)) (1 : ℂ) * qSeriesLaurentDeriv c +
        E * HahnSeries.single (-2 : ℤ) (-1 : ℂ) + E * R := by
    simp only [E, R]
    ring
  have h0 := coeff_neg_one_aeval_mul_deriv c (faberPoly c m)
  change (F * qSeriesLaurentDeriv c).coeff (-1) = 0 at h0
  rw [hsplit, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_mul_single,
    coeff_mul_eq_zero_of_lt (a := 1) (b := 0)
      (fun i hi => coeff_aeval_faberPoly_sub_of_lt_one c m hi)
      (fun j hj => coeff_qSeriesLaurentDeriv_sub_of_neg c hj) (by norm_num),
    show (-1 : ℤ) - -(m : ℤ) = ((m - 1 : ℕ) : ℤ) by omega, coeff_qSeriesLaurentDeriv_natCast,
    show (-1 : ℤ) - (-2) = 1 by norm_num] at h0
  have hE : E.coeff 1 = F.coeff 1 := by
    simp only [E, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    rw [if_neg (by omega), sub_zero]
  rw [hE, Nat.sub_add_cancel hm] at h0
  push_cast [Nat.cast_sub hm] at h0
  linear_combination -h0

/-- **The Faber recursion** (coefficient form of the generating identity in
`Notes/moonshine/MOON_ROUTE.md`):
`F_{n+2} = X F_{n+1} − Σ_{j<n} c(j+1) F_{n−j} − (n+2) c(n+1)`. -/
theorem faberPoly_recursion (c : ℕ → ℂ) (n : ℕ) :
    faberPoly c (n + 2) =
      X * faberPoly c (n + 1) - ∑ j ∈ Finset.range n, C (c (j + 1)) * faberPoly c (n - j) -
        C (((n : ℂ) + 2) * c (n + 1)) := by
  symm
  refine eq_faberPoly_of_coeff c (n + 2) _ fun k hk => ?_
  set Fp := aeval (qSeriesLaurent c) (faberPoly c (n + 1))
  set E := Fp - HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : ℂ)
  set fpos := qSeriesLaurent c - HahnSeries.single (-1 : ℤ) (1 : ℂ) with hfpos_def
  have hfpos : ∀ i : ℤ, i < 1 → fpos.coeff i = 0 := by
    intro i hi
    rw [hfpos_def, HahnSeries.coeff_sub, HahnSeries.coeff_single,
      coeff_qSeriesLaurent_of_lt_one c hi]
    split_ifs <;> simp
  have hsplit : qSeriesLaurent c * Fp =
      HahnSeries.single (-1 : ℤ) (1 : ℂ) * HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : ℂ) +
        HahnSeries.single (-1 : ℤ) (1 : ℂ) * E +
        fpos * HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : ℂ) + fpos * E := by
    simp only [E, fpos]
    ring
  -- the four pieces of `[qᵏ](f · F_{n+1}(f))`
  have hA : (HahnSeries.single (-1 : ℤ) (1 : ℂ) *
      HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : ℂ) : LaurentSeries ℂ).coeff k =
        if k = -((n + 2 : ℕ) : ℤ) then 1 else 0 := by
    rw [HahnSeries.single_mul_single, one_mul, HahnSeries.coeff_single]
    congr 1
    push_cast
    apply propext
    constructor <;> intro h <;> omega
  have hB : (HahnSeries.single (-1 : ℤ) (1 : ℂ) * E).coeff k =
      if k = 0 then ((n : ℂ) + 1) * c (n + 1) else 0 := by
    rw [HahnSeries.coeff_single_mul, one_mul]
    split_ifs with h0
    · subst h0
      simp only [E, HahnSeries.coeff_sub, HahnSeries.coeff_single]
      rw [show (0 : ℤ) - -1 = 1 by norm_num, if_neg (by omega), sub_zero,
        coeff_one_aeval_faberPoly c (by omega : 1 ≤ n + 1)]
      push_cast
      ring
    · exact coeff_aeval_faberPoly_sub_of_lt_one c (n + 1) (by omega)
  have hC : (fpos * HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : ℂ)).coeff k =
      if 1 ≤ k + (n + 1) then c (k + (n + 1)).toNat else 0 := by
    rw [HahnSeries.coeff_mul_single, mul_one, show k - -((n + 1 : ℕ) : ℤ) = k + (n + 1) by
      push_cast; ring]
    split_ifs with h1
    · rw [hfpos_def, HahnSeries.coeff_sub, HahnSeries.coeff_single, if_neg (by omega), sub_zero]
      have := coeff_qSeriesLaurent_natCast c (n := (k + (n + 1)).toNat) (by omega)
      rwa [Int.toNat_of_nonneg (by omega)] at this
    · exact hfpos _ (by omega)
  have hD : (fpos * E).coeff k = 0 :=
    coeff_mul_eq_zero_of_lt (a := 1) (b := 1) hfpos
      (fun i hi => coeff_aeval_faberPoly_sub_of_lt_one c (n + 1) hi) (by omega)
  -- the subtracted sum
  have hS : (aeval (qSeriesLaurent c)
      (∑ j ∈ Finset.range n, C (c (j + 1)) * faberPoly c (n - j))).coeff k =
      if -(n : ℤ) ≤ k ∧ k < 0 then c (k + (n + 1)).toNat else 0 := by
    rw [map_sum, HahnSeries.coeff_sum]
    simp_rw [coeff_aeval_C_mul, coeff_aeval_faberPoly c _ hk]
    split_ifs with hkr
    · rw [Finset.sum_eq_single (k + n).toNat]
      · rw [if_pos (by omega), mul_one]
        congr 1
        omega
      · intro j _ hne
        rw [if_neg (by omega), mul_zero]
      · intro hnot
        exact absurd (Finset.mem_range.mpr (by omega)) hnot
    · refine Finset.sum_eq_zero fun j hj => ?_
      have := Finset.mem_range.mp hj
      rw [if_neg (by omega), mul_zero]
  have hconst : (aeval (qSeriesLaurent c) (C (((n : ℂ) + 2) * c (n + 1)))).coeff k =
      if k = 0 then ((n : ℂ) + 2) * c (n + 1) else 0 := by
    rw [aeval_C, show algebraMap ℂ (LaurentSeries ℂ) (((n : ℂ) + 2) * c (n + 1)) =
      algebraMap ℂ (LaurentSeries ℂ) (((n : ℂ) + 2) * c (n + 1)) * 1 by rw [mul_one],
      coeff_algebraMap_mul, HahnSeries.coeff_one]
    by_cases h : k = 0 <;> simp [h]
  rw [map_sub, map_sub, map_mul, aeval_X, HahnSeries.coeff_sub, HahnSeries.coeff_sub, hS, hconst,
    hsplit, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add, hA, hB, hC, hD]
  push_cast
  -- case analysis on `k ≤ 0`
  rcases lt_or_eq_of_le hk with hneg | hz
  · split_ifs <;> first | (exfalso; omega) | ring
  · subst hz
    simp only [show ((0 : ℤ) + ((n : ℤ) + 1)).toNat = n + 1 by omega]
    split_ifs <;> first | (exfalso; omega) | ring

/-- `G(p) = p (f(p) − X) = 1 − Xp + Σ_{n ≥ 1} c(n) p^{n+1}`, a power series in `p` over `ℂ[X]`. -/
noncomputable def faberGen (c : ℕ → ℂ) : PowerSeries ℂ[X] :=
  PowerSeries.mk fun k => if k = 0 then 1 else if k = 1 then -X else C (c (k - 1))

/-- `H(p) = Σ_{m ≥ 1} F_m(X) pᵐ`. -/
noncomputable def faberSeries (c : ℕ → ℂ) : PowerSeries ℂ[X] :=
  PowerSeries.mk fun m => if m = 0 then 0 else faberPoly c m

/-- **The Faber generating identity** (blueprint: `Notes/moonshine/MOON_ROUTE.md`), in
logarithmic-derivative form:
`p · G′(p) = −G(p) · Σ_{m ≥ 1} F_m(X) pᵐ`, i.e. `log G(p) = −Σ_{m ≥ 1} F_m(X) pᵐ / m`. -/
theorem faberGen_generating (c : ℕ → ℂ) :
    PowerSeries.X * PowerSeries.derivative ℂ[X] (faberGen c) = -(faberGen c * faberSeries c) := by
  refine PowerSeries.ext fun m => ?_
  rw [map_neg, PowerSeries.coeff_mul m (faberGen c) (faberSeries c),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (faberGen c) * PowerSeries.coeff j (faberSeries c))]
  rcases m with _ | _ | n
  · simp [faberSeries]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp [faberGen, faberSeries, Finset.sum_range_succ, faberPoly_one]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, Finset.sum_range_succ',
      Finset.sum_range_succ', Finset.sum_range_succ]
    have hsum : ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) (faberGen c) *
        PowerSeries.coeff (n + 1 + 1 - (i + 1 + 1)) (faberSeries c) =
        ∑ j ∈ Finset.range n, C (c (j + 1)) * faberPoly c (n - j) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.mp hi
      simp only [faberGen, faberSeries, PowerSeries.coeff_mk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show i + 1 + 1 - 1 = i + 1 by omega, show n + 1 + 1 - (i + 1 + 1) = n - i by omega]
    rw [hsum]
    have hr := faberPoly_recursion c n
    simp only [map_mul, map_add, map_natCast, map_ofNat] at hr
    simp [faberGen, faberSeries, hr]
    ring

end VOA.Moonshine.ConwayNorton.M8
