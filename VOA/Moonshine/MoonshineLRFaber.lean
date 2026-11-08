import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Complex.Basic

/-!
# Faber polynomials of a normalised `q`-series

Let `f = q⁻¹ + Σ_{n ≥ 1} c(n) qⁿ`, a Laurent series with zero constant term.  For every `m`
there is a unique polynomial `F_m` such that `F_m(f) − q^{−m}` has only positive powers of
`q`; it is monic of degree `m`.  These are the Faber polynomials of `f`
(blueprint: the Faber polynomial construction in `Notes/moonshine/MOON_ROUTE.md`).

`F_m` is defined by the triangular recursion
`F_m = X^m − Σ_{j < m} [q^{−j}](f^m) · F_j`,
which removes the coefficients of `q^{−m+1}, …, q⁰` of `f^m` one at a time.

Main results:
* `faberPoly_monic`, `faberPoly_natDegree`: `F_m` is monic of degree `m`;
* `coeff_aeval_faberPoly`: for `k ≤ 0`, `[qᵏ] F_m(f) = 1` if `k = −m` and `0` otherwise;
* `eq_faberPoly_of_coeff`: uniqueness.

The coefficient `c 0` is ignored, matching the `qSeriesFun` convention in
`Notes/moonshine/MOON_ROUTE.md`:
`c n` is the coefficient of `qⁿ` for `n ≥ 1`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open Polynomial

/-- The unit part `u = q · f = 1 + Σ_{n ≥ 1} c(n) q^{n+1}` of `f`, as a power series. -/
noncomputable def qSeriesUnit (c : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => if k = 0 then 1 else if k = 1 then 0 else c (k - 1)

/-- The Laurent series `f = q⁻¹ + Σ_{n ≥ 1} c(n) qⁿ`. -/
noncomputable def qSeriesLaurent (c : ℕ → ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-1 : ℤ) (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (qSeriesUnit c)

theorem constantCoeff_qSeriesUnit (c : ℕ → ℂ) : PowerSeries.constantCoeff (qSeriesUnit c) = 1 := by
  simp [qSeriesUnit, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- `f^j = q^{−j} · u^j`. -/
theorem qSeriesLaurent_pow (c : ℕ → ℂ) (j : ℕ) :
    qSeriesLaurent c ^ j =
      HahnSeries.single (-(j : ℤ)) (1 : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (qSeriesUnit c ^ j) := by
  rw [qSeriesLaurent, mul_pow, HahnSeries.single_pow, one_pow,
    ← map_pow (HahnSeries.ofPowerSeries ℤ ℂ)]
  congr 2
  simp

/-- Coefficients of `f^j`: `[qᵏ] f^j = [q^{k+j}] u^j` (zero when `k + j < 0`). -/
theorem coeff_qSeriesLaurent_pow (c : ℕ → ℂ) (j : ℕ) (k : ℤ) :
    (qSeriesLaurent c ^ j).coeff k =
      if k + j < 0 then 0 else PowerSeries.coeff (k + j).natAbs (qSeriesUnit c ^ j) := by
  rw [qSeriesLaurent_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  exact PowerSeries.coeff_coe (R := ℂ) (qSeriesUnit c ^ j) (k + j)

/-- Below and at the pole: `[qᵏ] f^j = [k = −j]` for `k ≤ −j`. -/
theorem coeff_qSeriesLaurent_pow_of_le (c : ℕ → ℂ) (j : ℕ) {k : ℤ} (hk : k ≤ -(j : ℤ)) :
    (qSeriesLaurent c ^ j).coeff k = if k = -(j : ℤ) then 1 else 0 := by
  rw [coeff_qSeriesLaurent_pow]
  rcases lt_or_eq_of_le hk with hlt | heq
  · rw [if_pos (by omega), if_neg (by omega)]
  · subst heq
    rw [if_neg (by omega), if_pos rfl]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_qSeriesUnit]

/-- The Faber polynomials of `f = q⁻¹ + Σ_{n ≥ 1} c(n) qⁿ`:
`F_m = X^m − Σ_{j < m} [q^{−j}](f^m) · F_j`. -/
noncomputable def faberPoly (c : ℕ → ℂ) (m : ℕ) : ℂ[X] :=
  X ^ m - ∑ j : Fin m, C ((qSeriesLaurent c ^ m).coeff (-((j : ℕ) : ℤ))) * faberPoly c j
termination_by m
decreasing_by exact j.isLt

theorem faberPoly_eq (c : ℕ → ℂ) (m : ℕ) :
    faberPoly c m =
      X ^ m - ∑ j : Fin m, C ((qSeriesLaurent c ^ m).coeff (-((j : ℕ) : ℤ))) * faberPoly c j := by
  rw [faberPoly]

theorem faberPoly_zero (c : ℕ → ℂ) : faberPoly c 0 = 1 := by
  rw [faberPoly_eq]
  simp

theorem coeff_algebraMap_mul (a : ℂ) (x : LaurentSeries ℂ) (k : ℤ) :
    (algebraMap ℂ (LaurentSeries ℂ) a * x).coeff k = a * x.coeff k := by
  have h : algebraMap ℂ (LaurentSeries ℂ) a = HahnSeries.single 0 a := by
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  rw [h, HahnSeries.coeff_single_mul, sub_zero]

theorem coeff_aeval_C_mul (c : ℕ → ℂ) (a : ℂ) (P : ℂ[X]) (k : ℤ) :
    (aeval (qSeriesLaurent c) (C a * P)).coeff k = a * (aeval (qSeriesLaurent c) P).coeff k := by
  rw [map_mul, aeval_C, coeff_algebraMap_mul]

/-- `F_m` has degree `m` and is monic. -/
theorem faberPoly_degree_and_monic (c : ℕ → ℂ) (m : ℕ) :
    (faberPoly c m).degree = m ∧ (faberPoly c m).Monic := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hsum : (∑ j : Fin m, C ((qSeriesLaurent c ^ m).coeff (-((j : ℕ) : ℤ))) *
        faberPoly c j).degree < ((X : ℂ[X]) ^ m).degree := by
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j _
      rw [← smul_eq_C_mul]
      refine lt_of_le_of_lt (degree_smul_le _ _) ?_
      rw [(ih j j.isLt).1]
      exact_mod_cast j.isLt
    rw [faberPoly_eq]
    refine ⟨?_, (monic_X_pow m).sub_of_left hsum⟩
    rw [degree_sub_eq_left_of_degree_lt hsum, degree_X_pow]

theorem faberPoly_monic (c : ℕ → ℂ) (m : ℕ) : (faberPoly c m).Monic :=
  (faberPoly_degree_and_monic c m).2

theorem faberPoly_degree (c : ℕ → ℂ) (m : ℕ) : (faberPoly c m).degree = m :=
  (faberPoly_degree_and_monic c m).1

theorem faberPoly_natDegree (c : ℕ → ℂ) (m : ℕ) : (faberPoly c m).natDegree = m :=
  natDegree_eq_of_degree_eq_some (faberPoly_degree c m)

/-- **Characterising property.** For `k ≤ 0`, the coefficient of `qᵏ` in `F_m(f)` is `1` if `k = −m`
and `0` otherwise; i.e. `F_m(f) − q^{−m}` has only positive powers of `q`. -/
theorem coeff_aeval_faberPoly (c : ℕ → ℂ) (m : ℕ) {k : ℤ} (hk : k ≤ 0) :
    (aeval (qSeriesLaurent c) (faberPoly c m)).coeff k = if k = -(m : ℤ) then 1 else 0 := by
  induction m using Nat.strong_induction_on generalizing k with
  | _ m ih =>
    rw [faberPoly_eq, map_sub, map_pow, aeval_X, map_sum, HahnSeries.coeff_sub,
      HahnSeries.coeff_sum]
    simp_rw [coeff_aeval_C_mul]
    have hterm : ∀ j : Fin m,
        (qSeriesLaurent c ^ m).coeff (-((j : ℕ) : ℤ)) *
            (aeval (qSeriesLaurent c) (faberPoly c j)).coeff k =
          if k = -((j : ℕ) : ℤ) then (qSeriesLaurent c ^ m).coeff k else 0 := by
      intro j
      rw [ih j j.isLt hk]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    simp_rw [hterm]
    by_cases hkm : -(m : ℤ) < k
    · -- `k = −j` for exactly one `j < m`, namely `j = −k`.
      have hk' : ((k.natAbs : ℕ) : ℤ) = -k := by omega
      have hj : (k.natAbs : ℕ) < m := by omega
      rw [Finset.sum_eq_single ⟨k.natAbs, hj⟩]
      · rw [if_pos (by rw [hk', neg_neg]), if_neg (by omega), sub_self]
      · intro j _ hne
        rw [if_neg]
        intro h
        apply hne
        ext
        simp only
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · replace hkm : k ≤ -(m : ℤ) := not_lt.mp hkm
      rw [Finset.sum_eq_zero, sub_zero]
      · exact coeff_qSeriesLaurent_pow_of_le c m hkm
      · intro j _
        rw [if_neg]
        have := j.isLt
        omega

/-- The coefficient of `q^{−deg P}` in `P(f)` is the leading coefficient of `P`, and lower
coefficients vanish. -/
theorem coeff_aeval_qSeriesLaurent_of_le (c : ℕ → ℂ) (P : ℂ[X]) {k : ℤ}
    (hk : k ≤ -(P.natDegree : ℤ)) :
    (aeval (qSeriesLaurent c) P).coeff k =
      if k = -(P.natDegree : ℤ) then P.leadingCoeff else 0 := by
  rw [aeval_eq_sum_range, HahnSeries.coeff_sum]
  simp_rw [Algebra.smul_def, coeff_algebraMap_mul]
  rw [Finset.sum_eq_single P.natDegree]
  · rw [coeff_qSeriesLaurent_pow_of_le c _ hk]
    split_ifs
    · rw [mul_one]; rfl
    · rw [mul_zero]
  · intro i hi hne
    have hi' : i < P.natDegree := by
      have := Finset.mem_range.mp hi
      omega
    rw [coeff_qSeriesLaurent_pow_of_le c i (by omega), if_neg (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

/-- A polynomial `P` with `[qᵏ] P(f) = 0` for every `k ≤ 0` is zero. -/
theorem eq_zero_of_coeff_aeval_qSeriesLaurent (c : ℕ → ℂ) (P : ℂ[X])
    (h : ∀ k : ℤ, k ≤ 0 → (aeval (qSeriesLaurent c) P).coeff k = 0) : P = 0 := by
  by_contra hP
  have h0 := h (-(P.natDegree : ℤ)) (by omega)
  rw [coeff_aeval_qSeriesLaurent_of_le c P le_rfl, if_pos rfl] at h0
  exact hP (leadingCoeff_eq_zero.mp h0)

/-- **Uniqueness of Faber polynomials.** If `P(f) − q^{−m}` has only positive powers of `q`, then
`P = F_m`. -/
theorem eq_faberPoly_of_coeff (c : ℕ → ℂ) (m : ℕ) (P : ℂ[X])
    (h : ∀ k : ℤ, k ≤ 0 → (aeval (qSeriesLaurent c) P).coeff k = if k = -(m : ℤ) then 1 else 0) :
    P = faberPoly c m := by
  rw [← sub_eq_zero]
  refine eq_zero_of_coeff_aeval_qSeriesLaurent c _ fun k hk => ?_
  rw [map_sub, HahnSeries.coeff_sub, h k hk, coeff_aeval_faberPoly c m hk, sub_self]

/-- `F_1 = X`: the constant term of `f` is zero. -/
theorem faberPoly_one (c : ℕ → ℂ) : faberPoly c 1 = X := by
  symm
  refine eq_faberPoly_of_coeff c 1 X fun k hk => ?_
  rw [aeval_X]
  have := coeff_qSeriesLaurent_pow c 1 k
  rw [pow_one] at this
  rw [this]
  rcases lt_or_eq_of_le hk with hlt | rfl
  · by_cases hk1 : k = -1
    · subst hk1
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_qSeriesUnit]
    · rw [if_pos (by omega), if_neg (by simpa using hk1)]
  · simp [qSeriesUnit]

end VOA.Moonshine.ConwayNorton.M8
