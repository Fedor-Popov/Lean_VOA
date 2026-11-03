/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkExpansion

/-!
# Serre–Stark S5-7c: the Fricke-expansion residual is a theorem

`serreStarkFrickeBeta24 : SerreStarkFrickeBeta24`, hence (with `serreStarkOddVanish24`)
`serreStarkLevelBox24 : SerreStarkLevelBox24`.

Assembly: `fricke_LSeries_eq` (both functional equations), `Fs_mul_prod_eq` and
`prod_tildeE_eq_LSeries` (expansion of the resolvent factors), `LFunction_changeLevel`, the
constant bookkeeping `pref_Y` (`Pref(z) ∏_p p^{2 L₀ z} = K D₀^z`), and uniqueness of Dirichlet
coefficients (`LSeries.eq_of_LSeries_eventually_eq`, after the twist `n^{−i}`).
-/

open Complex Filter Topology ArithmeticFunction
open scoped UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

namespace ClassSetup

variable (S : ClassSetup)

/-! ## The constants -/

/-- `M₀ = ∏_p p^{L₀}`. -/
def M0 : ℕ := ∏ p : S.ι, p.1 ^ S.L0

theorem M0_pos : 0 < S.M0 :=
  Finset.prod_pos fun p _ => pow_pos (S.prime p).pos _

theorem N_dvd_M0_sq : S.N ∣ S.M0 ^ 2 := by
  have hM : S.M0 ^ 2 ≠ 0 := pow_ne_zero _ S.M0_pos.ne'
  rw [← Nat.factorization_le_iff_dvd S.hN.ne' hM]
  intro q
  by_cases hq : q ∈ S.N.primeFactors
  · have hqp := Nat.prime_of_mem_primeFactors hq
    have h1 : (S.M0 ^ 2).factorization q = 2 * S.L0 := by
      rw [Nat.factorization_pow, M0, Nat.factorization_prod fun p _ =>
        pow_ne_zero _ (S.prime p).ne_zero]
      simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single ⟨q, hq⟩]
      · rw [hqp.factorization_pow, Finsupp.single_eq_same]
      · intro b _ hb
        rw [(S.prime b).factorization_pow, Finsupp.single_apply, if_neg]
        intro h; exact hb (Subtype.ext h)
      · simp
    rw [h1]
    -- `v_q(N) < N ≤ L₀`
    have h2 : S.N.factorization q < S.N := by
      have := Nat.factorization_lt q S.hN.ne'
      exact this
    have h3 : S.N ≤ S.L0 := by unfold L0; omega
    omega
  · have : S.N.factorization q = 0 :=
      Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    rw [this]; exact Nat.zero_le _

/-- `D₀ = 4 t r² M₀² / N` (an integer). -/
def D0 : ℕ := 4 * S.t * S.r ^ 2 * S.M0 ^ 2 / S.N

theorem D0_mul_N : S.D0 * S.N = 4 * S.t * S.r ^ 2 * S.M0 ^ 2 :=
  Nat.div_mul_cancel (dvd_mul_of_dvd_right S.N_dvd_M0_sq _)

theorem r_pos : 0 < S.r := Nat.pos_of_ne_zero fun h => by
  have := S.hrN; rw [h] at this; exact S.hN.ne' (Nat.eq_zero_of_zero_dvd this)

theorem t_pos : 0 < S.t := Nat.pos_of_ne_zero S.ht.ne_zero

theorem D0_pos : 0 < S.D0 := by
  have h := S.D0_mul_N
  have hpos : 0 < 4 * S.t * S.r ^ 2 * S.M0 ^ 2 := by
    have := S.t_pos; have := S.r_pos; have := S.M0_pos; positivity
  rcases Nat.eq_zero_or_pos S.D0 with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

/-! ## `Pref(z) ∏_p p^{2 L₀ z} = K D₀^z` -/

theorem cpow_ofReal_eq_exp {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ((a : ℂ)) ^ w = exp (w * (Real.log a : ℂ)) := by
  rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 ha.ne'), ← Complex.ofReal_log ha.le, mul_comm]

theorem cpow_natCast_eq_exp {n : ℕ} (hn : 0 < n) (w : ℂ) :
    ((n : ℂ)) ^ w = exp (w * (Real.log n : ℂ)) := by
  have := cpow_ofReal_eq_exp (a := (n : ℝ)) (by exact_mod_cast hn) w
  simpa using this

/-- The exponent of `Pref(z) ∏_p p^{2 L₀ z}`. -/
def Aexp (z : ℂ) : ℂ :=
  z * Real.log (feScale S.N) + (-(1 / 2 - z)) * Real.log (feScale S.N) +
    (-(1 / 2 - z)) * Real.log S.t + (2 * z - 1 / 2) * Real.log S.r +
    (-(2 * z) / 2) * Real.log Real.pi - (-(1 - 2 * z) / 2) * Real.log Real.pi +
    ∑ p : S.ι, (-(S.L0 : ℂ)) * (-(2 * z) * Real.log p.1)

theorem pref_Y_exp (z : ℂ) :
    S.Pref z * ∏ p : S.ι, (S.yv p z) ^ (-(S.L0 : ℤ)) =
      (feRoot S.N)⁻¹ * DirichletCharacter.rootNumber S.ψ * exp (S.Aexp z) := by
  have hc := feScale_pos S.hN
  have hY : ∏ p : S.ι, (S.yv p z) ^ (-(S.L0 : ℤ)) =
      exp (∑ p : S.ι, (-(S.L0 : ℂ)) * (-(2 * z) * Real.log p.1)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [yv, cpow_natCast_eq_exp (S.prime p).pos, ← Complex.exp_int_mul]
    push_cast; ring_nf
  rw [hY, Pref, cpow_ofReal_eq_exp hc, cpow_ofReal_eq_exp hc,
    cpow_natCast_eq_exp S.t_pos, cpow_natCast_eq_exp S.r_pos,
    cpow_ofReal_eq_exp Real.pi_pos, cpow_ofReal_eq_exp Real.pi_pos, Aexp]
  simp only [Complex.exp_add, Complex.exp_sub]
  field_simp

/-- The logarithmic identity behind `pref_Y`. -/
theorem log_identity :
    2 * Real.log (feScale S.N) + Real.log S.t + 2 * Real.log S.r - 2 * Real.log Real.pi +
      2 * (S.L0 : ℝ) * ∑ p : S.ι, Real.log p.1 = Real.log S.D0 := by
  have hN : (0 : ℝ) < S.N := by exact_mod_cast S.hN
  have ht : (0 : ℝ) < S.t := by exact_mod_cast S.t_pos
  have hr : (0 : ℝ) < S.r := by exact_mod_cast S.r_pos
  have hM : (0 : ℝ) < S.M0 := by exact_mod_cast S.M0_pos
  have hD : (S.D0 : ℝ) = 4 * S.t * S.r ^ 2 * S.M0 ^ 2 / S.N := by
    rw [eq_div_iff hN.ne']
    exact_mod_cast S.D0_mul_N
  have hlogM : Real.log S.M0 = (S.L0 : ℝ) * ∑ p : S.ι, Real.log p.1 := by
    rw [M0, Nat.cast_prod, Real.log_prod (fun p _ => by
      have := (S.prime p).pos; positivity), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hc : Real.log (feScale S.N) = Real.log 2 + Real.log Real.pi - Real.log S.N / 2 := by
    rw [feScale, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num)
      Real.pi_ne_zero, Real.log_sqrt hN.le]
  rw [hD, Real.log_div (by positivity) hN.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) ht.ne',
    Real.log_pow, Real.log_pow, hlogM, hc, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The constant `K`. -/
def Kc : ℂ := S.Pref 0 * ∏ p : S.ι, (S.yv p 0) ^ (-(S.L0 : ℤ))

/-- `Pref(z) ∏_p y_p^{−L₀} = K D₀^z`. -/
theorem pref_Y (z : ℂ) :
    S.Pref z * ∏ p : S.ι, (S.yv p z) ^ (-(S.L0 : ℤ)) = S.Kc * (S.D0 : ℂ) ^ z := by
  have hsum : ∀ w : ℂ, (∑ p : S.ι, (-(S.L0 : ℂ)) * (-(2 * w) * (Real.log p.1 : ℂ))) =
      2 * (S.L0 : ℂ) * w * ∑ p : S.ι, (Real.log p.1 : ℂ) := by
    intro w; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
  have hA : S.Aexp z = S.Aexp 0 + z * (Real.log S.D0 : ℂ) := by
    have hl := S.log_identity
    have hl' : ((Real.log S.D0 : ℝ) : ℂ) = 2 * (Real.log (feScale S.N) : ℂ) +
        (Real.log S.t : ℂ) + 2 * (Real.log S.r : ℂ) - 2 * (Real.log Real.pi : ℂ) +
        2 * (S.L0 : ℂ) * ∑ p : S.ι, (Real.log p.1 : ℂ) := by
      rw [← hl]; push_cast; ring
    rw [hl', Aexp, Aexp, hsum, hsum]
    ring
  rw [Kc, pref_Y_exp, pref_Y_exp, cpow_natCast_eq_exp S.D0_pos, hA, Complex.exp_add]
  ring

/-! ## `K ≠ 0` -/

theorem rootNumber_ne_zero (hprim : S.ψ.IsPrimitive) :
    DirichletCharacter.rootNumber S.ψ ≠ 0 := by
  intro h0
  have hFE := hprim.completedLFunction_one_sub (-1 : ℂ)
  rw [h0, mul_zero, zero_mul, show (1 : ℂ) - -1 = 2 by norm_num] at hFE
  have hL := DirichletCharacter.LFunction_ne_zero_of_one_le_re S.ψ (s := 2)
    (Or.inr (by norm_num)) (by norm_num)
  have hgam : DirichletCharacter.gammaFactor S.ψ 2 ≠ 0 := by
    rcases S.ψ.even_or_odd with he | ho
    · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by norm_num)
    · rw [ho.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by norm_num)
  apply hL
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (Or.inl two_ne_zero), hFE,
    zero_div]

theorem Kc_ne_zero (hprim : S.ψ.IsPrimitive) : S.Kc ≠ 0 := by
  rw [Kc, pref_Y_exp]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (feRoot_ne_zero S.hN)) (S.rootNumber_ne_zero hprim))
    (Complex.exp_ne_zero _)

/-! ## The Euler polynomial `E'(z) = ∏_p (1 − ψ̄(p) p^{−2z})` -/

/-- The point mass at `k`. -/
def dltAF (k : ℕ) : ArithmeticFunction ℂ := ⟨fun n => if n = k ∧ n ≠ 0 then 1 else 0, by simp⟩

theorem LSeriesHasSum_dltAF {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    LSeriesHasSum (dltAF k) z ((k : ℂ) ^ (-z)) := by
  unfold LSeriesHasSum
  have : (k : ℂ) ^ (-z) = LSeries.term (dltAF k) z k := by
    rw [LSeries.term_of_ne_zero hk]
    simp [dltAF, hk, cpow_neg]
  rw [this]
  refine hasSum_single k fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero h0.ne']
    simp [dltAF, hn]

/-- One Euler factor `1 − c δ_k`. -/
def eulAF (c : ℂ) (k : ℕ) : ArithmeticFunction ℂ := 1 - c • dltAF k

theorem LSeriesHasSum_eulAF (c : ℂ) {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    LSeriesHasSum (eulAF c k) z (1 - c * (k : ℂ) ^ (-z)) := by
  have h1 : LSeriesHasSum ⇑(1 : ArithmeticFunction ℂ) z 1 := by
    have := (LSeriesSummable_one_AF z).LSeriesHasSum
    rw [coe_one_AF, LSeries_delta] at this
    rw [coe_one_AF]; simpa using this
  have h2 := (LSeriesHasSum_dltAF hk z).smul c
  unfold eulAF
  have := h1.sub h2
  simpa [smul_eq_mul] using this

/-- `e' = ∏_p (1 − ψ̄(p) δ_{p²})`. -/
def eAF : ArithmeticFunction ℂ := ∏ p : S.ι, eulAF (S.ψ⁻¹ p.1) (p.1 ^ 2)

theorem eAF_LSeries (z : ℂ) : LSeriesSummable (S.eAF) z ∧
    LSeries (S.eAF) z = ∏ q ∈ S.N.primeFactors, (1 - S.ψ⁻¹ q * (q : ℂ) ^ (-(2 * z))) := by
  have hp : ∀ p : S.ι, LSeriesHasSum (eulAF (S.ψ⁻¹ p.1) (p.1 ^ 2)) z
      (1 - S.ψ⁻¹ p.1 * ((p.1 ^ 2 : ℕ) : ℂ) ^ (-z)) :=
    fun p => LSeriesHasSum_eulAF _ (pow_ne_zero _ (S.prime p).ne_zero) z
  obtain ⟨h1, h2⟩ := LSeries_prod_AF Finset.univ (fun p : S.ι => eulAF (S.ψ⁻¹ p.1) (p.1 ^ 2)) z
    (fun p _ => (hp p).LSeriesSummable)
  refine ⟨h1, ?_⟩
  rw [eAF, h2, ← Finset.prod_coe_sort S.N.primeFactors]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [(hp p).LSeries_eq, Nat.cast_pow, ← natCast_cpow_natCast_mul]
  congr 3; ring

/-! ## The main identity -/

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- For `Re z` large, `1/2 − z` is good. -/
theorem eventually_good_half_sub_re : ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → S.Good (1 / 2 - z) := by
  classical
  have hp : ∀ p : S.ι, ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re →
      IsUnit (1 - ((p.1 : ℂ) ^ (-(2 * (1 / 2 - z)))) • S.Mp p) := by
    intro p
    set R := (Matrix.charpolyRev (S.Mp p)).roots.toFinset
    set B : ℝ := ∑ x ∈ R, ‖x‖ + 1
    have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast (S.prime p).one_lt
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt B hp1
    refine ⟨K + 1, fun z hz => ?_⟩
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← eval_charpolyRev_eq_det]
    intro hroot
    set x := (p.1 : ℂ) ^ (-(2 * (1 / 2 - z)))
    have hmem : x ∈ R := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots]
      · exact hroot
      · intro h0
        have := congrArg (Polynomial.eval 0) h0
        rw [Matrix.eval_charpolyRev, Polynomial.eval_zero] at this
        exact one_ne_zero this
    have hle : ‖x‖ ≤ ∑ x ∈ R, ‖x‖ :=
      Finset.single_le_sum (f := fun x => ‖x‖) (fun _ _ => norm_nonneg _) hmem
    have hnorm : ‖x‖ = (p.1 : ℝ) ^ (2 * z.re - 1) := by
      rw [Complex.norm_natCast_cpow_of_pos (S.prime p).pos]
      congr 1
      simp; ring
    have hbig : (p.1 : ℝ) ^ K ≤ (p.1 : ℝ) ^ (2 * z.re - 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hp1.le (by
        have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        linarith)
    linarith
  choose X hX using hp
  refine ⟨∑ p, |X p|, fun z hz => S.good_of_isUnit_Mp fun p => hX p z ?_⟩
  exact le_trans (le_trans (le_abs_self _) (Finset.single_le_sum (f := fun p => |X p|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ p))) hz

/-- `ψ̄^{(N)}` as a Dirichlet character mod `N`. -/
def χNbar : DirichletCharacter ℂ S.N := DirichletCharacter.changeLevel S.hrN S.ψ⁻¹

/-- `ψ̄^{(N)}` as a function on `ℕ`. -/
def χbar (v : ℕ) : ℂ := S.χNbar (v : ZMod S.N)

theorem χbar_one : S.χbar 1 = 1 := by simp [χbar]

theorem χbar_coprime (v : ℕ) (h : S.χbar v ≠ 0) : v.Coprime S.N := by
  by_contra hv
  apply h
  rw [χbar, MulChar.map_nonunit]
  rwa [ZMod.isUnit_iff_coprime]

variable {f : ℂ → ℂ} (hf : IsClassForm S.N S.r S.ψ S.t f)

/-- **The main identity.** For `Re z` large with `Im z = 1`,
`L(dil_{D₀}(e' ⋆ b), z) = K · L(H_g ⋆ ψ̄^{(N)}(√·), z)`, `b` the coefficients of `W f`. -/
theorem main_identity (hprim : S.ψ.IsPrimitive) (hev : S.ψ.Even) :
    ∃ X : ℝ, ∀ z : ℂ, X ≤ z.re → z.im = 1 →
      LSeriesSummable ⇑(S.eAF * toArithmeticFunction (thetaTypeCoeff (fricke S.N f))) z ∧
      LSeriesSummable ⇑(toArithmeticFunction (S.Hf (S.gf hf)) * sqAF S.χbar) z ∧
      LSeries (dil S.D0 ⇑(S.eAF * toArithmeticFunction (thetaTypeCoeff (fricke S.N f)))) z =
        S.Kc * LSeries ⇑(toArithmeticFunction (S.Hf (S.gf hf)) * sqAF S.χbar) z := by
  obtain ⟨X1, hX1⟩ := S.Fs_mul_prod_eq
  obtain ⟨X2, hX2⟩ := S.prod_tildeE_eq_LSeries
  obtain ⟨X3, hX3⟩ := S.eventually_good_half_sub_re
  refine ⟨max (max X1 X2) (max X3 2), fun z hz hzi => ?_⟩
  have hz1 : X1 ≤ z.re := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hz2 : X2 ≤ z.re := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hz3 : X3 ≤ z.re := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hz
  have hz4 : 2 ≤ z.re := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hz
  set g := S.gf hf
  set b := thetaTypeCoeff (fricke S.N f)
  have hgood := hX3 z hz3
  have hW := isThetaTypeForm_fricke S.hN S.h24 hf.1
  -- summabilities
  have hbs : LSeriesSummable b z := lseriesSummable_thetaType S.h4 S.hN hW (by linarith)
  have hBs : LSeriesSummable ⇑(toArithmeticFunction b) z := by
    refine (LSeriesSummable_congr z fun {n} hn => ?_).2 hbs
    simp [toArithmeticFunction, hn]
  have hLB : LSeries ⇑(toArithmeticFunction b) z = LSeries b z :=
    LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) z
  obtain ⟨hes, hel⟩ := S.eAF_LSeries z
  obtain ⟨hHs, hH⟩ := hX2 z hz2 g
  have hHAs : LSeriesSummable ⇑(toArithmeticFunction (S.Hf g)) z := by
    refine (LSeriesSummable_congr z fun {n} hn => ?_).2 hHs
    simp [toArithmeticFunction, hn]
  have hLH : LSeries ⇑(toArithmeticFunction (S.Hf g)) z = LSeries (S.Hf g) z :=
    LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) z
  have h2z : 1 < (2 * z).re := by rw [mul_re]; simp; linarith
  have hχs : LSeriesSummable S.χbar (2 * z) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re S.χNbar h2z
  have hsqs : LSeriesSummable ⇑(sqAF S.χbar) z := LSeriesSummable_sqAF hχs
  refine ⟨LSeriesSummable_mul hes hBs, LSeriesSummable_mul hHAs hsqs, ?_⟩
  -- assemble
  have hFE := S.fricke_LSeries_eq hf hprim hev (z := z) (by linarith) (by rw [hzi]; norm_num)
    hgood
  rw [hX1 z hz1 hgood g, hH] at hFE
  have hCL := DirichletCharacter.LFunction_changeLevel S.hrN S.ψ⁻¹ (s := 2 * z)
    (Or.inr (fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith))
  rw [show DirichletCharacter.changeLevel S.hrN S.ψ⁻¹ = S.χNbar from rfl,
    DirichletCharacter.LFunction_eq_LSeries _ h2z] at hCL
  have hsq : LSeries ⇑(sqAF S.χbar) z = LSeries (fun n : ℕ => S.χNbar n) (2 * z) :=
    LSeries_sqAF _ z
  have hD0 : (S.D0 : ℂ) ^ (-z) * (S.D0 : ℂ) ^ z = 1 := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.2 S.D0_pos.ne'), neg_add_cancel, cpow_zero]
  rw [LSeries_dil S.D0_pos, LSeries_mul' hes hBs, LSeries_mul' hHAs hsqs, hLB, hLH, hel, hFE,
    hsq, hCL]
  have hPY := S.pref_Y z
  set E' := ∏ q ∈ S.N.primeFactors, (1 - S.ψ⁻¹ q * (q : ℂ) ^ (-(2 * z)))
  set Lψ := DirichletCharacter.LFunction S.ψ⁻¹ (2 * z)
  set LH := LSeries (S.Hf g) z
  linear_combination ((S.D0 : ℂ) ^ (-z) * E' * LH * Lψ) * hPY + (S.Kc * E' * LH * Lψ) * hD0

/-- **Coefficient identity** (uniqueness of Dirichlet coefficients). -/
theorem coeff_identity (hprim : S.ψ.IsPrimitive) (hev : S.ψ.Even) {n : ℕ} (hn : n ≠ 0) :
    dil S.D0 ⇑(S.eAF * toArithmeticFunction (thetaTypeCoeff (fricke S.N f))) n =
      S.Kc * (toArithmeticFunction (S.Hf (S.gf hf)) * sqAF S.χbar) n := by
  obtain ⟨X, hX⟩ := S.main_identity hf hprim hev
  set F1 := dil S.D0 ⇑(S.eAF * toArithmeticFunction (thetaTypeCoeff (fricke S.N f)))
  set F2 : ℕ → ℂ := S.Kc • ⇑(toArithmeticFunction (S.Hf (S.gf hf)) * sqAF S.χbar)
  have hz : ∀ x : ℝ, X ≤ x → X ≤ ((x : ℂ) + Complex.I).re ∧ ((x : ℂ) + Complex.I).im = 1 :=
    fun x hx => ⟨by simpa using hx, by simp⟩
  have heq : ∀ x : ℝ, X ≤ x → LSeries (twI F1) x = LSeries (twI F2) x := by
    intro x hx
    obtain ⟨-, -, h⟩ := hX _ (hz x hx).1 (hz x hx).2
    rw [LSeries_twI, LSeries_twI, h, LSeries_smul]
  have hF1 : LSeries.abscissaOfAbsConv (twI F1) < ⊤ := by
    obtain ⟨h1, -, -⟩ := hX _ (hz X le_rfl).1 (hz X le_rfl).2
    have : LSeriesSummable (twI F1) (X : ℂ) :=
      LSeriesSummable_twI.2 (LSeriesSummable_dil S.D0_pos h1)
    exact lt_of_le_of_lt (by simpa using this.abscissaOfAbsConv_le) (by simp)
  have hF2 : LSeries.abscissaOfAbsConv (twI F2) < ⊤ := by
    obtain ⟨-, h2, -⟩ := hX _ (hz X le_rfl).1 (hz X le_rfl).2
    have : LSeriesSummable (twI F2) (X : ℂ) := LSeriesSummable_twI.2 (h2.smul _)
    exact lt_of_le_of_lt (by simpa using this.abscissaOfAbsConv_le) (by simp)
  have hev' : (fun x : ℝ => LSeries (twI F1) x) =ᶠ[atTop] fun x : ℝ => LSeries (twI F2) x := by
    filter_upwards [eventually_ge_atTop X] with x hx using heq x hx
  have h := LSeries.eq_of_LSeries_eventually_eq hF1 hF2 hev' hn
  unfold twI at h
  have hne : (n : ℂ) ^ (-Complex.I) ≠ 0 :=
    cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 hn))
  have := mul_right_cancel₀ hne h
  simpa [F2] using this

/-! ## Valuations -/

theorem prod_pow_factorization (k : S.ι → ℕ) (p : S.ι) :
    (∏ q : S.ι, q.1 ^ k q).factorization p.1 = k p := by
  rw [Nat.factorization_prod fun q _ => pow_ne_zero _ (S.prime q).ne_zero,
    Finsupp.finsetSum_apply, Finset.sum_eq_single p]
  · rw [(S.prime p).factorization_pow, Finsupp.single_eq_same]
  · intro q _ hq
    rw [(S.prime q).factorization_pow, Finsupp.single_apply, if_neg]
    intro h; exact hq (Subtype.ext h)
  · simp

theorem M0_factorization (p : S.ι) : S.M0.factorization p.1 = S.L0 :=
  S.prod_pow_factorization (fun _ => S.L0) p

theorem D0_factorization (p : S.ι) :
    S.D0.factorization p.1 + S.N.factorization p.1 =
      (4 * S.t * S.r ^ 2).factorization p.1 + 2 * S.L0 := by
  have h := congrArg (fun n => n.factorization p.1) S.D0_mul_N
  simp only at h
  have hX0 : 4 * S.t * S.r ^ 2 ≠ 0 := by have := S.t_pos; have := S.r_pos; positivity
  rw [Nat.factorization_mul S.D0_pos.ne' S.hN.ne',
    Nat.factorization_mul hX0 (pow_ne_zero _ S.M0_pos.ne'), Finsupp.add_apply,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    S.M0_factorization] at h
  omega

/-! ## The coefficient bound for `e' ⋆ b` -/

include hf in
theorem eAFB_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    ‖(S.eAF * toArithmeticFunction (thetaTypeCoeff (fricke S.N f))) n‖ ≤
      C * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hW := isThetaTypeForm_fricke S.hN S.h24 hf.1
  set b := thetaTypeCoeff (fricke S.N f)
  obtain ⟨C0, hC0, hb⟩ := norm_coeff_sq_le S.h4 S.hN hW
  set Cb := Real.sqrt C0 + ‖b 1‖ + ‖b 2‖ + ‖b 3‖ with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hbb : ∀ m : ℕ, 1 ≤ m → ‖b m‖ ≤ Cb * (m : ℝ) ^ (1 / 4 : ℝ) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
    by_cases h4 : 4 ≤ m
    · have h := hb m h4
      have hsq : ‖b m‖ ≤ Real.sqrt C0 * (m : ℝ) ^ (1 / 4 : ℝ) := by
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have e1 : Real.sqrt (Real.sqrt m) = (m : ℝ) ^ (1 / 4 : ℝ) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hm0]; norm_num
        calc ‖b m‖ = Real.sqrt (‖b m‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (C0 * Real.sqrt m) := Real.sqrt_le_sqrt h
          _ = Real.sqrt C0 * (m : ℝ) ^ (1 / 4 : ℝ) := by rw [Real.sqrt_mul hC0, e1]
      calc ‖b m‖ ≤ Real.sqrt C0 * (m : ℝ) ^ (1 / 4 : ℝ) := hsq
        _ ≤ Cb * (m : ℝ) ^ (1 / 4 : ℝ) := by
          gcongr; simp only [hCb]; have := norm_nonneg (b 1); have := norm_nonneg (b 2)
          have := norm_nonneg (b 3); linarith
    · have hle : ‖b m‖ ≤ Cb := by
        interval_cases m
        · simp only [hCb]; have := Real.sqrt_nonneg C0; have := norm_nonneg (b 2)
          have := norm_nonneg (b 3); linarith
        · simp only [hCb]; have := Real.sqrt_nonneg C0; have := norm_nonneg (b 1)
          have := norm_nonneg (b 3); linarith
        · simp only [hCb]; have := Real.sqrt_nonneg C0; have := norm_nonneg (b 1)
          have := norm_nonneg (b 2); linarith
      calc ‖b m‖ ≤ Cb := hle
        _ = Cb * 1 := (mul_one _).symm
        _ ≤ Cb * (m : ℝ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hm1 hCb0
  -- summability of `e'`
  have hes := (S.eAF_LSeries 0).1
  have hsum : Summable fun d : ℕ => ‖S.eAF d‖ := by
    have h1 : Summable fun d : ℕ => ‖LSeries.term (S.eAF) 0 d‖ := hes.norm
    refine h1.congr fun d => ?_
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero h0.ne', cpow_zero, div_one]
  set Ce := ∑' d : ℕ, ‖S.eAF d‖
  have hCe0 : 0 ≤ Ce := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨Cb * Ce, mul_nonneg hCb0 hCe0, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnq : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  rw [ArithmeticFunction.mul_apply]
  calc ‖∑ x ∈ n.divisorsAntidiagonal, S.eAF x.1 * toArithmeticFunction b x.2‖
      ≤ ∑ x ∈ n.divisorsAntidiagonal, ‖S.eAF x.1‖ * (Cb * (n : ℝ) ^ (1 / 4 : ℝ)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
        rw [Nat.mem_divisorsAntidiagonal] at hx
        have hx2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hx; exact hn0 hx.1.symm
        have hx2n : x.2 ≤ n := Nat.le_of_dvd (by omega) ⟨x.1, by rw [← hx.1]; ring⟩
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have : toArithmeticFunction b x.2 = b x.2 := by simp [toArithmeticFunction, hx2]
        rw [this]
        calc ‖b x.2‖ ≤ Cb * (x.2 : ℝ) ^ (1 / 4 : ℝ) := hbb x.2 (by omega)
          _ ≤ Cb * (n : ℝ) ^ (1 / 4 : ℝ) := by
            gcongr
    _ = (∑ d ∈ n.divisors, ‖S.eAF d‖) * (Cb * (n : ℝ) ^ (1 / 4 : ℝ)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact Nat.sum_divisorsAntidiagonal (fun d _ => ‖S.eAF d‖)
    _ ≤ Ce * (Cb * (n : ℝ) ^ (1 / 4 : ℝ)) := by
        gcongr
        exact hsum.sum_le_tsum _ fun _ _ => norm_nonneg _
    _ = Cb * Ce * (n : ℝ) ^ (1 / 4 : ℝ) := by ring

/-! ## Conclusion -/

theorem smooth_prod (k : S.ι → ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime) (h : ℓ ∣ ∏ p : S.ι, p.1 ^ k p) :
    ℓ ∣ S.N := by
  obtain ⟨p, -, hp⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 h
  have := (Nat.prime_dvd_prime_iff_eq hℓ (S.prime p)).1 (hℓ.dvd_of_dvd_pow hp)
  rw [this]; exact S.dvd p

theorem key_beta (hprim : S.ψ.IsPrimitive) (hev : S.ψ.Even) {m : S.ι → ℤ}
    (hm : ∀ p, -(S.L0 : ℤ) ≤ m p) :
    S.Kc * S.beta (S.gf hf) m =
      dil S.D0 ⇑(S.eAF * toArithmeticFunction (thetaTypeCoeff (fricke S.N f)))
        (∏ p : S.ι, p.1 ^ (2 * (m p + S.L0).toNat)) := by
  set k : S.ι → ℕ := fun p => (m p + S.L0).toNat
  have hmk : (fun p => (k p : ℤ) - S.L0) = m := by
    funext p; have := hm p; simp only [k]; omega
  have hn0 : (∏ p : S.ι, p.1 ^ (2 * k p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ (S.prime p).ne_zero
  rw [S.coeff_identity hf hprim hev hn0, mul_sqAF_smooth S.χbar_one S.χbar_coprime _ hn0
    (fun ℓ hℓ h => S.smooth_prod (fun p => 2 * k p) ℓ hℓ h)]
  rw [show toArithmeticFunction (S.Hf (S.gf hf)) (∏ p : S.ι, p.1 ^ (2 * k p)) =
    S.Hf (S.gf hf) (∏ p : S.ι, p.1 ^ (2 * k p)) from if_neg hn0, S.Hf_apply_pow, hmk]

theorem rpow_quarter_eq {m : S.ι → ℤ} (hm : ∀ p, -(S.L0 : ℤ) ≤ m p) {n' : ℕ}
    (hn' : S.D0 * n' = ∏ p : S.ι, p.1 ^ (2 * (m p + S.L0).toNat)) :
    (n' : ℝ) ^ (1 / 4 : ℝ) = ((S.N : ℝ) / (4 * S.t * S.r ^ 2)) ^ (1 / 4 : ℝ) *
      ∏ p : S.ι, Real.sqrt p.1 ^ (m p) := by
  set u := ∏ p : S.ι, Real.sqrt p.1 ^ (m p) with hu
  have hsp : ∀ p : S.ι, 0 < Real.sqrt p.1 := fun p =>
    Real.sqrt_pos.2 (by exact_mod_cast (S.prime p).pos)
  have hu0 : 0 < u := Finset.prod_pos fun p _ => zpow_pos (hsp p) _
  have hN : (0 : ℝ) < S.N := by exact_mod_cast S.hN
  have ht : (0 : ℝ) < S.t := by exact_mod_cast S.t_pos
  have hr : (0 : ℝ) < S.r := by exact_mod_cast S.r_pos
  have hM : (0 : ℝ) < S.M0 := by exact_mod_cast S.M0_pos
  -- `n = M₀² u⁴`
  have hfac : ∀ p : S.ι, (((p.1 ^ (2 * (m p + S.L0).toNat) : ℕ)) : ℝ) =
      (p.1 : ℝ) ^ (2 * S.L0) * ((Real.sqrt p.1) ^ (m p)) ^ 4 := by
    intro p
    have hp0 : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (S.prime p).ne_zero
    have hk : (((m p + S.L0).toNat : ℕ) : ℤ) = m p + S.L0 := by have := hm p; omega
    have e1 : ((Real.sqrt p.1) ^ (m p)) ^ 4 = (p.1 : ℝ) ^ (2 * m p) := by
      rw [← zpow_natCast, ← zpow_mul, show m p * ((4 : ℕ) : ℤ) = 2 * (2 * m p) by push_cast; ring,
        zpow_mul, show (Real.sqrt p.1) ^ (2 : ℤ) = p.1 by
          rw [zpow_two, Real.mul_self_sqrt (Nat.cast_nonneg _)]]
    rw [e1, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast (p.1 : ℝ) (2 * S.L0), ← zpow_add₀ hp0]
    congr 1
    push_cast [hk]
    ring
  have hn : ((∏ p : S.ι, p.1 ^ (2 * (m p + S.L0).toNat) : ℕ) : ℝ) = (S.M0 : ℝ) ^ 2 * u ^ 4 := by
    have hM2 : (∏ p : S.ι, (p.1 : ℝ) ^ (2 * S.L0)) = (S.M0 : ℝ) ^ 2 := by
      rw [M0, Nat.cast_prod, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [Nat.cast_pow, ← pow_mul, mul_comm]
    rw [Nat.cast_prod]
    simp_rw [hfac]
    rw [Finset.prod_mul_distrib, hM2, hu, Finset.prod_pow]
  have hD : (S.D0 : ℝ) = 4 * S.t * S.r ^ 2 * S.M0 ^ 2 / S.N := by
    rw [eq_div_iff hN.ne']; exact_mod_cast S.D0_mul_N
  have hn'r : (n' : ℝ) = (S.N : ℝ) / (4 * S.t * S.r ^ 2) * u ^ 4 := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hn'
    simp only [Nat.cast_mul] at h
    rw [hn, hD] at h
    field_simp at h ⊢
    linarith [h]
  rw [hn'r, Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hu0.le (by norm_num)

/-- **The Fricke-expansion bounds hold** for every class form (ψ primitive and even). -/
theorem frickeBeta_holds (hprim : S.ψ.IsPrimitive) (hev : S.ψ.Even) (g : S.V) :
    S.BetaBound g ∧ S.BetaIntegral g := by
  obtain ⟨f, hf, hfg⟩ := g.2
  have hg : g = S.gf hf := Subtype.ext hfg.symm
  rw [hg]
  obtain ⟨C, hC0, hC⟩ := S.eAFB_bound hf
  have hK := S.Kc_ne_zero hprim
  have hzero : ∀ m : S.ι → ℤ, (¬ ∀ p, -(S.L0 : ℤ) ≤ m p) → S.beta (S.gf hf) m = 0 := by
    intro m hm
    push Not at hm
    obtain ⟨p, hp⟩ := hm
    rw [beta_eq_sum]
    refine Finset.sum_eq_zero fun J _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ p) (S.cco_eq_zero p (J p) hp), zero_mul]
  constructor
  · set A : ℝ := (S.N : ℝ) / (4 * S.t * S.r ^ 2)
    refine ⟨‖S.Kc‖⁻¹ * C * A ^ (1 / 4 : ℝ), fun m => ?_⟩
    have hprod0 : 0 ≤ ∏ p : S.ι, Real.sqrt p.1 ^ (m p) :=
      Finset.prod_nonneg fun p _ => zpow_nonneg (Real.sqrt_nonneg _) _
    have hA0 : 0 ≤ A ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
    by_cases hm : ∀ p, -(S.L0 : ℤ) ≤ m p
    swap
    · rw [hzero m hm, norm_zero]; positivity
    have hkey := S.key_beta hf hprim hev hm
    unfold dil at hkey
    split_ifs at hkey with hD
    · obtain ⟨n', hn'⟩ := hD
      have hD0 := S.D0_pos
      rw [hn', Nat.mul_div_cancel_left _ hD0] at hkey
      have hprodne : (∏ p : S.ι, p.1 ^ (2 * (m p + S.L0).toNat)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun p _ => pow_ne_zero _ (S.prime p).ne_zero
      have hn'1 : 1 ≤ n' := by
        rcases Nat.eq_zero_or_pos n' with h0 | h0
        · exfalso; rw [h0, mul_zero] at hn'; exact hprodne hn'
        · exact h0
      have hb := hC n' hn'1
      rw [← hkey, norm_mul] at hb
      have hKn : 0 < ‖S.Kc‖ := norm_pos_iff.2 hK
      rw [S.rpow_quarter_eq hm hn'.symm] at hb
      calc ‖S.beta (S.gf hf) m‖ = ‖S.Kc‖⁻¹ * (‖S.Kc‖ * ‖S.beta (S.gf hf) m‖) := by
            field_simp
        _ ≤ ‖S.Kc‖⁻¹ * (C * (A ^ (1 / 4 : ℝ) * ∏ p : S.ι, Real.sqrt p.1 ^ (m p))) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = ‖S.Kc‖⁻¹ * C * A ^ (1 / 4 : ℝ) * ∏ p : S.ι, Real.sqrt p.1 ^ (m p) := by ring
    · have : S.beta (S.gf hf) m = 0 := (mul_eq_zero.1 hkey).resolve_left hK
      rw [this, norm_zero]; positivity
  · intro m hbad
    by_cases hm : ∀ p, -(S.L0 : ℤ) ≤ m p
    swap
    · exact hzero m hm
    have hkey := S.key_beta hf hprim hev hm
    unfold dil at hkey
    rw [if_neg] at hkey
    · exact (mul_eq_zero.1 hkey).resolve_left hK
    · -- `D₀ ∤ n` at a bad prime
      obtain ⟨p, hp⟩ := hbad
      intro hdvd
      have hn0 : (∏ q : S.ι, q.1 ^ (2 * (m q + S.L0).toNat)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun q _ => pow_ne_zero _ (S.prime q).ne_zero
      have hle := (Nat.factorization_le_iff_dvd S.D0_pos.ne' hn0).2 hdvd p.1
      rw [S.prod_pow_factorization (fun q => 2 * (m q + S.L0).toNat) p] at hle
      have hD := S.D0_factorization p
      rw [Nat.factorization_def _ (S.prime p), Nat.factorization_def _ (S.prime p),
        Nat.factorization_def _ (S.prime p)] at hD
      rw [Nat.factorization_def _ (S.prime p)] at hle
      have := hm p
      omega

end ClassSetup

/-- **`SerreStarkFrickeBeta24` is a theorem.** -/
theorem serreStarkFrickeBeta24 : SerreStarkFrickeBeta24 :=
  fun S hprim hev g => S.frickeBeta_holds hprim hev g

/-- **The level box residual is a theorem** (Serre–Stark level analysis, route C). -/
theorem serreStarkLevelBox24 : SerreStarkLevelBox24 :=
  levelBox24_of_frickeBeta serreStarkFrickeBeta24 serreStarkOddVanish24

end SSHecke

end VOA.Classification.COne
