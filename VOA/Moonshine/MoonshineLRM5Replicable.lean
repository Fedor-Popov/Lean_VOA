import VOA.Moonshine.MoonshineLRM5CosetMap
import VOA.Moonshine.Character
import Mathlib.NumberTheory.Modular

/-!
# `J` is replicable

Blueprint: replicability of `J` in `Notes/moonshine/MOON_BKM.md`. With `J = j − 744 = qSeriesFun cJ`
and `F_M` the Faber polynomial of `J`, for every `M ≥ 1` and `τ ∈ ℍ`:
* `faberPoly_cJ_eval_eq_qHeckeSum`: `F_M(J(τ)) = R_M(τ) = Σ_{ad=M} Σ_{b<d} J((aτ+b)/d)`;
* `coeff_faberPoly_cJ_eq_qHeckeCoeff`, the coefficient form `(Rep₁)`:
  `[qʳ] F_M(J) = Σ_{a ∣ gcd(M,r)} (M/a) c(Mr/a²)` for every `r ≥ 1`.

Proof. `D = F_M ∘ J − R_M` is `SL₂(ℤ)`-invariant (`qHeckeSum_smul`), and
`D(τ) = Σ_{r ≥ 1} δ_r qʳ` (`hasSum_mul_eval_qSeriesFun`, `hasSum_qHeckeSum`). Such a function
vanishes (`eq_zero_of_invariant_hasSum`), with no holomorphy argument. Every point is equivalent to
one of height at least `1/2`, where `|D| ≤ B ρ/(1 − ρ)` with `ρ = e^{−π}` whenever all `|δ_r| ≤ B`.
The coefficient bound `norm_coeff_le_of_hasSum_qPar` then improves `B` to `B ρ/(1 − ρ)`, and
`ρ/(1 − ρ) < 1`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real Polynomial Filter Topology
open scoped MatrixGroups Modular

/-! ### `J` as a `q`-series -/

/-- The coefficients of `J`: `cJ n = [qⁿ] J` (`n ≥ 1`; the value at `0` is `[q⁰] J = 0`). -/
noncomputable def cJ (n : ℕ) : ℂ := PowerSeries.coeff (n + 1) JShift

theorem isJDominated_cJ : IsJDominated cJ := fun _ => le_rfl

theorem qSeriesFun_cJ (τ : ℍ) : qSeriesFun cJ τ = jInvariant τ - 744 := by
  have h := hasSum_JShift_laurent τ
  have h2 := h.summable.tsum_eq_zero_add
  rw [h.tsum_eq] at h2
  simp only [pow_zero, mul_one, coeff_one_JShift, zero_add] at h2
  simp only [qSeriesFun, cJ]
  have e : (∑' n : ℕ, PowerSeries.coeff (n + 1 + 1) JShift * qPar τ ^ (n + 1)) =
      jInvariant τ - 744 - (qPar τ)⁻¹ := h2.symm
  rw [e]
  ring

theorem qSeriesFun_cJ_smul (γ : SL(2, ℤ)) (τ : ℍ) : qSeriesFun cJ (γ • τ) = qSeriesFun cJ τ := by
  rw [qSeriesFun_cJ, qSeriesFun_cJ, jInvariant_smul]

/-! ### Faber polynomials of a `q`-series, analytically -/

/-- `F_M(f(τ)) − q^{−M} = Σ_{r ≥ 1} [qʳ] F_M(f) · qʳ` for a `J`-dominated `f`. -/
theorem hasSum_faberPoly_eval_sub {c : ℕ → ℂ} (hc : IsJDominated c) {M : ℕ} (hM : 0 < M)
    (τ : ℍ) :
    HasSum (fun r : ℕ => (if r = 0 then 0 else
        (aeval (qSeriesLaurent c) (faberPoly c M)).coeff (r : ℤ)) * qPar τ ^ r)
      ((faberPoly c M).eval (qSeriesFun c τ) - (qPar τ ^ M)⁻¹) := by
  set L := aeval (qSeriesLaurent c) (faberPoly c M) with hL
  have hq : qPar τ ≠ 0 := Function.Periodic.qParam_ne_zero _
  have h := hasSum_mul_eval_qSeriesFun hc (faberPoly c M) τ
  rw [faberPoly_natDegree] at h
  have h1 := h.mul_right (qPar τ ^ M)⁻¹
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul] at h1
  have h2 := (hasSum_nat_add_iff' M).mpr h1
  have hlow : ∑ i ∈ Finset.range M, L.coeff ((i : ℤ) - M) * qPar τ ^ i * (qPar τ ^ M)⁻¹ =
      (qPar τ ^ M)⁻¹ := by
    rw [Finset.sum_eq_single 0]
    · rw [Nat.cast_zero, zero_sub, coeff_aeval_faberPoly c M (by omega), if_pos rfl]
      ring
    · intro i hi hi0
      rw [coeff_aeval_faberPoly c M (by have := Finset.mem_range.mp hi; omega),
        if_neg (by omega)]
      ring
    · intro h0
      exact absurd (Finset.mem_range.mpr hM) h0
  rw [hlow] at h2
  convert h2 using 1
  funext r
  rw [Nat.cast_add, add_sub_cancel_right, pow_add, mul_assoc,
    mul_inv_cancel_right₀ (pow_ne_zero _ hq)]
  by_cases hr : r = 0
  · subst hr
    rw [if_pos rfl, Nat.cast_zero, coeff_aeval_faberPoly c M le_rfl, if_neg (by omega)]
  · rw [if_neg hr]

/-! ### Invariant `q`-series vanish -/

theorem exp_neg_pi_lt_half : Real.exp (-π) < 1 / 2 := by
  have h1 : π + 1 ≤ Real.exp π := Real.add_one_le_exp π
  have h2 : Real.exp (-π) * Real.exp π = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.pi_gt_three
  nlinarith [Real.exp_pos (-π), Real.exp_pos π]

/-- Every point of `ℍ` is `SL₂(ℤ)`-equivalent to a point of height at least `1/2`. -/
theorem exists_smul_half_le_im (τ : ℍ) : ∃ γ : SL(2, ℤ), 1 / 2 ≤ (γ • τ).im := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  refine ⟨γ, ?_⟩
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have hpos := (γ • τ).im_pos
  nlinarith

/-- One improvement step: if all `‖δ_r‖ ≤ B`, then all `‖δ_r‖ ≤ B ρ/(1 − ρ)`, `ρ = e^{−π}`. -/
theorem norm_le_mul_of_invariant_hasSum {δ : ℕ → ℂ} {D : ℍ → ℂ}
    (hD : ∀ (γ : SL(2, ℤ)) (τ : ℍ), D (γ • τ) = D τ)
    (hs : ∀ τ : ℍ, HasSum (fun r => δ r * qPar τ ^ r) (D τ)) (h0 : δ 0 = 0) {B : ℝ}
    (hB : ∀ r, ‖δ r‖ ≤ B) (r : ℕ) :
    ‖δ r‖ ≤ B * (Real.exp (-π) / (1 - Real.exp (-π))) := by
  set ρ := Real.exp (-π) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by linarith [exp_neg_pi_lt_half]
  -- the bound at height at least `1/2`
  have htop : ∀ τ : ℍ, 1 / 2 ≤ τ.im → ‖D τ‖ ≤ B * (ρ / (1 - ρ)) := by
    intro τ hτ
    have hshift := (hasSum_nat_add_iff' 1).mpr (hs τ)
    simp only [Finset.range_one, Finset.sum_singleton, h0, zero_mul, sub_zero] at hshift
    have hgeom := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left (B * ρ)
    have hval : B * ρ * (1 - ρ)⁻¹ = B * (ρ / (1 - ρ)) := by ring
    rw [hval] at hgeom
    refine hshift.norm_le_of_bounded hgeom fun n => ?_
    rw [norm_mul, norm_pow, norm_qPar_eq]
    have hle : Real.exp (-2 * π * τ.im) ≤ ρ := by
      rw [hρ]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hpow : Real.exp (-2 * π * τ.im) ^ (n + 1) ≤ ρ ^ (n + 1) :=
      pow_le_pow_left₀ (Real.exp_pos _).le hle _
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    calc ‖δ (n + 1)‖ * Real.exp (-2 * π * τ.im) ^ (n + 1) ≤ B * ρ ^ (n + 1) :=
          mul_le_mul (hB _) hpow (by positivity) hB0
      _ = B * ρ * ρ ^ n := by ring
  -- everywhere, by `SL₂(ℤ)`-invariance
  have hall : ∀ τ : ℍ, ‖D τ‖ ≤ B * (ρ / (1 - ρ)) := by
    intro τ
    obtain ⟨γ, hγ⟩ := exists_smul_half_le_im τ
    rw [← hD γ τ]
    exact htop _ hγ
  exact norm_coeff_le_of_hasSum_qPar δ D _ hs hall r

/-- **An `SL₂(ℤ)`-invariant `q`-series without constant term vanishes.** -/
theorem eq_zero_of_invariant_hasSum {δ : ℕ → ℂ} {D : ℍ → ℂ}
    (hD : ∀ (γ : SL(2, ℤ)) (τ : ℍ), D (γ • τ) = D τ)
    (hs : ∀ τ : ℍ, HasSum (fun r => δ r * qPar τ ^ r) (D τ)) (h0 : δ 0 = 0) (r : ℕ) :
    δ r = 0 := by
  set κ := Real.exp (-π) / (1 - Real.exp (-π)) with hκ
  have hρ := exp_neg_pi_lt_half
  have hρ0 := Real.exp_pos (-π)
  have hκ0 : 0 ≤ κ := div_nonneg hρ0.le (by linarith)
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one (by linarith)]; linarith
  -- a first bound
  set τ₀ : ℍ := ⟨Complex.I * (1 / 2 : ℝ), by simp⟩ with hτ₀
  have hS : Summable fun r => ‖δ r * qPar τ₀ ^ r‖ := summable_norm_iff.mpr (hs τ₀).summable
  have hfirst : ∀ r, ‖δ r‖ ≤ ∑' r, ‖δ r * qPar τ₀ ^ r‖ := by
    refine norm_coeff_le_of_hasSum_qPar δ D _ hs fun τ => ?_
    obtain ⟨γ, hγ⟩ := exists_smul_half_le_im τ
    set w := γ • τ with hw
    have hsw : Summable fun r => ‖δ r * qPar w ^ r‖ := summable_norm_iff.mpr (hs w).summable
    rw [← hD γ τ, ← hw, ← (hs w).tsum_eq]
    refine (norm_tsum_le_tsum_norm hsw).trans ?_
    refine hsw.tsum_le_tsum (fun n => ?_) hS
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_qPar_eq, norm_qPar_eq]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le ?_ _) (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have : τ₀.im = 1 / 2 := by simp [τ₀, UpperHalfPlane.im]
    rw [this]
    nlinarith [Real.pi_pos]
  set B₀ := ∑' r, ‖δ r * qPar τ₀ ^ r‖ with hB₀
  -- iterate the improvement
  have hiter : ∀ n : ℕ, ∀ r, ‖δ r‖ ≤ B₀ * κ ^ n := by
    intro n
    induction n with
    | zero => simpa using hfirst
    | succ n ih =>
      intro r
      have := norm_le_mul_of_invariant_hasSum hD hs h0 ih r
      rw [pow_succ, ← mul_assoc]
      exact this
  have hlim : Tendsto (fun n : ℕ => B₀ * κ ^ n) atTop (𝓝 (B₀ * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1)
  rw [mul_zero] at hlim
  have hle : ‖δ r‖ ≤ 0 := ge_of_tendsto' hlim fun n => hiter n r
  exact norm_le_zero_iff.mp hle

/-! ### `J` is replicable -/

/-- The `q`-coefficients of `F_M(J) − R_M`. -/
noncomputable def replicationDefect (M r : ℕ) : ℂ :=
  if r = 0 then 0 else
    (aeval (qSeriesLaurent cJ) (faberPoly cJ M)).coeff (r : ℤ) - qHeckeCoeff cJ M r

theorem hasSum_replicationDefect {M : ℕ} (hM : 0 < M) (τ : ℍ) :
    HasSum (fun r => replicationDefect M r * qPar τ ^ r)
      ((faberPoly cJ M).eval (qSeriesFun cJ τ) - qHeckeSum cJ M τ) := by
  have h := (hasSum_faberPoly_eval_sub isJDominated_cJ hM τ).sub
    (hasSum_qHeckeSum isJDominated_cJ hM τ)
  rw [sub_sub_sub_cancel_right] at h
  convert h using 1
  funext r
  simp only [replicationDefect]
  split_ifs <;> ring

/-- **`J` is replicable (analytic form):** `F_M(J(τ)) = Σ_{ad=M} Σ_{b<d} J((aτ+b)/d)`. -/
theorem faberPoly_cJ_eval_eq_qHeckeSum {M : ℕ} (hM : 0 < M) (τ : ℍ) :
    (faberPoly cJ M).eval (qSeriesFun cJ τ) = qHeckeSum cJ M τ := by
  have hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      (faberPoly cJ M).eval (qSeriesFun cJ (γ • τ)) - qHeckeSum cJ M (γ • τ) =
        (faberPoly cJ M).eval (qSeriesFun cJ τ) - qHeckeSum cJ M τ := by
    intro γ τ
    rw [qSeriesFun_cJ_smul, qHeckeSum_smul qSeriesFun_cJ_smul]
  have hzero := eq_zero_of_invariant_hasSum hinv (hasSum_replicationDefect hM)
    (by simp [replicationDefect])
  have h := hasSum_replicationDefect hM τ
  simp only [hzero, zero_mul] at h
  exact sub_eq_zero.mp (h.unique hasSum_zero)

/-- **`J` is replicable (coefficient form, `(Rep₁)`):** for `r ≥ 1`,
`[qʳ] F_M(J) = Σ_{a ∣ gcd(M,r)} (M/a) · c(Mr/a²)`. -/
theorem coeff_faberPoly_cJ_eq_qHeckeCoeff {M : ℕ} (hM : 0 < M) {r : ℕ} (hr : r ≠ 0) :
    (aeval (qSeriesLaurent cJ) (faberPoly cJ M)).coeff (r : ℤ) = qHeckeCoeff cJ M r := by
  have hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      (faberPoly cJ M).eval (qSeriesFun cJ (γ • τ)) - qHeckeSum cJ M (γ • τ) =
        (faberPoly cJ M).eval (qSeriesFun cJ τ) - qHeckeSum cJ M τ := by
    intro γ τ
    rw [qSeriesFun_cJ_smul, qHeckeSum_smul qSeriesFun_cJ_smul]
  have hzero := eq_zero_of_invariant_hasSum hinv (hasSum_replicationDefect hM)
    (by simp [replicationDefect]) r
  rw [replicationDefect, if_neg hr] at hzero
  exact sub_eq_zero.mp hzero

end VOA.Moonshine.ConwayNorton.M8
