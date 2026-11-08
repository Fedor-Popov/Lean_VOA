import VOA.Moonshine.MoonshineLRHeckeExpansion
import VOA.Moonshine.MoonshineCNGenusZeroTop

/-!
# Nontriviality

Blueprint: non-injectivity modulo translations in `MOON_M8_LEAN.md`.

**Theorem** (`ReplicableFamily_notInjectiveModTranslations`). For a replicable family of positive
period, no member `f_k` is injective on `ℍ / ℤ`.

Proof (the non-injectivity argument in `Notes/moonshine/MOON_ROUTE.md`). Suppose `f = f_k` is
injective modulo `ℤ`.
1. By `ReplicableFamily.largeValuesFromTop` there are `R, Y > 0` such that every value of norm at
   least `R` is taken at height at least `Y`. With injectivity, `‖f‖ < R` below height `Y`.
2. Fix `m ≥ 1` and the replication polynomial `P` with `P(f) = H_m`. The remainder
   `u = H_m − q^{−m}` is bounded on `ℍ`: below height `Y` by `sup_{|w| ≤ R} |P(w)| + e^{2πmY}`, and
   from height `Y` up by its own absolutely convergent `q`-series (`hasSum_heckeOrbitSum`).
3. By `norm_coeff_le_of_hasSum_qPar`, the coefficients `faberRemainderCoeff F.c k m r` (`r ≥ 1`)
   are bounded. This holds for every `m ≥ 1`, contradicting `not_bounded_faberRemainderCoeff`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real

/-- An injective-mod-`ℤ` function whose large values come from height `≥ Y` is bounded by `R`
below height `Y`. -/
theorem norm_lt_of_injective_of_largeValues {f : ℍ → ℂ} (hinj : IsInjectiveModTranslations f)
    {R Y : ℝ} (hR : ∀ w : ℂ, R ≤ ‖w‖ → ∃ σ : ℍ, Y ≤ σ.im ∧ f σ = w) {τ : ℍ} (hτ : τ.im < Y) :
    ‖f τ‖ < R := by
  by_contra h
  rw [not_lt] at h
  obtain ⟨σ, hσY, hσ⟩ := hR (f τ) h
  obtain ⟨n, hn⟩ := hinj σ τ hσ
  have him : σ.im = τ.im := by
    change (σ : ℂ).im = (τ : ℂ).im
    rw [hn]
    simp
  linarith

/-- With bounded-below-`Y` values, every Faber remainder `H_m − q^{−m}` is bounded on `ℍ`. -/
theorem exists_bound_heckeOrbitSum_sub {N : ℕ} (F : ReplicableFamily N) (k : ℕ) {m : ℕ}
    (hm : 0 < m) {R Y : ℝ} (hY : 0 < Y)
    (hlow : ∀ τ : ℍ, τ.im < Y → ‖qSeriesFun (F.c k) τ‖ < R) :
    ∃ M : ℝ, ∀ τ : ℍ, ‖heckeOrbitSum F k m τ - (qPar τ ^ m)⁻¹‖ ≤ M := by
  obtain ⟨P, -, -, hP⟩ := F.exists_monic_eval_eq_heckeOrbitSum k m hm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    P.continuous.continuousOn
  set A : ℕ → ℂ := fun r => if r = 0 then 0 else faberRemainderCoeff F.c k m r with hA
  -- the tail bound at height `Y`
  set τ₀ : ℍ := ⟨Complex.I * Y, by simp [hY]⟩ with hτ₀
  have hτ₀im : τ₀.im = Y := by simp [τ₀, UpperHalfPlane.im]
  set s := Real.exp (-2 * π * Y) with hs
  have hsumm : Summable fun r : ℕ => ‖A r‖ * s ^ r := by
    refine (summable_norm_iff.mpr (hasSum_heckeOrbitSum F k hm τ₀).summable).congr fun r => ?_
    rw [norm_mul, norm_pow, norm_qPar_eq, hτ₀im]
  refine ⟨max (C + Real.exp (2 * π * m * Y)) (∑' r, ‖A r‖ * s ^ r), fun τ => ?_⟩
  by_cases hτ : τ.im < Y
  · refine le_max_of_le_left ?_
    rw [← hP]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · apply hC
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hlow τ hτ).le
    · rw [norm_inv, norm_pow, norm_qPar_eq, ← Real.exp_nat_mul, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hm') (sub_nonneg.mpr hτ.le)]
  · rw [not_lt] at hτ
    refine le_max_of_le_right ?_
    rw [← (hasSum_heckeOrbitSum F k hm τ).tsum_eq]
    refine tsum_of_norm_bounded hsumm.hasSum fun r => ?_
    rw [norm_mul, norm_pow, norm_qPar_eq]
    have hle : Real.exp (-2 * π * τ.im) ≤ s := by
      rw [hs]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hle r) (norm_nonneg _)

/-- **Non-injectivity modulo translations.** For a replicable family of positive period, no member
is injective on `ℍ / ℤ`. -/
theorem ReplicableFamily_notInjectiveModTranslations {N : ℕ} (hN : 0 < N)
    (F : ReplicableFamily N) : F.NotInjectiveModTranslations := by
  intro k hinj
  obtain ⟨R, Y, hY, hR⟩ := F.largeValuesFromTop k
  have hlow : ∀ τ : ℍ, τ.im < Y → ‖qSeriesFun (F.c k) τ‖ < R := fun τ hτ =>
    norm_lt_of_injective_of_largeValues hinj hR hτ
  apply not_bounded_faberRemainderCoeff hN F k
  intro m hm
  obtain ⟨M, hM⟩ := exists_bound_heckeOrbitSum_sub F k (by omega : 0 < m) hY hlow
  refine ⟨M, fun r hr => ?_⟩
  have := norm_coeff_le_of_hasSum_qPar
    (fun r => if r = 0 then 0 else faberRemainderCoeff F.c k m r) _ M
    (hasSum_heckeOrbitSum F k (by omega : 0 < m)) hM r
  simpa [show r ≠ 0 by omega] using this

end VOA.Moonshine.ConwayNorton.M8
