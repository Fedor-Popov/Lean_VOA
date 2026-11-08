import VOA.Moonshine.MoonshineCNGenusZeroAnalytic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Coefficient bound for bounded `q`-series on `ℍ`

If `u(τ) = Σ_{r ≥ 0} A_r qʳ` on `ℍ` (with `q = e^{2πiτ}`) and `‖u‖ ≤ M` on `ℍ`, then
`‖A_r‖ ≤ M` for every `r` (`norm_coeff_le_of_hasSum_qPar`).

The proof is discrete. Average `u(τ + t/L) · ζ^{(L−r)t}` over `t < L`, with `ζ = e^{2πi/L}`.
By the roots-of-unity sum (`sum_range_pow_rootOfUnity`), this picks out the coefficients
`A_{r'}` with `r' ≡ r (mod L)`. For `L > r` these are `A_r` and coefficients with index
at least `L`, so `‖A_r‖ e^{−2πry} ≤ M + (tail of the series from L)`. Letting `L → ∞` and
then `y → 0` gives the bound. No contour integrals are needed.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real Filter Topology

/-- Roots-of-unity sum: with `ζ = e^{2πi/L}`, `Σ_{t<L} (ζⁿ)ᵗ = L` if `L ∣ n`, and `0` otherwise. -/
theorem sum_range_pow_rootOfUnity {L : ℕ} (hL : 0 < L) (n : ℕ) :
    ∑ t ∈ Finset.range L, (Complex.exp (2 * π * Complex.I / L) ^ n) ^ t =
      if L ∣ n then (L : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp L hL.ne'
  split_ifs with h
  · obtain ⟨s, rfl⟩ := h
    rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp
  · have hne : Complex.exp (2 * π * Complex.I / L) ^ n ≠ 1 := fun h1 =>
      h ((hζ.pow_eq_one_iff_dvd n).mp h1)
    have hpow : (Complex.exp (2 * π * Complex.I / L) ^ n) ^ L = 1 := by
      rw [← pow_mul, show n * L = L * n from Nat.mul_comm n L, pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

theorem norm_exp_two_pi_I_div_natCast (L : ℕ) : ‖Complex.exp (2 * π * Complex.I / L)‖ = 1 := by
  rw [show 2 * (π : ℂ) * Complex.I / L = ((2 * π / L : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Translating `τ` by `t/L` multiplies `q` by `ζᵗ`. -/
theorem qPar_vadd_div (τ : ℍ) (t L : ℕ) :
    qPar (((t : ℝ) / L) +ᵥ τ) = qPar τ * Complex.exp (2 * π * Complex.I / L) ^ t := by
  simp only [qPar, Function.Periodic.qParam, coe_vadd]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The averaging step: for `L > r`, `‖A_r‖ ‖q‖ʳ ≤ M + Σ_k ‖A_{k+L}‖ ‖q‖^{k+L}`. -/
theorem norm_coeff_mul_le_add_tail (A : ℕ → ℂ) (u : ℍ → ℂ) (M : ℝ)
    (hu : ∀ τ : ℍ, HasSum (fun r => A r * qPar τ ^ r) (u τ)) (hM : ∀ τ : ℍ, ‖u τ‖ ≤ M)
    (τ : ℍ) {r L : ℕ} (hrL : r < L) :
    ‖A r‖ * ‖qPar τ‖ ^ r ≤ M + ∑' k, ‖A (k + L)‖ * ‖qPar τ‖ ^ (k + L) := by
  have hL : 0 < L := by omega
  set q := qPar τ with hq
  set s := ‖q‖ with hs
  set a : ℕ → ℝ := fun r' => ‖A r'‖ * s ^ r' with ha_def
  have ha : Summable a := by
    have := summable_norm_iff.mpr (hu τ).summable
    simpa [a, norm_mul, norm_pow] using this
  set ζ := Complex.exp (2 * π * Complex.I / L) with hζ
  have hζ1 : ‖ζ‖ = 1 := norm_exp_two_pi_I_div_natCast L
  set g : ℕ → ℂ := fun r' => if L ∣ r' + (L - r) then A r' * q ^ r' else 0 with hg
  have hga : ∀ r', ‖g r'‖ ≤ a r' := by
    intro r'
    simp only [hg, ha_def]
    split_ifs
    · rw [norm_mul, norm_pow]
    · rw [norm_zero]
      positivity
  have hgs : Summable g := Summable.of_norm_bounded ha hga
  -- the averaged sum equals `L · Σ' g`
  have hterm : ∀ t : ℕ, u (((t : ℝ) / L) +ᵥ τ) * (ζ ^ (L - r)) ^ t =
      ∑' r', A r' * q ^ r' * (ζ ^ (r' + (L - r))) ^ t := by
    intro t
    rw [← (hu _).tsum_eq, ← tsum_mul_right]
    refine tsum_congr fun r' => ?_
    rw [qPar_vadd_div]
    ring
  have hsumm : ∀ t : ℕ, Summable fun r' => A r' * q ^ r' * (ζ ^ (r' + (L - r))) ^ t := by
    intro t
    refine Summable.of_norm_bounded ha fun r' => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hζ1, one_pow, one_pow, mul_one]
  have havg : ∑ t ∈ Finset.range L, u (((t : ℝ) / L) +ᵥ τ) * (ζ ^ (L - r)) ^ t =
      (L : ℂ) * ∑' r', g r' := by
    simp_rw [hterm]
    rw [← Summable.tsum_finsetSum fun t _ => hsumm t, ← tsum_mul_left]
    refine tsum_congr fun r' => ?_
    rw [← Finset.mul_sum, sum_range_pow_rootOfUnity hL]
    simp only [hg]
    split_ifs <;> ring
  -- so `‖Σ' g‖ ≤ M`
  have hgM : ‖∑' r', g r'‖ ≤ M := by
    have h1 : ‖∑ t ∈ Finset.range L, u (((t : ℝ) / L) +ᵥ τ) * (ζ ^ (L - r)) ^ t‖ ≤ L * M := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ t ∈ Finset.range L, ‖u (((t : ℝ) / L) +ᵥ τ) * (ζ ^ (L - r)) ^ t‖ ≤ M := by
        intro t _
        rw [norm_mul, norm_pow, norm_pow, hζ1, one_pow, one_pow, mul_one]
        exact hM _
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [havg, norm_mul, Complex.norm_natCast] at h1
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    exact le_of_mul_le_mul_left (by linarith) hL'
  -- isolate the `r' = r` term
  have hgr : g r = A r * q ^ r := by
    simp only [hg]
    rw [if_pos ⟨1, by omega⟩]
  have hsplit := hgs.tsum_eq_add_tsum_ite r
  rw [hgr] at hsplit
  -- the rest is bounded by the tail from `L`
  set f : ℕ → ℝ := fun r' => if L ≤ r' then a r' else 0 with hf
  have hfa : ∀ r', 0 ≤ f r' := by
    intro r'
    simp only [hf, ha_def]
    split_ifs <;> positivity
  have hfs : Summable f :=
    Summable.of_nonneg_of_le hfa (fun r' => by
      simp only [hf]
      split_ifs
      · exact le_rfl
      · simp only [ha_def]
        positivity) ha
  have hrest : ‖∑' r', (if r' = r then 0 else g r')‖ ≤ ∑' r', f r' := by
    refine tsum_of_norm_bounded hfs.hasSum fun r' => ?_
    split_ifs with h1
    · rw [norm_zero]
      exact hfa r'
    · simp only [hg, hf]
      split_ifs with h2 h3
      · rw [norm_mul, norm_pow]
      · exfalso
        obtain ⟨j, hj⟩ := h2
        rcases j with _ | _ | j
        · omega
        · omega
        · have : L * (j + 1 + 1) = L * j + 2 * L := by ring
          omega
      · rw [norm_zero]
        simp only [ha_def]
        positivity
      · rw [norm_zero]
  have htail : ∑' r', f r' = ∑' k, a (k + L) := by
    rw [← hfs.sum_add_tsum_nat_add L]
    have h0 : ∑ i ∈ Finset.range L, f i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [hf]
        rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
    rw [h0, zero_add]
    refine tsum_congr fun k => ?_
    simp only [hf]
    rw [if_pos (by omega)]
  -- combine
  have hAr : ‖A r * q ^ r‖ = ‖A r‖ * s ^ r := by rw [norm_mul, norm_pow]
  have h1 : A r * q ^ r = ∑' r', g r' - ∑' r', (if r' = r then 0 else g r') := by
    rw [hsplit]
    ring
  have h2 : ‖A r * q ^ r‖ ≤ M + ∑' k, a (k + L) := by
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    rw [← htail]
    linarith
  rw [hAr] at h2
  exact h2

/-- **Coefficient bound.** If `u(τ) = Σ_r A_r qʳ` on `ℍ` and `‖u‖ ≤ M` on `ℍ`, then `‖A_r‖ ≤ M`. -/
theorem norm_coeff_le_of_hasSum_qPar (A : ℕ → ℂ) (u : ℍ → ℂ) (M : ℝ)
    (hu : ∀ τ : ℍ, HasSum (fun r => A r * qPar τ ^ r) (u τ)) (hM : ∀ τ : ℍ, ‖u τ‖ ≤ M)
    (r : ℕ) : ‖A r‖ ≤ M := by
  -- for every `τ`, `‖A_r‖ ‖q‖ʳ ≤ M` (let `L → ∞`)
  have key : ∀ τ : ℍ, ‖A r‖ * ‖qPar τ‖ ^ r ≤ M := by
    intro τ
    set a : ℕ → ℝ := fun r' => ‖A r'‖ * ‖qPar τ‖ ^ r' with ha_def
    have ht : Tendsto (fun L => M + ∑' k, a (k + L)) atTop (𝓝 (M + 0)) :=
      tendsto_const_nhds.add (tendsto_sum_nat_add a)
    rw [add_zero] at ht
    exact ge_of_tendsto ht (eventually_atTop.mpr ⟨r + 1, fun L hL =>
      norm_coeff_mul_le_add_tail A u M hu hM τ (by omega)⟩)
  -- along `τ = iy`, `y → 0⁺`
  have hy : ∀ y : ℝ, 0 < y → ‖A r‖ * Real.exp (-2 * π * y) ^ r ≤ M := by
    intro y hy
    have := key ⟨Complex.I * y, by simp [hy]⟩
    rw [norm_qPar_eq] at this
    simpa [UpperHalfPlane.im] using this
  have hcont : Continuous fun y : ℝ => ‖A r‖ * Real.exp (-2 * π * y) ^ r :=
    continuous_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).pow r)
  have hlim : Tendsto (fun y : ℝ => ‖A r‖ * Real.exp (-2 * π * y) ^ r) (𝓝[>] 0)
      (𝓝 (‖A r‖ * Real.exp (-2 * π * 0) ^ r)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [mul_zero, Real.exp_zero, one_pow, mul_one] at hlim
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy' => hy y hy')

end VOA.Moonshine.ConwayNorton.M8
