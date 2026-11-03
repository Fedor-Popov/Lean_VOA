/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Conditional

/-!
# The paper gaps `GapLemma37` and `GapGaloisBound` (G2)

Both gaps of `Conditional.lean` that come from Gannon–Rayhaun §3 (arXiv:2609.00122) are reduced
here to **one** named classical fact about theta functions, `ThetaGaloisLaw` (GR Prop. 3.8,
eq. (3.18)): for `24 ∣ M`, `4 t r² ∣ M`, `ℓ` coprime to `M` and `γ ≡ diag(ℓ, ℓ⁻¹) (mod M)`,

  `θ_{n₀,r,t}(γτ) η(τ) = (2t/ℓ) θ_{ℓn₀,r,t}(τ) η(γτ)`.

Its `ℓ = 1`, `n₀ = 0`, `r = t = 1` case is GR (3.11), `η(γτ)/η(τ) = θ(γτ)/θ(τ)` on `Γ(24)`.

## Main results

* `gapLemma37_of_thetaGaloisLaw : ThetaGaloisLaw → GapLemma37` — GR Lemma 3.7. Proved here:
  holomorphy of `η ch_V` on `ℍ` (`differentiableOn_eta_mul_ch`), the multiplier on `Γ₁(N)` from
  `Γ(N)`-invariance, `T`-periodicity and `Γ₁(N) = Γ(N) ⟨T⟩` (`multiplier_of_thetaGaloisLaw`), and
  the cusp bounds for *every* `γ ∈ SL₂(ℤ)` (`cusp_bound`): `ch_V ∘ γ` is a combination of the
  `ch_b` (`exists_ch_comp`, by `SL2Z_generators`), `|η(γτ)| = |cτ+d|^{1/2} |η(τ)|` (from
  `Δ = η²⁴`), and `|η ch_b| ≤ K` on `Im τ ≥ 1` (pseudo-unitarity `h_b ≥ 0`).
* `gapGaloisBound_of_thetaGaloisLaw : ThetaGaloisLaw → GapGaloisBound` — GR (3.31)–(3.35):
  an explicit `γ_ℓ ≡ diag(ℓ, ℓ⁻¹) (mod N)`, the Galois signed permutation, the theta law,
  the `S`-transform, `Proj_ℤ`, and the `q^{-1/24}` coefficient (`y → ∞` at `τ = iy`).

`ThetaGaloisLaw` is **not** proved here (it is the Shimura theta multiplier / the Galois action
on the modular data of `V_{2tr²}`); everything else is.
-/

open Complex Finset Module Filter Topology
open UpperHalfPlane hiding I

noncomputable section

namespace VOA.Classification.COne

open VOA

universe u

/-! ## The named classical input -/

/-- **The theta Galois law** (GR Prop. 3.8, eq. (3.18); Shimura's theta multiplier). For
`24 ∣ M`, `4 t r² ∣ M`, `ℓ` coprime to `M`, `ℓ ℓ' ≡ 1 (mod M)` and `γ ≡ diag(ℓ, ℓ') (mod M)`:
`θ_{n₀,r,t}(γτ) η(τ) = (2t/ℓ) θ_{ℓn₀,r,t}(τ) η(γτ)` (cross-multiplied form of (3.18); `η` has no
zeros on `ℍ`). For `ℓ = 1` this is the `Γ(M)`-invariance of the lattice character
`θ_{n₀,r,t}/η` of `V_{2tr²}` (conductor `lcm(4tr², 24)`), in particular GR (3.11).

Checked numerically (30 digits) for `(n₀,r,t,ℓ,M) ∈ {(0,1,1,1,24), (1,7,1,5,1176),
(2,7,1,11,1176), (1,1,3,7,72), (1,2,5,7,240), (1,3,2,5,72)}` and for `-γ` (`ℓ ↦ M - ℓ`); the
variant with `ℓ⁻¹ n₀` in place of `ℓ n₀` fails for `r = 7`. -/
def ThetaGaloisLaw : Prop :=
  ∀ (n₀ : ℤ) (r t M : ℕ), 0 < r → 0 < t → 4 * t * r ^ 2 ∣ M → 24 ∣ M →
    ∀ ℓ : ℕ, ℓ.Coprime M → ∀ ℓ' : ℤ, (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD M] →
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ 0 0 ≡ ℓ [ZMOD M] → γ 1 1 ≡ ℓ' [ZMOD M] → γ 0 1 ≡ 0 [ZMOD M] → γ 1 0 ≡ 0 [ZMOD M] →
      ∀ τ : ℂ, 0 < τ.im →
        rankOneTheta n₀ r t (mobius γ τ) * ModularForm.eta τ =
          (jacobiSym (2 * (t : ℤ)) ℓ : ℂ) * rankOneTheta ((ℓ : ℤ) * n₀) r t τ *
            ModularForm.eta (mobius γ τ)

/-! ## `mobius` and the action on `ℍ` -/

theorem mobius_eq_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) :
    mobius γ τ = ((γ • τ : ℍ) : ℂ) := by
  rw [coe_specialLinearGroup_apply, mobius]
  simp

theorem im_mobius_pos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (mobius γ τ).im := by
  rw [show τ = ((⟨τ, hτ⟩ : ℍ) : ℂ) from rfl, mobius_eq_smul]
  exact (γ • (⟨τ, hτ⟩ : ℍ)).im_pos

theorem mobius_mul (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    mobius (γ * δ) τ = mobius γ (mobius δ τ) := by
  have h1 : mobius δ τ = ((δ • (⟨τ, hτ⟩ : ℍ) : ℍ) : ℂ) := mobius_eq_smul δ ⟨τ, hτ⟩
  rw [show τ = ((⟨τ, hτ⟩ : ℍ) : ℂ) from rfl, mobius_eq_smul, h1, mobius_eq_smul, mul_smul]

theorem mobius_T_zpow (n : ℤ) (τ : ℂ) : mobius (ModularGroup.T ^ n) τ = τ + n := by
  rw [mobius, ModularGroup.coe_T_zpow]
  simp

/-! ## Periodicity -/

theorem thetaRef_add_int (τ : ℂ) (n : ℤ) : thetaRef (τ + n) = thetaRef τ := by
  have hp : Function.Periodic thetaRef 1 := fun τ => by
    simpa [thetaRef] using rankOneTheta_T 0 1 1 τ
  simpa using (hp.int_mul n) τ

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

/-- `F_V = η ch_V` is `1`-periodic on `ℍ` (for `c = 1`). -/
theorem IsModularData.F_add_one (hD : D.IsModularData) (hc : V.centralCharge = 1) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ModularForm.eta (τ + 1) * D.ch D.vac (τ + 1) = ModularForm.eta τ * D.ch D.vac τ := by
  have h := hD.ch_add_nat D.vac 1 hτ
  rw [Nat.cast_one] at h
  rw [eta_add_one, h, hD.h_vac, hc]
  have : cexp (2 * Real.pi * I / 24) * cexp (2 * Real.pi * I * (((0 : ℚ) : ℂ) - 1 / 24) * 1) =
      1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
  linear_combination (ModularForm.eta τ * D.ch D.vac τ) * this

theorem IsModularData.F_add_int (hD : D.IsModularData) (hc : V.centralCharge = 1) {τ : ℂ}
    (hτ : 0 < τ.im) (n : ℤ) :
    ModularForm.eta (τ + n) * D.ch D.vac (τ + n) = ModularForm.eta τ * D.ch D.vac τ := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have hk : 0 < (τ + (k : ℤ)).im := by simpa using hτ
    rw [show τ + ((k + 1 : ℤ) : ℂ) = (τ + (k : ℤ)) + 1 by push_cast; ring,
      hD.F_add_one hc hk, ih]
  | pred k ih =>
    have hk : 0 < (τ + ((-(k : ℤ) - 1 : ℤ) : ℂ)).im := by simpa using hτ
    rw [← ih, show τ + ((-(k : ℤ) : ℤ) : ℂ) = (τ + ((-(k : ℤ) - 1 : ℤ) : ℂ)) + 1 by
      push_cast; ring, hD.F_add_one hc hk]

end ModularData


/-! ## `q`-series: holomorphy and growth -/

theorem re_two_pi_I_mul (w : ℝ) (τ : ℂ) :
    (2 * Real.pi * I * (w : ℂ) * τ).re = -(2 * Real.pi * w * τ.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_cexp_two_pi_I_mul (w : ℝ) (τ : ℂ) :
    ‖cexp (2 * Real.pi * I * (w : ℂ) * τ)‖ = Real.exp (-(2 * Real.pi * w * τ.im)) := by
  rw [Complex.norm_exp, re_two_pi_I_mul]

/-- A `q`-series `Σ c_n q^{x+n}` with nonnegative coefficients converging on `ℍ` is holomorphic
on `ℍ`. -/
theorem differentiableOn_qseries (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (x : ℝ) (f : ℂ → ℂ)
    (hf : ∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => (c n : ℂ) * cexp (2 * Real.pi * I * ((x : ℂ) + n) * τ)) (f τ)) :
    DifferentiableOn ℂ f {τ : ℂ | 0 < τ.im} := by
  intro τ₀ hτ₀
  have hy : 0 < τ₀.im := hτ₀
  set U : Set ℂ := {τ : ℂ | τ₀.im / 2 < τ.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτ₀U : τ₀ ∈ U := by simp only [hU, Set.mem_setOf_eq]; linarith
  set u : ℕ → ℝ := fun n => c n * Real.exp (-(2 * Real.pi * n * (τ₀.im / 2))) with hu
  -- summability of the majorant, from convergence at `i y₀/2`
  have hu_sum : Summable u := by
    have h1 := hf ((((τ₀.im / 2 : ℝ)) : ℂ) * I) (by simp; linarith)
    have h2 := summable_norm_iff.2 h1.summable
    have h3 := h2.mul_left (Real.exp (2 * Real.pi * x * (τ₀.im / 2)))
    refine h3.congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc n),
      show (x : ℂ) + n = ((x + n : ℝ) : ℂ) by push_cast; ring, norm_cexp_two_pi_I_mul, hu]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  set F : ℕ → ℂ → ℂ := fun n τ => (c n : ℂ) * cexp (2 * Real.pi * I * (n : ℂ) * τ) with hF
  have hF_le : ∀ n (w : ℂ), w ∈ U → ‖F n w‖ ≤ u n := by
    intro n w hw
    simp only [hU, Set.mem_setOf_eq] at hw
    rw [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc n),
      show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by push_cast; ring, norm_cexp_two_pi_I_mul]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc n)
    have : 0 ≤ 2 * Real.pi * (n : ℝ) := by positivity
    nlinarith
  have hG : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, F n w) U :=
    Complex.differentiableOn_tsum_of_summable_norm hu_sum
      (fun n => by simp only [hF]; fun_prop) hUo hF_le
  have hE : DifferentiableOn ℂ (fun w : ℂ => cexp (2 * Real.pi * I * (x : ℂ) * w) *
      ∑' n : ℕ, F n w) U := by
    refine DifferentiableOn.mul ?_ hG
    fun_prop
  have heq : Set.EqOn f (fun w : ℂ => cexp (2 * Real.pi * I * (x : ℂ) * w) *
      ∑' n : ℕ, F n w) U := by
    intro w hw
    have hw' : 0 < w.im := by
      simp only [hU, Set.mem_setOf_eq] at hw; linarith
    have hs : Summable fun n => F n w :=
      Summable.of_norm_bounded hu_sum fun n => hF_le n w hw
    refine (hf w hw').unique ?_
    refine (hs.hasSum.mul_left (cexp (2 * Real.pi * I * (x : ℂ) * w))).congr_fun fun n => ?_
    simp only [hF]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  exact ((hE.congr heq).differentiableAt (hUo.mem_nhds hτ₀U)).differentiableWithinAt

/-- Growth of a `q`-series `Σ c_n q^{x+n-1/24}`, `x ≥ 0`, on `Im τ ≥ 1`:
`‖f(τ)‖ ≤ K e^{2π Im τ/24}`. -/
theorem norm_qseries_le (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (x : ℝ) (hx : 0 ≤ x) (f : ℂ → ℂ)
    (hf : ∀ τ : ℂ, 0 < τ.im →
      HasSum (fun n : ℕ => (c n : ℂ) * cexp (2 * Real.pi * I * ((x : ℂ) + n - 1 / 24) * τ))
        (f τ)) :
    ∃ K : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖f τ‖ ≤ K * Real.exp (2 * Real.pi * τ.im / 24) := by
  set g : ℕ → ℝ := fun n => c n * Real.exp (-(2 * Real.pi * (x + n)))
  have hg : Summable g := by
    have h1 := hf I (by simp)
    have h2 := (summable_norm_iff.2 h1.summable).mul_left (Real.exp (-(2 * Real.pi / 24)))
    refine h2.congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc n),
      show (x : ℂ) + n - 1 / 24 = ((x + n - 1 / 24 : ℝ) : ℂ) by push_cast; ring,
      norm_cexp_two_pi_I_mul]
    simp only [Complex.I_im, mul_one]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  refine ⟨∑' n, g n, fun τ hτ => ?_⟩
  have hb : HasSum (fun n => Real.exp (2 * Real.pi * τ.im / 24) * g n)
      (Real.exp (2 * Real.pi * τ.im / 24) * ∑' n, g n) := hg.hasSum.mul_left _
  rw [mul_comm]
  refine (hf τ (by linarith)).norm_le_of_bounded hb fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc n),
    show (x : ℂ) + n - 1 / 24 = ((x + n - 1 / 24 : ℝ) : ℂ) by push_cast; ring,
    norm_cexp_two_pi_I_mul, mul_left_comm, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc n)
  have : 0 ≤ 2 * Real.pi * (x + n) := by positivity
  nlinarith

/-- `‖η(τ)‖ ≤ P e^{-2π Im τ/24}` on `Im τ ≥ 1`. -/
theorem norm_eta_le : ∃ P : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
    ‖ModularForm.eta τ‖ ≤ P * Real.exp (-(2 * Real.pi * τ.im / 24)) := by
  set ρ : ℝ := Real.exp (-(2 * Real.pi))
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  have hK : IsCompact (Metric.closedBall (0 : ℂ) ρ) := isCompact_closedBall 0 ρ
  have hsub : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball hρ1
  obtain ⟨P, hP⟩ := hK.exists_bound_of_continuousOn
    (ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn.mono hsub)
  refine ⟨P, fun τ hτ => ?_⟩
  have hq : cexp (2 * Real.pi * I * τ) ∈ Metric.closedBall (0 : ℂ) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right,
      show (2 * Real.pi * I * τ) = 2 * Real.pi * I * ((1 : ℝ) : ℂ) * τ by push_cast; ring,
      norm_cexp_two_pi_I_mul]
    exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  have h1 := hP _ hq
  unfold ModularForm.eta
  rw [norm_mul, mul_comm]
  simp_rw [ModularForm.eta_q_eq_pow]
  refine mul_le_mul h1 (le_of_eq ?_) (norm_nonneg _) ((norm_nonneg _).trans h1)
  rw [Function.Periodic.qParam, show 2 * (Real.pi : ℂ) * I * τ / ((24 : ℝ) : ℂ) =
    2 * Real.pi * I * ((1 / 24 : ℝ) : ℂ) * τ by push_cast; ring, norm_cexp_two_pi_I_mul]
  congr 1
  ring

/-- `‖η(γτ)‖ = ‖cτ + d‖^{1/2} ‖η(τ)‖` for every `γ ∈ SL₂(ℤ)` (from `Δ = η²⁴`). -/
theorem norm_eta_mobius (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖ModularForm.eta (mobius γ τ)‖ =
      ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) * ‖ModularForm.eta τ‖ := by
  set z : ℍ := ⟨τ, hτ⟩
  have hs := congrFun (SlashInvariantForm.slash_action_generators_SL2Z
    ModularForm.discriminant_S_invariant ModularForm.discriminant_T_invariant γ) z
  rw [ModularForm.SL_slash_apply] at hs
  have hden : denom γ z = (γ 1 0 : ℂ) * τ + γ 1 1 := by simp [denom, z]
  have hd0 : denom γ z ≠ 0 := denom_ne_zero γ z
  have h24 : ModularForm.eta (mobius γ τ) ^ 24 =
      ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 12 * ModularForm.eta τ ^ 24 := by
    have e1 : ModularForm.discriminant (γ • z) = ModularForm.eta (mobius γ τ) ^ 24 := by
      rw [ModularForm.discriminant, ← mobius_eq_smul]
    have e2 : ModularForm.discriminant z = ModularForm.eta τ ^ 24 := rfl
    rw [e1, e2, hden] at hs
    rw [← hden] at hs ⊢
    rw [zpow_neg, zpow_ofNat] at hs
    rw [← hs]
    field_simp
  have hn := congrArg norm h24
  simp only [norm_pow, norm_mul] at hn
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) (by norm_num : (24 : ℕ) ≠ 0)).1 ?_
  rw [hn, mul_pow, ← Real.rpow_natCast (‖_‖ ^ (1 / 2 : ℝ)), ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-! ## The multiplier on `Γ₁(N)` -/

theorem modEq_of_zmod {N : ℕ} {a b : ℤ} (h : (a : ZMod N) = b) : a ≡ b [ZMOD N] :=
  (ZMod.intCast_eq_intCast_iff a b N).1 h

/-- GR (3.11) from `ThetaGaloisLaw`: `η(γτ) θ(τ) = θ(γτ) η(τ)` for `γ ∈ Γ(M)`, `24 ∣ M`. -/
theorem eta_theta_of_thetaGaloisLaw (hL : ThetaGaloisLaw) {M : ℕ} (hM : 24 ∣ M)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma M) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ModularForm.eta (mobius γ τ) * thetaRef τ = thetaRef (mobius γ τ) * ModularForm.eta τ := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  have h4 : 4 * 1 * 1 ^ 2 ∣ M := (show 4 * 1 * 1 ^ 2 ∣ 24 by norm_num).trans hM
  have key := hL 0 1 1 M one_pos one_pos h4 hM 1 (Nat.coprime_one_left M) 1 (by simp)
    γ (by simpa using modEq_of_zmod (by simpa using h00))
    (by simpa using modEq_of_zmod (by simpa using h11))
    (modEq_of_zmod (by simpa using h01)) (modEq_of_zmod (by simpa using h10)) τ hτ
  simp only [thetaRef, Nat.cast_one, Int.cast_one, mul_zero, jacobiSym.one_right,
    Int.cast_one, one_mul] at key ⊢
  rw [mul_comm, key, mul_comm]

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

theorem IsLevel.twentyFour_dvd (hD : D.IsModularData) (hc : V.centralCharge = 1) {N : ℕ}
    (hN : D.IsLevel N) : 24 ∣ N := by
  obtain ⟨k, hk⟩ := hN.2 D.vac
  rw [hD.h_vac, hc] at hk
  have hk' : (N : ℂ) = 24 * (-k : ℤ) := by push_cast; linear_combination (-24 : ℂ) * hk
  have : (N : ℤ) = 24 * (-k) := by exact_mod_cast hk'
  exact Int.natCast_dvd_natCast.1 ⟨-k, this⟩

/-- **The multiplier of `F_V = η ch_V` on `Γ₁(N)`** (GR proof of Lemma 3.7). -/
theorem IsModularData.multiplier_of_thetaGaloisLaw (hL : ThetaGaloisLaw) (hD : D.IsModularData)
    (hc : V.centralCharge = 1) {N : ℕ} (hN : D.IsLevel N)
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ a (τ : ℂ), 0 < τ.im →
      D.ch a (mobius γ τ) = D.ch a τ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ModularForm.eta (mobius γ τ) * D.ch D.vac (mobius γ τ) * thetaRef τ =
      thetaRef (mobius γ τ) * (ModularForm.eta τ * D.ch D.vac τ) := by
  set b : ℤ := γ 0 1
  set δ := γ * ModularGroup.T ^ (-b) with hδ
  have hγδ : γ = δ * ModularGroup.T ^ b := by rw [hδ, mul_assoc, ← zpow_add, neg_add_cancel,
    zpow_zero, mul_one]
  have hδΓ : δ ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma1_mem] at hγ
    obtain ⟨h00, h11, h10⟩ := hγ
    rw [CongruenceSubgroup.Gamma_mem]
    have e : ∀ i j, δ i j = ∑ k, γ i k * (ModularGroup.T ^ (-b)) k j := fun i j => by
      rw [hδ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    simp only [e, ModularGroup.coe_T_zpow, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    refine ⟨by simp [h00], ?_, by simp [h10], by simp [h10, h11]⟩
    rw [h00]; simp [b]
  have hτb : 0 < (τ + b).im := by simpa using hτ
  have hm : mobius γ τ = mobius δ (τ + b) := by
    rw [hγδ, mobius_mul _ _ hτ, mobius_T_zpow]
  have hinv := hΓ δ hδΓ D.vac (τ + b) hτb
  have hη := eta_theta_of_thetaGaloisLaw hL (IsLevel.twentyFour_dvd hD hc hN) hδΓ hτb
  rw [hm, hinv, ← thetaRef_add_int τ b, ← hD.F_add_int hc hτ b]
  linear_combination (D.ch D.vac (τ + b)) * hη

end ModularData

/-! ## Lemma 3.7: holomorphy and the cusps -/

theorem mobius_S (τ : ℂ) : mobius ModularGroup.S τ = -1 / τ := by
  simp [mobius, ModularGroup.S]

theorem mobius_S_inv (τ : ℂ) : mobius ModularGroup.S⁻¹ τ = -1 / τ := by
  simp [mobius, ModularGroup.S, Matrix.SpecialLinearGroup.SL2_inv_expl, neg_div]

theorem mobius_T_inv (τ : ℂ) : mobius ModularGroup.T⁻¹ τ = τ + (-1 : ℤ) := by
  rw [← zpow_neg_one, mobius_T_zpow]

theorem mobius_T (τ : ℂ) : mobius ModularGroup.T τ = τ + (1 : ℕ) := by
  rw [← zpow_one ModularGroup.T, mobius_T_zpow]; simp

theorem mobius_one (τ : ℂ) : mobius 1 τ = τ := by
  simp [mobius]

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

/-- **`ch ∘ γ` is a combination of characters** for every `γ ∈ SL₂(ℤ)` (from `S_transform`,
`ch_add_nat` and `SL₂(ℤ) = ⟨S, T⟩`). -/
theorem IsModularData.exists_ch_comp (hD : D.IsModularData)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ Mx : D.ι → D.ι → ℂ, ∀ a (τ : ℂ), 0 < τ.im →
      D.ch a (mobius γ τ) = ∑ b, Mx a b * D.ch b τ := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  set e : D.ι → ℂ := fun a => cexp (2 * Real.pi * I * ((D.h a : ℂ) - V.centralCharge / 24))
  have hT : ∀ a (τ : ℂ), 0 < τ.im → D.ch a (τ + (1 : ℕ)) = e a * D.ch a τ := by
    intro a τ hτ
    rw [hD.ch_add_nat a 1 hτ]; simp [e]
  have hdiag : ∀ (f : D.ι → ℂ) a (τ : ℂ),
      f a * D.ch a τ = ∑ b, (if a = b then f a else 0) * D.ch b τ := by
    intro f a τ
    simp
  induction hγ using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨D.S, fun a τ hτ => by rw [mobius_S, hD.S_transform a τ hτ]⟩
    · exact ⟨fun a b => if a = b then e a else 0, fun a τ hτ => by
        rw [mobius_T, hT a τ hτ, hdiag]⟩
  | inv_mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨D.S, fun a τ hτ => by rw [mobius_S_inv, hD.S_transform a τ hτ]⟩
    · refine ⟨fun a b => if a = b then (e a)⁻¹ else 0, fun a τ hτ => ?_⟩
      have h1 : 0 < (τ + (-1 : ℤ)).im := by simpa using hτ
      have h := hT a _ h1
      rw [show τ + ((-1 : ℤ) : ℂ) + ((1 : ℕ) : ℂ) = τ by push_cast; ring] at h
      have he : e a ≠ 0 := Complex.exp_ne_zero _
      rw [mobius_T_inv, ← hdiag (fun a => (e a)⁻¹), h]
      field_simp
  | one => exact ⟨fun a b => if a = b then 1 else 0, fun a τ _ => by
      rw [mobius_one, ← hdiag (fun _ => 1)]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Mx, hMx⟩ := hx
    obtain ⟨My, hMy⟩ := hy
    refine ⟨fun a c => ∑ b, Mx a b * My b c, fun a τ hτ => ?_⟩
    rw [mobius_mul _ _ hτ, hMx a _ (im_mobius_pos y hτ)]
    simp_rw [hMy _ τ hτ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring

/-- `‖η ch_b‖` is bounded on `Im τ ≥ 1` (pseudo-unitarity: `h_b ≥ 0`). -/
theorem IsModularData.norm_eta_mul_ch_le (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) (b : D.ι) :
    ∃ K : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖ModularForm.eta τ‖ * ‖D.ch b τ‖ ≤ K := by
  obtain ⟨P, hP⟩ := norm_eta_le
  obtain ⟨K, hK⟩ := norm_qseries_le
    (fun n => (finrank ℂ ((D.module b).weight ((D.h b : ℂ) + n)) : ℝ)) (fun n => by positivity)
    (D.h b) (by exact_mod_cast hD.h_nonneg hV b) (D.ch b) fun τ hτ => by
      have h := hD.char b τ hτ
      rw [hc] at h
      refine h.congr_fun fun n => ?_
      push_cast
      ring_nf
  refine ⟨P * K, fun τ hτ => ?_⟩
  have h1 := hP τ hτ
  have h2 := hK τ hτ
  calc ‖ModularForm.eta τ‖ * ‖D.ch b τ‖
      ≤ (P * Real.exp (-(2 * Real.pi * τ.im / 24))) *
        (K * Real.exp (2 * Real.pi * τ.im / 24)) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = P * K := by
        rw [show (P * Real.exp (-(2 * Real.pi * τ.im / 24))) *
          (K * Real.exp (2 * Real.pi * τ.im / 24)) = P * K *
            (Real.exp (-(2 * Real.pi * τ.im / 24)) * Real.exp (2 * Real.pi * τ.im / 24)) by ring,
          ← Real.exp_add]
        simp

/-- **The cusp condition of Lemma 3.7.** -/
theorem IsModularData.cusp_bound (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖ModularForm.eta (mobius γ τ) * D.ch D.vac (mobius γ τ)‖ ≤
        C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Mx, hMx⟩ := hD.exists_ch_comp γ
  choose K hK using fun b => hD.norm_eta_mul_ch_le hV hc b
  refine ⟨∑ b, ‖Mx D.vac b‖ * K b, fun τ hτ => ?_⟩
  have hτ' : 0 < τ.im := by linarith
  set j := ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ)
  have hj : 0 ≤ j := by positivity
  rw [norm_mul, norm_eta_mobius γ hτ', hMx D.vac τ hτ']
  have hs : ‖ModularForm.eta τ‖ * ‖∑ b, Mx D.vac b * D.ch b τ‖ ≤ ∑ b, ‖Mx D.vac b‖ * K b := by
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [norm_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hK b τ hτ) (norm_nonneg _)
  calc j * ‖ModularForm.eta τ‖ * ‖∑ b, Mx D.vac b * D.ch b τ‖
      = j * (‖ModularForm.eta τ‖ * ‖∑ b, Mx D.vac b * D.ch b τ‖) := by ring
    _ ≤ j * ∑ b, ‖Mx D.vac b‖ * K b := mul_le_mul_of_nonneg_left hs hj
    _ = (∑ b, ‖Mx D.vac b‖ * K b) * j := by ring

/-- **Holomorphy of `F_V = η ch_V` on `ℍ`.** -/
theorem IsModularData.differentiableOn_eta_mul_ch (hD : D.IsModularData)
    (hc : V.centralCharge = 1) :
    DifferentiableOn ℂ (fun τ => ModularForm.eta τ * D.ch D.vac τ) {τ : ℂ | 0 < τ.im} := by
  have hch : DifferentiableOn ℂ (D.ch D.vac) {τ : ℂ | 0 < τ.im} :=
    differentiableOn_qseries (fun n => (finrank ℂ (V.grading n) : ℝ)) (fun n => by positivity)
      (-1 / 24) (D.ch D.vac) fun τ hτ => by
        have h := hD.char_vac τ hτ
        rw [hc] at h
        refine h.congr_fun fun n => ?_
        push_cast
        ring_nf
  refine DifferentiableOn.mul (fun τ hτ => ?_) hch
  exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hτ).differentiableWithinAt

end ModularData

/-- **GR Lemma 3.7, from the theta Galois law.** `#print axioms`-clean, conditional on
`ThetaGaloisLaw` (only its `ℓ = 1`, `θ_{0,1,1}` case, i.e. GR (3.11), is used). -/
theorem gapLemma37_of_thetaGaloisLaw (hL : ThetaGaloisLaw) : GapLemma37.{u} := by
  intro 𝒱 _ _ V hV hc D hD N hN hΓ
  refine ⟨hD.differentiableOn_eta_mul_ch hc, fun γ hγ τ hτ => ?_, fun γ => ?_⟩
  · exact hD.multiplier_of_thetaGaloisLaw hL hc hN hΓ γ hγ hτ
  · exact hD.cusp_bound hV hc γ

/-! ## The Galois bound, GR (3.31)–(3.35) -/

/-- An explicit `γ_ℓ ∈ SL₂(ℤ)` with `γ_ℓ ≡ diag(ℓ, ℓ') (mod N)`, `ℓ ℓ' ≡ 1 (mod N)`:
`γ_ℓ = (ℓ, -N y; N, x)` from Bézout `ℓ x + N² y = 1`. -/
theorem exists_gamma_diag {N ℓ : ℕ} (hℓ : ℓ.Coprime N) :
    ∃ (ℓ' : ℤ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ), (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD N] ∧
      γ 0 0 ≡ ℓ [ZMOD N] ∧ γ 1 1 ≡ ℓ' [ZMOD N] ∧ γ 0 1 ≡ 0 [ZMOD N] ∧ γ 1 0 ≡ 0 [ZMOD N] := by
  have h2 : ℓ.Coprime (N ^ 2) := Nat.Coprime.pow_right 2 hℓ
  have hb := Nat.gcd_eq_gcd_ab ℓ (N ^ 2)
  rw [h2.gcd_eq_one] at hb
  set x := ℓ.gcdA (N ^ 2)
  set y := ℓ.gcdB (N ^ 2)
  push_cast at hb
  have hdet : Matrix.det !![(ℓ : ℤ), -((N : ℤ) * y); (N : ℤ), x] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination -hb
  refine ⟨x, ⟨!![(ℓ : ℤ), -((N : ℤ) * y); (N : ℤ), x], hdet⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Int.modEq_iff_dvd.2 ⟨-(N : ℤ) * y, by linear_combination -hb⟩).symm
  · simp
  · simp
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact Int.modEq_iff_dvd.2 ⟨y, by ring⟩
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact Int.modEq_iff_dvd.2 ⟨-1, by ring⟩

/-- `Proj_ℤ` of a combination of `S`-transformed theta quotients (as in GR Lemma 3.10, with
arbitrary residues `n t j`): only the `q^{-1/24}`-sector `θ_{0,1,t}/η` survives. -/
theorem projZ_theta_S {N : ℕ} (hN : 0 < N) (T : Finset ℕ) (hT : ∀ t ∈ T, Squarefree t)
    (r : ℕ → ℕ) [∀ t, NeZero (r t)] (hrN : ∀ t ∈ T, 4 * t * r t ^ 2 ∣ N)
    (b : (t : ℕ) → ZMod (r t) → ℂ) (n : (t : ℕ) → ZMod (r t) → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    projZ N 1 (fun τ => ∑ t ∈ T, ∑ j : ZMod (r t), b t j *
      (rankOneTheta (n t j) (r t) t (-1 / τ) / ModularForm.eta (-1 / τ))) τ =
    ∑ t ∈ T, (1 / ((r t : ℂ) * (Real.sqrt (2 * t) : ℂ)) * ∑ j : ZMod (r t), b t j) *
      (rankOneTheta 0 1 t τ / ModularForm.eta τ) := by
  have hS : ∀ τ' : ℂ, 0 < τ'.im → (∑ t ∈ T, ∑ j : ZMod (r t), b t j *
      (rankOneTheta (n t j) (r t) t (-1 / τ') / ModularForm.eta (-1 / τ'))) =
      ∑ t ∈ T, ∑ j : ZMod (r t), b t j *
        ((((Real.sqrt (2 * (t : ℝ) * ((r t : ℕ) : ℝ) ^ 2))⁻¹ : ℝ) : ℂ) *
          ∑ i : Fin (r t), cexp (2 * Real.pi * I * (i : ℕ) * (n t j) / (r t : ℕ)) *
            (rankOneTheta (i : ℕ) (r t) (1 / (4 * (t : ℝ) * ((r t : ℕ) : ℝ) ^ 2)) τ' /
              ModularForm.eta τ')) := by
    intro τ' hτ'
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun j _ => ?_
    have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero (hT t ht).ne_zero
    rw [theta_div_eta_S _ (r t) htpos hτ']
  rw [projZ_congr hS hτ, projZ_sum T]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [projZ_sum, projZ_const_mul]
  have hrpos : 0 < r t := Nat.pos_of_ne_zero (NeZero.ne _)
  have hproj : ∀ i : Fin (r t), projZ N 1 (fun τ => rankOneTheta (i : ℕ) (r t)
      (1 / (4 * (t : ℝ) * ((r t : ℕ) : ℝ) ^ 2)) τ / ModularForm.eta τ) τ =
      (if (i : ℕ) = 0 then rankOneTheta 0 1 t τ else 0) / ModularForm.eta τ :=
    fun i => projZ_theta_div_eta hN (hT t ht) hrpos (hrN t ht) i.2 hτ
  simp only [hproj]
  have hi : ∀ j : ZMod (r t), ∑ i : Fin (r t),
      cexp (2 * Real.pi * I * (i : ℕ) * (n t j) / (r t : ℕ)) *
        ((if (i : ℕ) = 0 then rankOneTheta 0 1 t τ else 0) / ModularForm.eta τ) =
      rankOneTheta 0 1 t τ / ModularForm.eta τ := by
    intro j
    rw [Fintype.sum_eq_single ⟨0, hrpos⟩]
    · simp
    · intro i hi0
      have : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
      simp [this]
  simp only [hi]
  rw [inv_sqrt_two_mul_sq _ (Nat.cast_nonneg _), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `q^{1/24} θ_{0,1,t}/η → 1` at `τ = iy`, `y → ∞`. -/
theorem tendsto_theta01_div_eta {t : ℕ} (ht : 0 < t) :
    Tendsto (fun y : ℝ => ((Real.exp (-(2 * Real.pi * y * 1 / 24)) : ℝ) : ℂ) *
      (rankOneTheta 0 1 t ((y : ℂ) * I) / ModularForm.eta ((y : ℂ) * I))) atTop (𝓝 1) := by
  -- the product `∏ (1 - qⁿ⁺¹)` at `q = e^{-2πy}`
  set g : ℂ → ℂ := fun q => ∏' n : ℕ, (1 - q ^ (n + 1))
  have hg0 : g 0 = 1 := by simp [g]
  have hgc : ContinuousAt g 0 :=
    (ModularForm.differentiableOn_tprod_one_sub_pow.differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))).continuousAt
  have hq : Tendsto (fun y : ℝ => cexp (2 * Real.pi * I * ((y : ℂ) * I))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : ∀ y : ℝ, ‖cexp (2 * Real.pi * I * ((y : ℂ) * I))‖ = Real.exp (-(2 * Real.pi * y)) := by
      intro y
      rw [show 2 * Real.pi * I * ((y : ℂ) * I) = 2 * Real.pi * I * ((1 : ℝ) : ℂ) * ((y : ℂ) * I)
        by push_cast; ring, norm_cexp_two_pi_I_mul]
      simp
    simp_rw [this]
    have hb : Tendsto (fun y : ℝ => -(2 * Real.pi) * y) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
    refine (Real.tendsto_exp_atBot.comp hb).congr fun y => ?_
    simp only [Function.comp_apply]
    ring_nf
  have hP : Tendsto (fun y : ℝ => g (cexp (2 * Real.pi * I * ((y : ℂ) * I)))) atTop (𝓝 1) := by
    rw [← hg0]; exact hgc.tendsto.comp hq
  -- theta
  have hJ : Tendsto jacobiTheta (Filter.comap Complex.im atTop) (𝓝 1) := by
    have h := isBigO_at_im_infty_jacobiTheta_sub_one
    have h0 : Tendsto (fun τ : ℂ => Real.exp (-Real.pi * τ.im)) (Filter.comap Complex.im atTop)
        (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_comap.const_mul_atTop_of_neg (by linarith [Real.pi_pos]))
    have := h.trans_tendsto h0
    simpa using this.add_const 1
  have hθ : Tendsto (fun y : ℝ => rankOneTheta 0 1 t ((y : ℂ) * I)) atTop (𝓝 1) := by
    have hmap : Tendsto (fun y : ℝ => 2 * (t : ℂ) * ((y : ℂ) * I)) atTop
        (Filter.comap Complex.im atTop) := by
      rw [tendsto_comap_iff]
      have htp : (0 : ℝ) < 2 * t := by positivity
      refine (tendsto_id.const_mul_atTop htp).congr fun y => ?_
      simp
    refine (hJ.comp hmap).congr fun y => ?_
    simp only [Function.comp_apply, rankOneTheta_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂]
    simp
  have hdiv := hθ.div hP one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ((eventually_gt_atTop 0).mono fun y hy => ?_)
  have hη : ModularForm.eta ((y : ℂ) * I) =
      ((Real.exp (-(2 * Real.pi * y * 1 / 24)) : ℝ) : ℂ) *
        g (cexp (2 * Real.pi * I * ((y : ℂ) * I))) := by
    unfold ModularForm.eta
    simp_rw [ModularForm.eta_q_eq_pow]
    congr 1
    rw [Function.Periodic.qParam, Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hP0 : g (cexp (2 * Real.pi * I * ((y : ℂ) * I))) ≠ 0 := by
    have := ModularForm.eta_tprod_ne_zero (z := (y : ℂ) * I) (by simpa using hy)
    simp_rw [ModularForm.eta_q_eq_pow] at this
    exact this
  have he : ((Real.exp (-(2 * Real.pi * y * 1 / 24)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  simp only [Pi.div_apply]
  rw [hη]
  field_simp

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
  {D : ModularData V}

/-- `Proj_ℤ` of `z · ch_a(-1/τ)`: `z Σ_{h_b ∈ ℤ} S_{ab} ch_b(τ)`. -/
theorem IsModularData.projZ_S_label (hD : D.IsModularData) {N : ℕ} (hN : D.IsLevel N)
    (a : D.ι) (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    projZ N V.centralCharge (fun τ => z * D.ch a (-1 / τ)) τ =
      z * ∑ b ∈ D.intLabels, D.S a b * D.ch b τ := by
  rw [projZ_const_mul N V.centralCharge z (fun τ => D.ch a (-1 / τ)) τ,
    projZ_congr (g := fun τ => ∑ b, D.S a b * D.ch b τ)
      (fun τ hτ => hD.S_transform a τ hτ) hτ, projZ_sum]
  simp only [projZ_const_mul, hD.projZ_ch hN _ hτ, intLabels, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

/-- The leading `q^{-1/24}` coefficient of `Σ_{h_b∈ℤ} S_{ab} ch_b` is `S_{a,vac}`. -/
theorem IsModularData.tendsto_S_int (hD : D.IsModularData) (hV : Nice V)
    (hc : V.centralCharge = 1) (a : D.ι) (z : ℂ) :
    Tendsto (fun y : ℝ => ((Real.exp (-(2 * Real.pi * y * 1 / 24)) : ℝ) : ℂ) *
      (z * ∑ b ∈ D.intLabels, D.S a b * D.ch b ((y : ℂ) * I))) atTop
      (𝓝 (z * D.S a D.vac)) := by
  have hlim : Tendsto (fun y : ℝ => z * ∑ b ∈ D.intLabels, D.S a b *
      (((Real.exp (-(2 * Real.pi * y * 1 / 24)) * D.chR b y : ℝ)) : ℂ)) atTop
      (𝓝 (z * ∑ b ∈ D.intLabels, D.S a b * (((if b = D.vac then 1 else 0 : ℝ)) : ℂ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun b _ => Tendsto.const_mul _ ?_)
    exact (Complex.continuous_ofReal.tendsto _).comp (hD.tendsto_chR hV hc b)
  have hv : ∑ b ∈ D.intLabels, D.S a b * (((if b = D.vac then 1 else 0 : ℝ)) : ℂ) =
      D.S a D.vac := by
    rw [Finset.sum_eq_single D.vac]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hD.vac_mem_intLabels h
  rw [hv] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun y hy => ?_)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [(hD.char_imag hc b hy).2]
  push_cast
  ring

end ModularData

/-- **GR (3.31)–(3.35), from the theta Galois law.** `#print axioms`-clean, conditional on
`ThetaGaloisLaw`. -/
theorem gapGaloisBound_of_thetaGaloisLaw (hL : ThetaGaloisLaw) : GapGaloisBound.{u} := by
  intro 𝒱 _ _ V hV hc D hD N hN hGal T R a hT hdec ℓ hℓ
  have h24 : 24 ∣ N := ModularData.IsLevel.twentyFour_dvd hD hc hN
  obtain ⟨ℓ', γ, hℓℓ', h00, h11, h01, h10⟩ := exists_gamma_diag hℓ
  obtain ⟨π, ε, hε, hπ⟩ := hGal ℓ ℓ' hℓℓ' γ h00 h11 h01 h10
  set χ : ℕ → ℂ := fun t => (jacobiSym (2 * (t : ℤ)) ℓ : ℂ)
  -- (3.31) = (3.32) at `σ = -1/τ`
  have hid : ∀ τ : ℂ, 0 < τ.im → ε D.vac * D.ch (π D.vac) (-1 / τ) =
      ∑ t ∈ T, ∑ j : ZMod (R t), (χ t * a t j) *
        (rankOneTheta ((ℓ : ℤ) * ((j.val : ℕ) : ℤ)) (R t : ℕ) t (-1 / τ) /
          ModularForm.eta (-1 / τ)) := by
    intro τ hτ
    have hσ := im_neg_one_div_pos hτ
    set σ := -1 / τ with hσdef
    clear_value σ
    have hγσ := im_mobius_pos γ hσ
    have hη1 := ModularForm.eta_ne_zero hγσ
    have hη2 := ModularForm.eta_ne_zero hσ
    rw [← hπ D.vac _ hσ]
    have h := hdec _ hγσ
    rw [mul_comm, ← eq_div_iff hη1, Finset.sum_div] at h
    rw [h]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have htpos : 0 < t := Nat.pos_of_ne_zero (hT t ht).1.ne_zero
    have hG := hL ((j.val : ℕ) : ℤ) (R t : ℕ) t N (R t).pos htpos (hT t ht).2 h24 ℓ hℓ ℓ'
      hℓℓ' γ h00 h11 h01 h10 _ hσ
    field_simp
    simp only [χ]
    linear_combination (a t j) * hG
  -- `Proj_ℤ` of both sides
  have hproj : ∀ τ : ℂ, 0 < τ.im →
      ε D.vac * ∑ b ∈ D.intLabels, D.S (π D.vac) b * D.ch b τ =
        ∑ t ∈ T, (χ t * ((1 / ((R t : ℕ) : ℂ) / (Real.sqrt (2 * t) : ℂ)) *
          ∑ j : ZMod (R t), a t j)) * (rankOneTheta 0 1 t τ / ModularForm.eta τ) := by
    intro τ hτ
    rw [← hD.projZ_S_label hN (π D.vac) (ε D.vac) hτ, hc,
      projZ_congr (g := fun τ => ∑ t ∈ T, ∑ j : ZMod (R t), (χ t * a t j) *
        (rankOneTheta ((ℓ : ℤ) * ((j.val : ℕ) : ℤ)) (R t : ℕ) t (-1 / τ) /
          ModularForm.eta (-1 / τ))) hid hτ,
      projZ_theta_S hN.1 T (fun t ht => (hT t ht).1) (fun t => (R t : ℕ))
        (fun t ht => (hT t ht).2) (fun t j => χ t * a t j) _ hτ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
    ring
  -- the leading coefficient
  have hL1 := hD.tendsto_S_int hV hc (π D.vac) (ε D.vac)
  have hL2 : Tendsto (fun y : ℝ => ((Real.exp (-(2 * Real.pi * y * 1 / 24)) : ℝ) : ℂ) *
      (ε D.vac * ∑ b ∈ D.intLabels, D.S (π D.vac) b * D.ch b ((y : ℂ) * I))) atTop
      (𝓝 (∑ t ∈ T, (χ t * ((1 / ((R t : ℕ) : ℂ) / (Real.sqrt (2 * t) : ℂ)) *
          ∑ j : ZMod (R t), a t j)) * 1)) := by
    have := tendsto_finsetSum T fun t ht => (tendsto_theta01_div_eta
      (Nat.pos_of_ne_zero (hT t ht).1.ne_zero)).const_mul
      (χ t * ((1 / ((R t : ℕ) : ℂ) / (Real.sqrt (2 * t) : ℂ)) * ∑ j : ZMod (R t), a t j))
    refine this.congr' ((eventually_gt_atTop 0).mono fun y hy => ?_)
    dsimp only
    rw [hproj _ (by simpa using hy), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have heq := tendsto_nhds_unique hL1 hL2
  simp only [mul_one] at heq
  have hnorm : ‖ε D.vac‖ = 1 := by
    rcases hε D.vac with h | h <;> simp [h]
  have hS := hD.S_vac_right (π D.vac)
  have hd := hD.d_ge_one (π D.vac)
  have hS0 := hD.S00_pos
  have key : ‖∑ t ∈ T, χ t * ((1 / ((R t : ℂ) * (Real.sqrt (2 * t) : ℂ))) *
      ∑ j : ZMod (R t), a t j)‖ = D.S00 * D.d (π D.vac) := by
    have : ∑ t ∈ T, χ t * ((1 / ((R t : ℂ) * (Real.sqrt (2 * t) : ℂ))) *
        ∑ j : ZMod (R t), a t j) = ε D.vac * D.S (π D.vac) D.vac := by
      rw [heq]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    rw [this, norm_mul, hnorm, one_mul, hS, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith)]
  rw [key]
  nlinarith


/-- Both paper gaps of `Conditional.lean` follow from the single named classical input. -/
theorem paperGaps_of_thetaGaloisLaw (hL : ThetaGaloisLaw) :
    GapLemma37.{u} ∧ GapGaloisBound.{u} :=
  ⟨gapLemma37_of_thetaGaloisLaw hL, gapGaloisBound_of_thetaGaloisLaw hL⟩

end VOA.Classification.COne
