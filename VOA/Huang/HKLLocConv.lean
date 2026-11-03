/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLLocPsi

/-!
# HKL locality, per test: the product and reversed product agree after `(z₁ - z₂)ᴺ`

`(z₁ - z₂)ᴺ ⟨f, Y_W(a, z₁) Y_W(b, z₂) c⟩ = (z₁ - z₂)ᴺ ⟨f, Y_W(b, z₂) Y_W(a, z₁) c⟩`.

For an integral four-point test `d = (a, b, c; f)` the two Laurent coefficient sequences

* `sA n = prodCoef (prodOp μ) d (δ - α - n)` — `⟨f, a_{-n-1} b_{α+β+γ-δ+n-1} c⟩`, the expansion at
  `ζ = ∞` of the product `ζ ↦ ⟨f, Y_W(a, ζ) Y_W(b, 1) c⟩`,
* `tC n = prodCoef (prodOp μ) d.swapM (n + α + γ)` — `⟨f, b_{α+β+γ-δ+n-1} a_{-n-1} c⟩`, the
  expansion at `ζ = 0` of the reversed product `⟨f, Y_W(b, 1) Y_W(a, ζ) c⟩`,

agree after multiplication by `(ζ - 1)^{N₀}` (`conv_test`), `N₀` depending only on the
weights of `a`, `b` and the lowest weight of `A ⊠ A`.  Proof: the glued function `glueFun` of the
four channels (`HKLLocPsi`, `HKLLocGlue`) is holomorphic on `ℂ ∖ {0, 1}` (in `ζ = 1 + r`), equals
the two expansions on `‖ζ‖ > 1` and `0 < ‖ζ‖ < 1`, and equals the iterate channel near `ζ = 1`,
where the integral iterate exponents are bounded below by `-N₀`; then `conv_eq_of_glue`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLLoc

open CategoryTheory Filter Topology
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.HexagonClose VOA.Huang.HKLExt
open VOA.Huang.BraidingSkew
open Complex

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}
variable {F : FusionChoice V} {A : Ordinary V} {μ : tensorObj F A A ⟶ A}
  {d : FourPointTest A A A A}

/-! ## The two Laurent expansions -/

/-- Reindexing a `ℂ`-indexed sum with integral exponents by `ℤ`. -/
theorem hasSum_int_of_complex {c : ℂ → ℂ} {g : ℤ → ℂ} (hg : Function.Injective g)
    (hsupp : ∀ w, c w ≠ 0 → ∃ n, g n = w) {X : ℂ} (h : HasSum c X) :
    HasSum (fun n => c (g n)) X := by
  refine (hg.hasSum_iff fun w hw => ?_).2 h
  by_contra hc
  obtain ⟨n, rfl⟩ := hsupp w hc
  exact hw ⟨n, rfl⟩

variable (hV : StronglyRational V) (htw : (twistIso A).hom = 𝟙 A) (hd : IntTest d)
include hV htw hd

/-- The product expansion at `ζ = ∞`. -/
theorem hasSum_prodA {ζ : ℂ} (hζ : 1 < ‖ζ‖) :
    HasSum (fun n : ℤ => prodCoef F (prodOp F μ) d (d.δ - d.α - n) * ζ ^ n)
      (prodL F (prodOp F μ) d (Complex.log ζ)) := by
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ; linarith
  have hre : 0 < (Complex.log ζ).re := by rw [Complex.log_re]; exact Real.log_pos hζ
  have hs := (summable_prodL F hV (prodOp F μ) d hre).hasSum
  have h := hasSum_int_of_complex (g := fun n : ℤ => d.δ - d.α - n)
    (fun a b hab => by simpa using hab) (fun w hw => ?_) hs
  · refine h.congr_fun fun n => ?_
    simp only
    rw [show d.δ - d.α - (d.δ - d.α - (n : ℂ)) = n by ring, exp_int_mul_log n hζ0]
  · have hc : prodCoef F (prodOp F μ) d w ≠ 0 := fun h0 => hw (by rw [h0, zero_mul])
    obtain ⟨n, hn⟩ := prodL_exp_int htw hd w hc
    exact ⟨n, by simp only; rw [← hn]; ring⟩

/-- The reversed-product expansion at `ζ = 0`. -/
theorem hasSum_prodC {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : ‖ζ‖ < 1) :
    HasSum (fun n : ℤ => prodCoef F (prodOp F μ) d.swapM (n + d.α + d.γ) * ζ ^ n)
      (ED d (ζ - 1) * prodL F (prodOp F μ) d.swapM (Complex.log (1 / ζ))) := by
  obtain ⟨m, hm⟩ := hd.total
  have hζ1 : 1 < ‖1 / ζ‖ := by
    rw [norm_div, norm_one, one_lt_div (norm_pos_iff.2 hζ0)]; exact hζ
  have hre : 0 < (Complex.log (1 / ζ)).re := by rw [Complex.log_re]; exact Real.log_pos hζ1
  have hs := ((summable_prodL F hV (prodOp F μ) d.swapM hre).hasSum).mul_left (ED d (ζ - 1))
  have hED : ED d (ζ - 1) = ζ ^ m := by
    rw [ED, hm, show (1 : ℂ) + (ζ - 1) = ζ by ring, exp_int_mul_log m hζ0]
  have h := hasSum_int_of_complex (g := fun n : ℤ => n + d.α + d.γ)
    (fun a b hab => by simpa using hab) (fun w hw => ?_) hs
  · refine h.congr_fun fun n => ?_
    simp only
    have e : d.swapM.δ - d.swapM.α - ((n : ℂ) + d.α + d.γ) = ((m - n : ℤ) : ℂ) := by
      change d.δ - d.β - ((n : ℂ) + d.α + d.γ) = _
      push_cast; rw [← hm]; ring
    rw [hED, e, exp_int_mul_log _ (one_div_ne_zero hζ0), one_div, inv_zpow', neg_sub,
      mul_left_comm, ← zpow_add₀ hζ0]
    congr 2
    ring
  · have hc : prodCoef F (prodOp F μ) d.swapM w ≠ 0 := fun h0 => hw (by rw [h0, zero_mul, mul_zero])
    obtain ⟨k, hk⟩ := prodL_exp_int htw hd.swapM w hc
    refine ⟨m - k, ?_⟩
    change d.δ - d.β - w = _ at hk
    simp only
    push_cast
    rw [← hm, ← hk]; ring

/-! ## The pole bound at `ζ = 1` -/

omit htw in
include htw in
/-- The iterate channel has a pole of order `≤ N₀` at `ρ = 0`. -/
theorem iterL_pole_bound (N₀ : ℕ)
    (hN₀ : ∀ w : ℂ, (F A A).isMod.weight w ≠ ⊥ → (d.α + d.β).re - N₀ ≤ w.re) :
    ∃ C : ℝ, ∀ ρ : ℂ, ρ ≠ 0 → ‖ρ‖ ≤ 1 / 2 →
      ‖ρ ^ N₀ * iterL F (iterOp F μ) d.swapM (Complex.log ρ)‖ ≤ C := by
  set c := iterCoef F (iterOp F μ) d.swapM with hc
  have hsum := summable_norm_iterCoef F hV (iterOp F μ) d.swapM (r := 1 / 2) (by norm_num)
    (by norm_num)
  refine ⟨(1 / 2 : ℝ) ^ N₀ * ∑' w, ‖c w‖ * (1 / 2 : ℝ) ^ (w - d.swapM.α - d.swapM.β).re,
    fun ρ hρ0 hρ => ?_⟩
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hterm : ∀ w, ‖ρ ^ N₀ * (c w * Complex.exp ((w - d.swapM.α - d.swapM.β) * Complex.log ρ))‖
      ≤ (1 / 2 : ℝ) ^ N₀ * (‖c w‖ * (1 / 2 : ℝ) ^ (w - d.swapM.α - d.swapM.β).re) := by
    intro w
    by_cases hcw : c w = 0
    · rw [hcw]; simp
    have hwb : (F A A).isMod.weight w ≠ ⊥ := fun hb =>
      hcw (iterCoef_eq_zero_of_bot F (iterOp F μ) d.swapM hb)
    obtain ⟨n, hn⟩ := iterL_exp_int htw hd.swapM w hcw
    have hlow := hN₀ w hwb
    have hnlow : -(N₀ : ℤ) ≤ n := by
      have h1 : (w - d.swapM.α - d.swapM.β).re = (n : ℝ) := by rw [hn]; simp
      have h2 : (w - d.swapM.α - d.swapM.β).re = w.re - (d.α + d.β).re := by
        change (w - d.β - d.α).re = _
        simp; ring
      have : -(N₀ : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hre : (w - d.swapM.α - d.swapM.β).re = (n : ℝ) := by rw [hn]; simp
    rw [hn, exp_int_mul_log n hρ0, Complex.intCast_re, norm_mul, norm_mul, norm_pow, norm_zpow,
      Real.rpow_intCast]
    have hk : 0 ≤ n + N₀ := by omega
    obtain ⟨k, hk'⟩ : ∃ k : ℕ, n + N₀ = k := ⟨(n + N₀).toNat, (Int.toNat_of_nonneg hk).symm⟩
    have hn' : n = (k : ℤ) - N₀ := by omega
    have e1 : ‖ρ‖ ^ N₀ * ‖ρ‖ ^ n = ‖ρ‖ ^ k := by
      rw [hn', zpow_sub₀ hρpos.ne', zpow_natCast, zpow_natCast]
      field_simp
    have e2 : (1 / 2 : ℝ) ^ N₀ * (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ k := by
      rw [hn', zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
      field_simp
    have hpow : ‖ρ‖ ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ (norm_nonneg _) hρ k
    calc ‖ρ‖ ^ N₀ * (‖c w‖ * ‖ρ‖ ^ n) = ‖c w‖ * (‖ρ‖ ^ N₀ * ‖ρ‖ ^ n) := by ring
      _ = ‖c w‖ * ‖ρ‖ ^ k := by rw [e1]
      _ ≤ ‖c w‖ * (1 / 2 : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (1 / 2 : ℝ) ^ N₀ * (‖c w‖ * (1 / 2 : ℝ) ^ n) := by rw [← e2]; ring
  have hmaj : Summable fun w => (1 / 2 : ℝ) ^ N₀ *
      (‖c w‖ * (1 / 2 : ℝ) ^ (w - d.swapM.α - d.swapM.β).re) := hsum.mul_left _
  have hns := Summable.of_nonneg_of_le (fun w => norm_nonneg _) hterm hmaj
  have e : ρ ^ N₀ * iterL F (iterOp F μ) d.swapM (Complex.log ρ) =
      ∑' w, ρ ^ N₀ * (c w * Complex.exp ((w - d.swapM.α - d.swapM.β) * Complex.log ρ)) := by
    rw [iterL, tsum_mul_left]
  rw [e]
  refine (norm_tsum_le_tsum_norm hns).trans ?_
  refine (Summable.tsum_le_tsum hterm hns hmaj).trans ?_
  rw [tsum_mul_left]

/-! ## The per-test identity -/

variable (hcomm : (braiding F A A).hom ≫ μ = μ)
  (hassoc : tensorHom F μ (𝟙 A) ≫ μ =
    (evalAssoc F (ordinaryFourPointInput_pbw F hV) A A A).hom ≫ tensorHom F (𝟙 A) μ ≫ μ)

include hcomm hassoc in
/-- **Per-test locality**: the expansions of the product and the reversed product agree
after multiplication by `(ζ - 1)^{N₀}`. -/
theorem conv_test (N₀ : ℕ)
    (hN₀ : ∀ w : ℂ, (F A A).isMod.weight w ≠ ⊥ → (d.α + d.β).re - N₀ ≤ w.re) :
    ∀ k : ℤ, conv N₀ (fun n => prodCoef F (prodOp F μ) d (d.δ - d.α - n)) k =
      conv N₀ (fun n => prodCoef F (prodOp F μ) d.swapM (n + d.α + d.γ)) k := by
  obtain ⟨N, hN⟩ := exists_weight_bot A.isMod d.δ
  obtain ⟨Pp, hPa, hPA, hPC, hPB, hPD⟩ := exists_halfPlane_glue hV htw hd hcomm hassoc
    (s := 1) (Or.inl rfl) (p := Phase.upper.inv) (Or.inr rfl) phase_upper_inv_kap hN
  obtain ⟨Pm, hMa, hMA, hMC, hMB, hMD⟩ := exists_halfPlane_glue hV htw hd hcomm hassoc
    (s := -1) (Or.inr rfl) (p := Phase.upper) (Or.inl rfl) phase_upper_kap hN
  have hp : HalfGlue 1 Pp (chA F μ d) (chB F μ d N) (chC F μ d) (chD F μ d) :=
    ⟨hPa, hPA, hPC, hPB, hPD⟩
  have hm : HalfGlue (-1) Pm (chA F μ d) (chB F μ d N) (chC F μ d) (chD F μ d) :=
    ⟨hMa, hMA, hMC, hMB, hMD⟩
  have hc : ChannelsHolo (chA F μ d) (chB F μ d N) (chC F μ d) (chD F μ d) :=
    ⟨fun r h => differentiableAt_chA hV htw hd h, fun r h0 h => differentiableAt_chC hV htw hd h0 h,
      fun r h0 h => differentiableAt_chB hV htw hd N h0 h,
      fun r h0 h => differentiableAt_chD hV htw hd h0 h⟩
  set Ψ : ℂ → ℂ := fun ζ => glueFun (chA F μ d) (chB F μ d N) (chC F μ d) Pp Pm (ζ - 1) with hΨ
  -- supports
  obtain ⟨B, hB⟩ := (F A A).isMod.boundedBelow
  have hs0 : ∀ n : ℤ, ⌊(d.δ - d.α).re - B⌋ < n →
      prodCoef F (prodOp F μ) d (d.δ - d.α - n) = 0 := by
    intro n hn
    by_contra hne
    have hb := hB _ (fun hb => hne (prodCoef_eq_zero_of_bot F (prodOp F μ) d hb))
    have h1 : (d.δ - d.α - (n : ℂ)).re = (d.δ - d.α).re - n := by simp
    rw [h1] at hb
    have h2 := Int.floor_le ((d.δ - d.α).re - B)
    have h3 : ((⌊(d.δ - d.α).re - B⌋ + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h3
    linarith [Int.lt_floor_add_one ((d.δ - d.α).re - B)]
  have ht0 : ∀ n : ℤ, n < ⌈B - (d.α + d.γ).re⌉ →
      prodCoef F (prodOp F μ) d.swapM (n + d.α + d.γ) = 0 := by
    intro n hn
    by_contra hne
    have hb := hB _ (fun hb => hne (prodCoef_eq_zero_of_bot F (prodOp F μ) d.swapM hb))
    have h1 : ((n : ℂ) + d.α + d.γ).re = n + (d.α + d.γ).re := by simp; ring
    rw [h1] at hb
    have h3 : (n : ℝ) < ⌈B - (d.α + d.γ).re⌉ := by exact_mod_cast hn
    have h4 : (n : ℝ) + 1 ≤ ⌈B - (d.α + d.γ).re⌉ := by
      have : n + 1 ≤ ⌈B - (d.α + d.γ).re⌉ := hn
      exact_mod_cast this
    have h5 := Int.ceil_lt_add_one (B - (d.α + d.γ).re)
    linarith
  -- the pole bound
  obtain ⟨C₁, hC₁⟩ := iterL_pole_bound (μ := μ) hV htw hd N₀ hN₀
  have hcont : ContinuousOn (fun r : ℂ => ED d r * (1 + r) ^ N₀) (Metric.closedBall 0 (1 / 4)) := by
    intro r hr
    have h1 : 1 + r ≠ 0 := by
      intro h
      rw [Metric.mem_closedBall, dist_zero_right] at hr
      have : ‖r‖ = 1 := by rw [show r = -1 by linear_combination h]; simp
      linarith
    exact ((differentiableAt_ED hV htw hd h1).mul
      ((differentiableAt_const _).add differentiableAt_id |>.pow N₀)).continuousAt.continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := (isCompact_closedBall (0 : ℂ) (1 / 4)).exists_bound_of_continuousOn hcont
  refine conv_eq_of_glue (Ψ := Ψ) (n₀ := ⌊(d.δ - d.α).re - B⌋) (n₁ := ⌈B - (d.α + d.γ).re⌉)
    hs0 ht0 (fun ζ hζ => ?_) (fun ζ hζ0 hζ => ?_) (fun ζ h0 h1 => ?_) (ε := 1 / 4) (C := C₂ * C₁)
    (by norm_num) (fun ζ hζ1 hζ => ?_)
  · -- expansion at infinity
    have hn : 1 < ‖1 + (ζ - 1)‖ := by rwa [show (1 : ℂ) + (ζ - 1) = ζ by ring]
    rw [hΨ]
    simp only
    rw [glueFun_outside hn, chA, show (1 : ℂ) + (ζ - 1) = ζ by ring]
    exact hasSum_prodA hV htw hd hζ
  · -- expansion at zero
    have hn : ‖1 + (ζ - 1)‖ < 1 := by rwa [show (1 : ℂ) + (ζ - 1) = ζ by ring]
    rw [hΨ]
    simp only
    rw [glueFun_inside hn, chC, show (1 : ℂ) + (ζ - 1) = ζ by ring]
    exact hasSum_prodC hV htw hd hζ0 hζ
  · -- holomorphy
    have hd' := differentiableAt_glueFun hp hm hc (r := ζ - 1) (sub_ne_zero.2 h1)
      (by rwa [show (1 : ℂ) + (ζ - 1) = ζ by ring])
    exact hd'.comp ζ (differentiableAt_id.sub_const 1)
  · -- the pole bound
    have hr0 : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
    have hr : ‖ζ - 1‖ < 1 / 4 := hζ
    rw [hΨ]
    simp only
    rw [glueFun_eq_D hp hm hc hr0 hr, chD]
    set r := ζ - 1 with hrdef
    have h1 : 1 + r ≠ 0 := by
      intro h
      have : ‖r‖ = 1 := by rw [show r = -1 by linear_combination h]; simp
      linarith
    have hn1 : 3 / 4 ≤ ‖1 + r‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-r)
      rw [norm_one, norm_neg, sub_neg_eq_add] at this
      linarith
    set ρ := -(r / (1 + r)) with hρ
    have hρ0 : ρ ≠ 0 := neg_ne_zero.2 (div_ne_zero hr0 h1)
    have hρle : ‖ρ‖ ≤ 1 / 2 := by
      rw [hρ, norm_neg, norm_div, div_le_iff₀ (by linarith)]
      linarith
    have er : r = -ρ * (1 + r) := by rw [hρ]; field_simp
    have hcb := hC₂ r (by rw [Metric.mem_closedBall, dist_zero_right]; exact hr.le)
    have hib := hC₁ ρ hρ0 hρle
    have e : r ^ N₀ * (ED d r * iterL F (iterOp F μ) d.swapM (Complex.log ρ)) =
        (-1) ^ N₀ * (ED d r * (1 + r) ^ N₀) *
          (ρ ^ N₀ * iterL F (iterOp F μ) d.swapM (Complex.log ρ)) := by
      have hrpow : r ^ N₀ = (-1) ^ N₀ * ρ ^ N₀ * (1 + r) ^ N₀ := by
        conv_lhs => rw [er]
        rw [mul_pow, neg_pow]
      rw [hrpow]
      ring
    rw [e, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact mul_le_mul hcb hib (norm_nonneg _) ((norm_nonneg _).trans hcb)

end VOA.Huang.HKLLoc
