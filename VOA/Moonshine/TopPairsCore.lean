/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TopPairsArith

/-!
# `TopPairs`, part 2: the top-pair identity `Θ₀(o(v)Φ₀b) = o(b)Φ₀v` on `(V₃⁺)₂`

For the explicit triality data of `SigmaAssemble` (`Φ₀ = φ⋆` and `Θ₀ = φ_B` on the weight-2 tops),
both sides of the top-pair identity are computed in closed form on the basis
`x_n = e^n + e^{−n}`, `n ∈ S₁`, of `(V₃⁺)₂`:

* `oX_hP` — the zero mode of `x_n` (`|n|² = 4`, any `n`) on `(T⁺)₂`:
  `o(x_n)(h_v(−½) ⊗ t) = 2⁻³ h_{v − 2⟨v,n⟩n}(−½) ⊗ e_n t` (the `V₃⁺` analogue of
  `SigmaTop.actT_lV_hP`, from `leechYM_echg_X`).
* `latL_cw'` — `latL n (w_j) = Σ_l (δ_{jl} − n_jn_l/4) w_l`.
* `isEig_z` — `z = e_n e_m t₀` is a joint `Z_{0k}`-eigenvector with character `NS n m`
  (seed property of `t₀`); hence `ψ_l z = u_l ω^{|N|} z` (`psi_z`).
* `lhs_basis`, `rhs_basis` — both sides as `Σ_l (coefficient) • h_{w_l}(−½) ⊗ z`.
* `top_basis` — the identity on the basis, from `TopPairsArith.coef_identity`.
* `top_pairs0` — the identity on all of `(V₃⁺)₂` (bilinearity, `OmegaV3_le_span`).

So the sign is **`ε = +1`**: the relevant `Θ` is `Θ₀` itself (`Θ₀ = φ_B` with
`ψ_0 = B = ∏_{k≠0}(a + bZ_{0k})`).

## Status
`sorry`-free; unconditional (uses only the explicit data of `SigmaAssemble`).  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.TopPairs

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.Moonshine.SigmaTop
open VOA.Moonshine.SigmaAssemble VOA.TwistedHeisenberg VOA.Moonshine.InvForm
open VOA.Moonshine.LatticeTwisted VOA.Moonshine.Extraspecial
open Module (End)
open Submodule

/-! ## §1  The zero mode of `x_n = e^n + e^{−n}` on `(T⁺)₂` -/

theorem hP_eq_sum (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    hP v t = ∑ c, v c • hP (Pi.single c 1) t := by
  conv_lhs => rw [pi_eq_sum_single v]
  rw [hP_sum_left]
  simp only [hP_smul_left]

/-- **`o(x_n)` on the top level** (`|n|² = 4`):
`o(e^n + e^{−n})(h_v ⊗ t) = 2⁻³ h_{latL n v} ⊗ e_n t`. -/
theorem oX_hP {n : leech.carrier} (hn4 : leech.form n n = 4) (v : Fin (rank leech) → ℂ)
    (t : TLeechT) :
    mode (plusModule.YM (frameX0P n)) 1 (hP v t)
      = ((2 : ℂ) ^ (-(3 : ℤ))) • hP (latL n v) (eT leech leech_even leech_isUnit_det_gramMat n t) := by
  rw [hP_eq_sum v, map_sum]
  conv_rhs => rw [pi_eq_sum_single v, map_sum, hP_sum_left]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, map_smul, hP_smul_left, smul_comm]
  congr 1
  apply Subtype.ext
  rw [mode_plusModule, hP_coe, Submodule.coe_smul, hP_coe, hvec_single]
  change leechTwistedModule.YM (echg leech n + echg leech (-n)) (2 * 1) _ = _
  rw [show (2 : ℤ) * 1 = 2 by norm_num, map_add, Pi.add_apply, LinearMap.add_apply,
    leechYM_echg_neg_two, leechYM_echg_X n hn4]
  simp only [latL, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    hvec_sub, hvec_smul, hvec_single, hvec_chargeCoord]
  have hc : chT n (cc c) = chargeCoord leech n c := by simp [chT, cc]
  have hs : (∑ a, chargeCoord leech n a • Pi.single c (1 : ℂ) a) = chargeCoord leech n c := by
    simp [Pi.single_apply]
  rw [hc, hs, ← add_smul, ← smul_smul (2 : ℂ) (chargeCoord leech n c)]
  congr 1
  norm_num

/-- `latL n (w_b) = Σ_l (δ_{bl} − 2n_bn_l/8) w_l`. -/
theorem latL_cw' (γ : leech.carrier) (b : Fin 24) :
    latL γ (cw b) = ∑ l, ((if b = l then 1 else 0) - ((2 * lv γ b * lv γ l : ℤ) : ℂ) / 8) • cw l := by
  rw [latL_cw]
  simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-! ## §2  `e_n e_m t₀` is a joint `Z`-eigenvector -/

/-- `z = e_n e_m t₀`. -/
noncomputable def zz (n m : leech.carrier) : TLeechT := eL n (eL m t0)

theorem zz_mem {n m : leech.carrier} (hn : n ∉ lambda0) (hm : m ∉ lambda0) :
    zz n m ∈ leechFrameT s0 := by
  have h1 := eT_mem_leechFrameT m t0_mem
  rw [SigmaTop.frameChar_eq_one hm] at h1
  have h2 := eT_mem_leechFrameT n h1
  rwa [SigmaTop.frameChar_eq_one hn, s0_add_one_add_one] at h2

theorem ZZ_t0 {k : Fin 24} (hk : k ≠ 0) :
    (2 * kM 0 k) • eT leech leech_even leech_isUnit_det_gramMat (gM 0 k) t0 = t0 := by
  have h := (t0_seed 0 k (Ne.symm hk)).2
  rw [AM, LinearMap.smul_apply] at h
  rw [mul_smul]
  change (2 : ℂ) • (kM 0 k • eL (gM 0 k) t0) = t0
  rw [h, smul_smul]; norm_num

/-- **`e_n e_m t₀` is a joint eigenvector** of the `Z_{0k}` with character `NS n m`. -/
theorem isEig_z (n m : leech.carrier) : IsEigN (NS n m) (zz n m) := by
  intro k hk
  have hne : (2 * kM 0 k) ≠ 0 := mul_ne_zero two_ne_zero (kM_ne_zero (Ne.symm hk))
  have hg : eL (gM 0 k) t0 = (2 * kM 0 k)⁻¹ • t0 := by
    calc eL (gM 0 k) t0 = (2 * kM 0 k)⁻¹ • ((2 * kM 0 k) • eL (gM 0 k) t0) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (2 * kM 0 k)⁻¹ • t0 := congrArg _ (ZZ_t0 hk)
  rw [ZZ_apply, uN_NS, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zz]
  change (2 * kM 0 k) • eL (gM 0 k) (eL n (eL m t0)) = _
  rw [eL_comm_apply (gM 0 k) n, eL_comm_apply (gM 0 k) m, hg, map_smul, map_smul, map_smul,
    smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp
  exact div_self (kM_ne_zero (Ne.symm hk))

theorem psi_z {n m : leech.carrier} (hn : n ∉ lambda0) (hm : m ∉ lambda0) (l : Fin 24) :
    psiOf (Bop s0) l (zz n m) = (uN (NS n m) l * betaN (NS n m)) • zz n m :=
  psiOf_eigN (zz_mem hn hm) (zero_not_mem_NS n m) (isEig_z n m) l

/-! ## §3  Both sides on the basis -/

theorem Phi0_basis {m : leech.carrier} (hm : m ∈ halfFourChi 1) :
    Φ0 (frameX0P m) = cStar m • hP (cw (blk m)) (eL m t0) := by
  have hm0 : m ∉ lambda0 := by rw [mem_lambda0, (mem_halfFourChi hm).2]; exact one_ne_zero
  rw [Φ0_top _ (frameX0P_mem_OmegaV3 hm), phiV, phiV3_frameX0P _ hm, tauStar, cE_eq hm0,
    hP_smul_right]

theorem mode_smul_right (v : VPlus) (c : ℂ) (x : TP) :
    mode (plusModule.YM v) 1 (c • x) = c • mode (plusModule.YM v) 1 x := map_smul _ c x

theorem lhs_basis {n m : leech.carrier} (hn : n ∈ halfFourChi 1) (hm : m ∈ halfFourChi 1) :
    Θ0 (mode (plusModule.YM (frameX0P n)) 1 (Φ0 (frameX0P m)))
      = ∑ l, ((2 : ℂ) ^ (-(3 : ℤ)) * (cStar m * ((if blk m = l then 1 else 0)
          - ((2 * lv n (blk m) * lv n l : ℤ) : ℂ) / 8) * (uN (NS n m) l * betaN (NS n m))))
          • hP (cw l) (zz n m) := by
  obtain ⟨hn4, hn1⟩ := mem_halfFourChi hn
  obtain ⟨hm4, hm1⟩ := mem_halfFourChi hm
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, hn1]; exact one_ne_zero
  have hm0 : m ∉ lambda0 := by rw [mem_lambda0, hm1]; exact one_ne_zero
  rw [Phi0_basis hm, mode_smul_right, oX_hP hn4]
  have hmem : hP (latL n (cw (blk m))) (zz n m) ∈ OmegaT s0 :=
    ⟨hP_mem_frame _ (zz_mem hn0 hm0), hP_mem_weight _ _⟩
  change Θ0 (cStar m • (2 : ℂ) ^ (-(3 : ℤ)) • hP (latL n (cw (blk m))) (zz n m)) = _
  rw [map_smul, map_smul, Θ0_top _ hmem, phiB, latL_cw', hP_sum_left, map_sum, Finset.smul_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hP_smul_left, map_smul, phiTT_hP, psi_z hn0 hm0, hP_smul_right, smul_smul, smul_smul,
    smul_smul]
  congr 1
  ring

theorem rhs_basis {n m : leech.carrier} (hn : n ∈ halfFourChi 1) (hm : m ∈ halfFourChi 1) :
    mode (plusModule.YM (frameX0P m)) 1 (Φ0 (frameX0P n))
      = ∑ l, ((2 : ℂ) ^ (-(3 : ℤ)) * (cStar n * (-1 : ℂ) ^ (leech.form m n)
          * ((if blk n = l then 1 else 0) - ((2 * lv m (blk n) * lv m l : ℤ) : ℂ) / 8)))
          • hP (cw l) (zz n m) := by
  obtain ⟨hm4, -⟩ := mem_halfFourChi hm
  rw [Phi0_basis hn, mode_smul_right, oX_hP hm4]
  change cStar n • (2 : ℂ) ^ (-(3 : ℤ)) • hP (latL m (cw (blk n))) (eL m (eL n t0)) = _
  rw [eL_comm_apply, hP_smul_right, latL_cw', hP_sum_left, Finset.smul_sum, Finset.smul_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hP_smul_left, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

/-- **The top-pair identity on the basis** `x_n, x_m` (`n, m ∈ S₁`). -/
theorem top_basis {n m : leech.carrier} (hn : n ∈ halfFourChi 1) (hm : m ∈ halfFourChi 1) :
    Θ0 (mode (plusModule.YM (frameX0P n)) 1 (Φ0 (frameX0P m)))
      = mode (plusModule.YM (frameX0P m)) 1 (Φ0 (frameX0P n)) := by
  obtain ⟨hn4, hn1⟩ := mem_halfFourChi hn
  obtain ⟨hm4, hm1⟩ := mem_halfFourChi hm
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, hn1]; exact one_ne_zero
  have hm0 : m ∉ lambda0 := by rw [mem_lambda0, hm1]; exact one_ne_zero
  rw [lhs_basis hn hm, rhs_basis hn hm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coef_identity hn0 hn4 hm0 hm4 l]

/-! ## §4  Bilinear extension to `(V₃⁺)₂` -/

theorem mode_YM_add (v w : VPlus) (x : TP) :
    mode (plusModule.YM (v + w)) 1 x = mode (plusModule.YM v) 1 x + mode (plusModule.YM w) 1 x := by
  rw [mode, mode, mode, map_add]; rfl

theorem mode_YM_smul (c : ℂ) (v : VPlus) (x : TP) :
    mode (plusModule.YM (c • v)) 1 x = c • mode (plusModule.YM v) 1 x := by
  rw [mode, mode, map_smul]; rfl

theorem mode_YM_zero (x : TP) : mode (plusModule.YM (0 : VPlus)) 1 x = 0 := by
  simp [mode, map_zero]

/-- **The top-pair identity on `(V₃⁺)₂`** for the unnormalised data:
`Θ₀(o(v)Φ₀b) = o(b)Φ₀v` for all `v, b ∈ (V₃⁺)₂`. -/
theorem top_pairs0 {v b : VPlus} (hv : v ∈ OmegaV3) (hb : b ∈ OmegaV3) :
    Θ0 (mode (plusModule.YM v) 1 (Φ0 b)) = mode (plusModule.YM b) 1 (Φ0 v) := by
  have hv' := OmegaV3_le_span hv
  have hb' := OmegaV3_le_span hb
  clear hv hb
  induction hv' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, hn, rfl⟩ := ha
    induction hb' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      exact top_basis hn hm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy, mode_YM_add]
    | smul c x _ hx => rw [map_smul, map_smul, map_smul, hx, mode_YM_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [mode_YM_add, map_add, hx, hy, map_add, map_add]
  | smul c x _ hx => rw [mode_YM_smul, map_smul, hx, map_smul, map_smul]

end VOA.Moonshine.TopPairs
