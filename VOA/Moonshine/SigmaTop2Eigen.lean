/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Bridge

/-!
# (R-top): the off-diagonal constants `κ±`, the operators `W(a)`, and the seed reduction

For `j ≠ k` the zero mode of `σ(w_j(−1)w_k(−1)𝟙)` on `(T⁺)₂` is `A₊ ⊗ L₊ + A₋ ⊗ L₋` with
`A± = κ± e_{γ±}`, `γ± = 4e_j ± 4e_k` (`actT_sig_dV_offdiag`).  This file proves the structure of the
`A±` that the eigen-conditions of `topSigmaV3_of_eigen` / `topSigmaTT_of_eigen` need, symbolically
(the cocycles are those of `Module.Free.chooseBasis`; no sign is ever evaluated).

## Main results
* `latCob_add_self`, `latCob_mul_self` — the comparison coboundary on doubles.
* `tc_mul_self`, `tc_neg`, `tc_mul_tc` — the transport constants `tc`.
* `dQ_symm` — `θ`-invariance of `σ(w_j(−1)w_k(−1)𝟙)`: the coefficients of `e^{±γ}` agree; hence
  `kP_eq : κ₊ = ½ ε_N(α_j,α_k) tc(γ₊)`, `kM_eq`, and `eV_aP_sq : e(γ₊)² = ε_jε_k` (the `Θ`-scalar).
* `AP_mul_self`, `AM_mul_self` — `(κ± e_{γ±})² = ¼`.
* `lam_eq` — the prescribed eigenvalue is a character:
  `lam j k n = −½(−1)^{⟨γ₊,n⟩} = ½(−1)^{⟨γ₋,n⟩}`.
* `IsSeed t` (`A₊ t = −½ t`, `A₋ t = ½ t` for all `j ≠ k`), `SeedExists`, `seed_in_frame`.
* `eig_of_seed`, `eigenV3_of_seed`, `topSigmaV3_of_seed` — every `τ(n) = c_n e_n t` (`t` a seed)
  meets the `V₃⁺` eigen-conditions.
* `Wop a = tc(a) e_{ιa}` and `Wop_mul : W(a)W(b) = ε_N(a,b) W(a+b)` — the transported
  operators form a projective representation of `Λ₀` with the **`N`-cocycle**.
* `ZZ j k = 2κ₋ e_{γ₋}`, `ZZ_comp : Z_{jk} Z_{ij} = Z_{ik}`, `ZZ_mul_self`, `ZZ_swap`;
  `topSigmaTT_of_seed` — the block maps `ψ_m = Z_{0m} B` meet the `T_{s'}⁺` eigen-conditions.

## Status
`sorry`-free; `#print axioms` of `topSigmaV3_of_seed`, `topSigmaTT_of_seed`:
`[propext, Classical.choice, Quot.sound]`.  The seed itself is constructed in
`SigmaTop2Seed.lean`.  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.IntegralLattice
open VOA.LatGen HeisenbergN VOA.Moonshine.Triality
open Module (End)

/-! ## §1  The comparison coboundary on doubles -/

theorem latCob_add_self (K L : IntegralLattice) (ι : K.carrier →ₗ[ℤ] L.carrier) (a : K.carrier) :
    latCob K L ι (a + a) = 1 := by
  unfold latCob cobSign
  have h : symForm (latticeBasis K) (cocDiff K L ι) (a + a) (a + a)
      = 4 * symForm (latticeBasis K) (cocDiff K L ι) a a := by
    simp only [map_add, LinearMap.add_apply]; ring
  rw [h, zpow_mul, show (Complex.I ^ (4 : ℤ)) = 1 by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_pow_four], one_zpow]

theorem latCob_mul_self (K L : IntegralLattice) (hK : K.Even) (hL : L.Even)
    (ι : K.carrier →ₗ[ℤ] L.carrier) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) (a : K.carrier) :
    latCob K L ι a * latCob K L ι a = latticeCocycle K a a * latticeCocycle L (ι a) (ι a) := by
  have h := latticeCocycle_map_mul_latCob K L hK hL ι hι a a
  rw [latCob_add_self, mul_one] at h
  have hs := latticeCocycle_sq L (ι a) (ι a)
  calc latCob K L ι a * latCob K L ι a
      = (latticeCocycle L (ι a) (ι a) * latticeCocycle L (ι a) (ι a)) * (latCob K L ι a * latCob K L ι a) := by
        rw [hs, one_mul]
    _ = latticeCocycle L (ι a) (ι a) * (latticeCocycle L (ι a) (ι a) * (latCob K L ι a * latCob K L ι a)) := by ring
    _ = _ := by rw [h]; ring

/-! ## §2  The transport constants `tc` -/

/-- Shorthand for the operators `e_γ` on `T`. -/
noncomputable abbrev eL (γ : leech.carrier) : End ℂ TLeechT :=
  eT leech leech_even leech_isUnit_det_gramMat γ

/-- Shorthand for the golay cocycle. -/
noncomputable abbrev εN (x y : golayN.carrier) : ℂ := latticeCocycle golayN x y

/-- Shorthand for the Leech cocycle. -/
noncomputable abbrev εΛ (x y : leech.carrier) : ℂ := latticeCocycle leech x y

/-- The value of the chosen character `golayE`. -/
noncomputable abbrev eV (a : lam0.carrier) : ℂ := charVal lam0 golayE a

theorem tc_ne_zero (a : lam0.carrier) : tc a ≠ 0 := by
  unfold tc
  exact div_ne_zero (latCob_ne_zero _ _ _ _)
    (mul_ne_zero (charVal_ne_zero _ _ _) (latCob_ne_zero _ _ _ _))

theorem eV_neg (a : lam0.carrier) : eV (-a) = (eV a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (charVal_neg_mul lam0 golayE a)

theorem tc_neg (a : lam0.carrier) : tc (-a) = tc a * (eV a * eV a) := by
  unfold tc
  rw [latCob_neg, latCob_neg]
  change _ / (eV (-a) * _) = _ / (eV a * _) * _
  rw [eV_neg]
  have h1 := charVal_ne_zero lam0 golayE a
  have h2 := latCob_ne_zero lam0 golayN inclN a
  field_simp

theorem εN_sq (x y : golayN.carrier) : εN x y * εN x y = 1 := latticeCocycle_sq _ _ _
theorem εΛ_sq (x y : leech.carrier) : εΛ x y * εΛ x y = 1 := latticeCocycle_sq _ _ _
theorem εN_ne_zero (x y : golayN.carrier) : εN x y ≠ 0 := FrameT.latticeCocycle_ne_zero' _ _ _
theorem εΛ_ne_zero (x y : leech.carrier) : εΛ x y ≠ 0 := FrameT.latticeCocycle_ne_zero' _ _ _

/-- `tc(a)² e(a)² = ε_Λ(ιa,ιa) ε_N(ιa,ιa)`. -/
theorem tc_mul_self (a : lam0.carrier) :
    tc a * tc a * (eV a * eV a) = εΛ (inclΛ a) (inclΛ a) * εN (inclN a) (inclN a) := by
  have hΛ := latCob_mul_self lam0 leech lam0_even leech_even inclΛ inclΛ_form a
  have hN := latCob_mul_self lam0 golayN lam0_even golayN_even inclN inclN_form a
  have he := charVal_ne_zero lam0 golayE a
  have hc := latCob_ne_zero lam0 golayN inclN a
  have h0 := FrameT.latticeCocycle_ne_zero' lam0 a a
  have hsN := εN_sq (inclN a) (inclN a)
  unfold tc
  change latCob lam0 leech inclΛ a / (eV a * latCob lam0 golayN inclN a) *
      (latCob lam0 leech inclΛ a / (eV a * latCob lam0 golayN inclN a)) * (eV a * eV a) = _
  have hev : eV a ≠ 0 := he
  rw [div_mul_div_comm, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero (mul_ne_zero hev hc) (mul_ne_zero hev hc)), hΛ]
  calc latticeCocycle lam0 a a * latticeCocycle leech (inclΛ a) (inclΛ a) * (eV a * eV a)
      = latticeCocycle lam0 a a * latticeCocycle leech (inclΛ a) (inclΛ a) * (eV a * eV a)
          * (εN (inclN a) (inclN a) * εN (inclN a) (inclN a)) := by rw [hsN, mul_one]
    _ = _ := by
        change _ = εΛ (inclΛ a) (inclΛ a) * εN (inclN a) (inclN a) *
          (eV a * latCob lam0 golayN inclN a * (eV a * latCob lam0 golayN inclN a))
        have : latCob lam0 golayN inclN a * latCob lam0 golayN inclN a
            = latticeCocycle lam0 a a * εN (inclN a) (inclN a) := hN
        linear_combination (-(eV a * eV a * latticeCocycle leech (inclΛ a) (inclΛ a) * εN (inclN a) (inclN a))) * this

/-! ## §3  `θ`-invariance of `σ(w_j(−1)w_k(−1)𝟙)` and the constants `κ±` -/

theorem ne_of_lv {x y : leech.carrier} (i : Fin 24) (h : lv x i ≠ lv y i) : x ≠ y :=
  fun e => h (e ▸ rfl)

theorem lv_gP_j {j k : Fin 24} (hjk : j ≠ k) : lv (gP j k) j = 4 := by
  rw [lv_gP_apply]; simp [hjk]
theorem lv_gP_k {j k : Fin 24} (hjk : j ≠ k) : lv (gP j k) k = 4 := by
  rw [lv_gP_apply]; simp [Ne.symm hjk]
theorem lv_gM_j {j k : Fin 24} (hjk : j ≠ k) : lv (gM j k) j = 4 := by
  rw [lv_gM_apply]; simp [hjk]
theorem lv_gM_k {j k : Fin 24} (hjk : j ≠ k) : lv (gM j k) k = -4 := by
  rw [lv_gM_apply]; simp [Ne.symm hjk]

theorem vacuumN_ne_zero' : vacuumN (rank leech) ≠ 0 := one_ne_zero

theorem inclΛ_aQ (j k : Fin 24) :
    (fun i => inclΛ (aQ j k i)) = ![gP j k, gM j k, -gM j k, -gP j k] := by
  funext i; fin_cases i <;> simp [aQ, gP, gM]

/-- The four `golaySigma`-coefficients times transport constants. -/
noncomputable def dQ (j k : Fin 24) (i : Fin 4) : ℂ := 4 * cQ j k i * tc (aQ j k i)

open Classical in
/-- **`θ`-invariance**: the coefficients of `e^{±γ₊}` (and of `e^{±γ₋}`) in
`σ(w_j(−1)w_k(−1)𝟙)` agree. -/
theorem dQ_symm {j k : Fin 24} (hjk : j ≠ k) : dQ j k 0 = dQ j k 3 ∧ dQ j k 1 = dQ j k 2 := by
  set v : LatModuleGen leech := (((sig (dV (fw j) (fw k)) : V0Sub.carrier) : VPlus) : LatModuleGen leech)
  have hθ : thetaLat leech v = v := (mem_leechVOAPlus_iff v).mp (((sig (dV (fw j) (fw k)) : V0Sub.carrier) : VPlus)).2
  have hv : v = ∑ i : Fin 4, dQ j k i • latChargeGen leech (inclΛ (aQ j k i)) := sig_dV_offdiag_coe hjk
  rw [hv, map_sum] at hθ
  simp only [map_smul, thetaLat_latChargeGen] at hθ
  have e0 : inclΛ (aQ j k 0) = gP j k := rfl
  have e1 : inclΛ (aQ j k 1) = gM j k := rfl
  have e2 : inclΛ (aQ j k 2) = -gM j k := by simp [aQ, gM]
  have e3 : inclΛ (aQ j k 3) = -gP j k := by simp [aQ, gP]
  rw [Fin.sum_univ_four, Fin.sum_univ_four, e0, e1, e2, e3, neg_neg, neg_neg] at hθ
  have n1 : gP j k ≠ gM j k := ne_of_lv k (by rw [lv_gP_k hjk, lv_gM_k hjk]; norm_num)
  have n2 : gP j k ≠ -gM j k := ne_of_lv j (by rw [lv_neg, Pi.neg_apply, lv_gP_j hjk, lv_gM_j hjk]; norm_num)
  have n3 : gP j k ≠ -gP j k := ne_of_lv j (by rw [lv_neg, Pi.neg_apply, lv_gP_j hjk]; norm_num)
  have n4 : gM j k ≠ -gM j k := ne_of_lv j (by rw [lv_neg, Pi.neg_apply, lv_gM_j hjk]; norm_num)
  have n5 : gM j k ≠ -gP j k := ne_of_lv j (by rw [lv_neg, Pi.neg_apply, lv_gP_j hjk, lv_gM_j hjk]; norm_num)
  have hinj : ∀ a b : ℂ, a • vacuumN (rank leech) = b • vacuumN (rank leech) → a = b :=
    fun a b h => smul_left_injective ℂ vacuumN_ne_zero' h
  constructor
  · have h := congrArg (coordEα leech (gP j k)) hθ
    simp only [map_add, map_smul, coordEα_latChargeGen, if_neg n1, if_neg n2, if_neg n3,
      smul_zero, add_zero, zero_add] at h
    exact (hinj _ _ h).symm
  · have h := congrArg (coordEα leech (gM j k)) hθ
    simp only [map_add, map_smul, coordEα_latChargeGen, if_neg n1.symm, if_neg n4, if_neg n5,
      smul_zero, add_zero, zero_add] at h
    exact (hinj _ _ h).symm

theorem kP_eq {j k : Fin 24} (hjk : j ≠ k) : kP j k = (1 / 2 : ℂ) * cQ j k 0 * tc (aP j k) := by
  have h := (dQ_symm hjk).1
  unfold dQ at h
  rw [kP, ← h, aQ_0]
  norm_num; ring

theorem kM_eq {j k : Fin 24} (hjk : j ≠ k) : kM j k = (1 / 2 : ℂ) * cQ j k 1 * tc (aM j k) := by
  have h := (dQ_symm hjk).2
  unfold dQ at h
  rw [kM, ← h, aQ_1]
  norm_num; ring

/-! ## §4  `(κ± e_{γ±})² = ¼` -/

theorem golayEps_mul_self (j : Fin 24) : golayEps j * golayEps j = 1 := by
  rw [← pow_two]; exact golayEps_sq j

theorem golayEps_ne_zero (j : Fin 24) : golayEps j ≠ 0 := by
  intro h; have := golayEps_mul_self j; rw [h, zero_mul] at this; exact zero_ne_one this

theorem εN_root_self (j : Fin 24) : εN (golayRoot j) (golayRoot j) = golayEps j := by
  rw [golayEps, latticeCocycle_neg_right]

theorem εN_root_comm {j k : Fin 24} (hjk : j ≠ k) :
    εN (golayRoot j) (golayRoot k) * εN (golayRoot k) (golayRoot j) = 1 := by
  rw [latticeCocycle_comm golayN golayN_even, golayRoot_orth hjk, zpow_zero]

theorem εN_root_symm {j k : Fin 24} (hjk : j ≠ k) :
    εN (golayRoot k) (golayRoot j) = εN (golayRoot j) (golayRoot k) := by
  have h := εN_root_comm hjk
  have hs := εN_sq (golayRoot j) (golayRoot k)
  calc εN (golayRoot k) (golayRoot j)
      = (εN (golayRoot j) (golayRoot k) * εN (golayRoot j) (golayRoot k)) * εN (golayRoot k) (golayRoot j) := by
        rw [hs, one_mul]
    _ = εN (golayRoot j) (golayRoot k) * (εN (golayRoot j) (golayRoot k) * εN (golayRoot k) (golayRoot j)) := by ring
    _ = _ := by rw [h, mul_one]

theorem εN_aP_self {j k : Fin 24} (hjk : j ≠ k) :
    εN (inclN (aP j k)) (inclN (aP j k)) = golayEps j * golayEps k := by
  rw [inclN_aP]
  simp only [εN, latticeCocycle_add_left, latticeCocycle_add_right]
  have h := εN_root_comm hjk
  simp only [εN] at h
  rw [← εN_root_self j, ← εN_root_self k]
  simp only [εN]
  linear_combination (latticeCocycle golayN (golayRoot j) (golayRoot j) *
    latticeCocycle golayN (golayRoot k) (golayRoot k)) * h

theorem εN_aM_self {j k : Fin 24} (hjk : j ≠ k) :
    εN (inclN (aM j k)) (inclN (aM j k)) = golayEps j * golayEps k := by
  rw [inclN_aM]
  simp only [εN, latticeCocycle_add_left, latticeCocycle_add_right, latticeCocycle_neg_left,
    latticeCocycle_neg_right]
  have h := εN_root_comm hjk
  simp only [εN] at h
  rw [← εN_root_self j, ← εN_root_self k]
  simp only [εN]
  linear_combination (latticeCocycle golayN (golayRoot j) (golayRoot j) *
    latticeCocycle golayN (golayRoot k) (golayRoot k)) * h

theorem cQ_0_eq (j k : Fin 24) : cQ j k 0 = εN (golayRoot j) (golayRoot k) := rfl
theorem cQ_1_eq (j k : Fin 24) : cQ j k 1 = golayEps k * εN (golayRoot j) (golayRoot k) := by
  rw [cQ_1, latticeCocycle_neg_right]
theorem cQ_2_eq (j k : Fin 24) : cQ j k 2 = golayEps j * εN (golayRoot j) (golayRoot k) := by
  rw [cQ_2, latticeCocycle_neg_left]
theorem cQ_3_eq (j k : Fin 24) :
    cQ j k 3 = golayEps j * golayEps k * εN (golayRoot j) (golayRoot k) := by
  rw [cQ_3, latticeCocycle_neg_left, latticeCocycle_neg_right]

/-- `e(γ₊)² = ε_j ε_k` (the `Θ`-scalar of `e^{α_j+α_k}`), from `θ`-invariance. -/
theorem eV_aP_sq {j k : Fin 24} (hjk : j ≠ k) : eV (aP j k) * eV (aP j k) = golayEps j * golayEps k := by
  have h := (dQ_symm hjk).1
  unfold dQ at h
  rw [aQ_3, aQ_0, tc_neg, cQ_0_eq, cQ_3_eq] at h
  have hc : 4 * εN (golayRoot j) (golayRoot k) * tc (aP j k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (εN_ne_zero _ _)) (tc_ne_zero _)
  have h1 : golayEps j * golayEps k * (eV (aP j k) * eV (aP j k)) = 1 := by
    have h' : (4 * εN (golayRoot j) (golayRoot k) * tc (aP j k)) * 1
        = (4 * εN (golayRoot j) (golayRoot k) * tc (aP j k)) *
          (golayEps j * golayEps k * (eV (aP j k) * eV (aP j k))) := by
      rw [mul_one]; linear_combination h
    exact (mul_left_cancel₀ hc h').symm
  have ej := golayEps_mul_self j
  have ek := golayEps_mul_self k
  linear_combination (golayEps j * golayEps k) * h1 - (eV (aP j k) * eV (aP j k)) * ej
    - (eV (aP j k) * eV (aP j k) * golayEps j * golayEps j) * ek

theorem eV_aM_sq {j k : Fin 24} (hjk : j ≠ k) : eV (aM j k) * eV (aM j k) = golayEps j * golayEps k := by
  have h := (dQ_symm hjk).2
  unfold dQ at h
  rw [aQ_2, aQ_1, tc_neg, cQ_1_eq, cQ_2_eq] at h
  have hc : 4 * εN (golayRoot j) (golayRoot k) * tc (aM j k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) (εN_ne_zero _ _)) (tc_ne_zero _)
  have h1 : golayEps k = golayEps j * (eV (aM j k) * eV (aM j k)) := by
    have h' : (4 * εN (golayRoot j) (golayRoot k) * tc (aM j k)) * golayEps k
        = (4 * εN (golayRoot j) (golayRoot k) * tc (aM j k)) *
          (golayEps j * (eV (aM j k) * eV (aM j k))) := by
      linear_combination h
    exact mul_left_cancel₀ hc h'
  have ej := golayEps_mul_self j
  linear_combination (-golayEps j) * h1 - (eV (aM j k) * eV (aM j k)) * ej

theorem tc_aP_sq {j k : Fin 24} (hjk : j ≠ k) : tc (aP j k) * tc (aP j k) = εΛ (gP j k) (gP j k) := by
  have h := tc_mul_self (aP j k)
  rw [eV_aP_sq hjk, εN_aP_self hjk] at h
  have hne : golayEps j * golayEps k ≠ 0 := mul_ne_zero (golayEps_ne_zero j) (golayEps_ne_zero k)
  exact mul_right_cancel₀ hne (by rw [h]; rfl)

theorem tc_aM_sq {j k : Fin 24} (hjk : j ≠ k) : tc (aM j k) * tc (aM j k) = εΛ (gM j k) (gM j k) := by
  have h := tc_mul_self (aM j k)
  rw [eV_aM_sq hjk, εN_aM_self hjk] at h
  have hne : golayEps j * golayEps k ≠ 0 := mul_ne_zero (golayEps_ne_zero j) (golayEps_ne_zero k)
  exact mul_right_cancel₀ hne (by rw [h]; rfl)

/-- The operator `A₊ = κ₊ e_{γ₊}` on `T`. -/
noncomputable def AP (j k : Fin 24) : End ℂ TLeechT := kP j k • eL (gP j k)

/-- The operator `A₋ = κ₋ e_{γ₋}` on `T`. -/
noncomputable def AM (j k : Fin 24) : End ℂ TLeechT := kM j k • eL (gM j k)

theorem eL_mul_self (γ : leech.carrier) : eL γ * eL γ = εΛ γ γ • (1 : End ℂ TLeechT) :=
  eT_mul_self' leech leech_even leech_isUnit_det_gramMat γ

theorem kP_sq {j k : Fin 24} (hjk : j ≠ k) : kP j k * kP j k * εΛ (gP j k) (gP j k) = 1 / 4 := by
  rw [kP_eq hjk]
  have h1 := tc_aP_sq hjk
  have h2 := εN_sq (golayRoot j) (golayRoot k)
  have h3 := εΛ_sq (gP j k) (gP j k)
  rw [cQ_0_eq]
  linear_combination (1 / 4 : ℂ) * (tc (aP j k) * tc (aP j k) * εΛ (gP j k) (gP j k)) * h2
    + (1 / 4 : ℂ) * εΛ (gP j k) (gP j k) * h1 + (1 / 4 : ℂ) * h3

theorem kM_sq {j k : Fin 24} (hjk : j ≠ k) : kM j k * kM j k * εΛ (gM j k) (gM j k) = 1 / 4 := by
  rw [kM_eq hjk]
  have h1 := tc_aM_sq hjk
  have h2 := εN_sq (golayRoot j) (golayRoot k)
  have h3 := εΛ_sq (gM j k) (gM j k)
  have h4 := golayEps_mul_self k
  rw [cQ_1_eq]
  linear_combination (1 / 4 : ℂ) * (tc (aM j k) * tc (aM j k) * εΛ (gM j k) (gM j k)) *
      (golayEps k * golayEps k) * h2
    + (1 / 4 : ℂ) * (tc (aM j k) * tc (aM j k) * εΛ (gM j k) (gM j k)) * h4
    + (1 / 4 : ℂ) * εΛ (gM j k) (gM j k) * h1 + (1 / 4 : ℂ) * h3

/-- **`(κ₊ e_{γ₊})² = ¼`.** -/
theorem AP_mul_self {j k : Fin 24} (hjk : j ≠ k) : AP j k * AP j k = (1 / 4 : ℂ) • 1 := by
  rw [AP, smul_mul_smul_comm, eL_mul_self, smul_smul, kP_sq hjk]

/-- **`(κ₋ e_{γ₋})² = ¼`.** -/
theorem AM_mul_self {j k : Fin 24} (hjk : j ≠ k) : AM j k * AM j k = (1 / 4 : ℂ) • 1 := by
  rw [AM, smul_mul_smul_comm, eL_mul_self, smul_smul, kM_sq hjk]

theorem kP_ne_zero {j k : Fin 24} (hjk : j ≠ k) : kP j k ≠ 0 := by
  rw [kP_eq hjk]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (εN_ne_zero _ _)) (tc_ne_zero _)

theorem kM_ne_zero {j k : Fin 24} (hjk : j ≠ k) : kM j k ≠ 0 := by
  rw [kM_eq hjk, cQ_1_eq]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero (golayEps_ne_zero _) (εN_ne_zero _ _)))
    (tc_ne_zero _)

/-! ## §5  The prescribed eigenvalues as characters: `lam = −½(−1)^{⟨γ₊,n⟩} = ½(−1)^{⟨γ₋,n⟩}` -/

theorem form_gP_left (j k : Fin 24) (n : leech.carrier) :
    leech.form (gP j k) n = (4 * (lv n j + lv n k)) / 8 := by
  rw [leech_form_lv, lv_gP, smul_dotProduct, add_dotProduct, single_dotProduct, single_dotProduct,
    smul_eq_mul, one_mul, one_mul]

theorem form_gM_left (j k : Fin 24) (n : leech.carrier) :
    leech.form (gM j k) n = (4 * (lv n j - lv n k)) / 8 := by
  rw [leech_form_lv, lv_gM, smul_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct,
    smul_eq_mul, one_mul, one_mul]

theorem int_sq_one {x : ℤ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

theorem int_sq_nine {x : ℤ} (h : x ^ 2 = 9) : x = 3 ∨ x = -3 := by
  have : (x - 3) * (x + 3) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

/-- **The eigenvalue pattern is a character**: `lam j k n = −½ (−1)^{⟨γ₊,n⟩}` and
`= ½ (−1)^{⟨γ₋,n⟩}` on `S₁`. -/
theorem lam_eq {j k : Fin 24} (hjk : j ≠ k) {n : leech.carrier} (hn : n ∈ halfFourChi 1) :
    lam j k n = -(1 / 2 : ℂ) * (-1 : ℂ) ^ (leech.form (gP j k) n) ∧
      lam j k n = (1 / 2 : ℂ) * (-1 : ℂ) ^ (leech.form (gM j k) n) := by
  obtain ⟨h4, h1⟩ := mem_halfFourChi hn
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, h1]; exact one_ne_zero
  have hsq := lv_sq hn0 h4
  rw [form_gP_left, form_gM_left]
  unfold lam
  by_cases hbj : blk n = j
  · have hk : k ≠ blk n := hbj ▸ Ne.symm hjk
    have hj9 := hsq j; rw [if_pos hbj.symm] at hj9
    have hk1 := hsq k; rw [if_neg hk] at hk1
    rw [if_pos (Or.inl hbj)]
    rcases int_sq_nine hj9 with ha | ha <;> rcases int_sq_one hk1 with hb | hb <;>
      rw [ha, hb] <;> norm_num
  · by_cases hbk : blk n = k
    · have hj : j ≠ blk n := hbk ▸ hjk
      have hj1 := hsq j; rw [if_neg hj] at hj1
      have hk9 := hsq k; rw [if_pos hbk.symm] at hk9
      rw [if_pos (Or.inr hbk)]
      rcases int_sq_one hj1 with ha | ha <;> rcases int_sq_nine hk9 with hb | hb <;>
        rw [ha, hb] <;> norm_num
    · have hj1 := hsq j; rw [if_neg (Ne.symm hbj)] at hj1
      have hk1 := hsq k; rw [if_neg (Ne.symm hbk)] at hk1
      rw [if_neg (by tauto)]
      rcases int_sq_one hj1 with ha | ha <;> rcases int_sq_one hk1 with hb | hb <;>
        rw [ha, hb] <;> norm_num

/-! ## §6  The seed, and the eigen-conditions on `V₃⁺` -/

/-- **The seed conditions**: `κ₊ e_{γ₊} t = −½ t` and `κ₋ e_{γ₋} t = ½ t` for all `j ≠ k`. -/
def IsSeed (t : TLeechT) : Prop :=
  ∀ j k : Fin 24, j ≠ k → AP j k t = -(1 / 2 : ℂ) • t ∧ AM j k t = (1 / 2 : ℂ) • t

/-- **The single datum behind all eigen-conditions**: a nonzero seed vector exists. -/
def SeedExists : Prop := ∃ t : TLeechT, t ≠ 0 ∧ IsSeed t

theorem frameJL_comm_eL {γ : leech.carrier} (hγ : γ ∈ lambda0) : frameJL * eL γ = eL γ * frameJL := by
  have h := FrameT.frameJ_comm_sign leech leech_even leech_isUnit_det_gramMat frameW γ
  rw [frameW_sign, chiSign_of_eq_zero _ _ ((mem_lambda0 γ).mp hγ), one_smul] at h
  exact h

theorem projT_eL {γ : leech.carrier} (hγ : γ ∈ lambda0) (s : ZMod 2) (t : TLeechT) :
    projT s (eL γ t) = eL γ (projT s t) := by
  rw [projT_apply, projT_apply, map_smul, map_add, map_smul]
  congr 3
  exact congrArg (fun f : End ℂ TLeechT => f t) (frameJL_comm_eL hγ)

theorem gM_mem' (j k : Fin 24) : gM j k ∈ lambda0 := gM_mem j k
theorem gP_mem' (j k : Fin 24) : gP j k ∈ lambda0 := gP_mem j k

theorem isSeed_projT {t : TLeechT} (ht : IsSeed t) (s : ZMod 2) : IsSeed (projT s t) := by
  intro j k hjk
  obtain ⟨h1, h2⟩ := ht j k hjk
  constructor
  · have h := congrArg (projT s) h1
    simp only [AP, LinearMap.smul_apply, map_smul, projT_eL (gP_mem j k)] at h
    exact h
  · have h := congrArg (projT s) h2
    simp only [AM, LinearMap.smul_apply, map_smul, projT_eL (gM_mem j k)] at h
    exact h

theorem projT_add_projT (t : TLeechT) : projT 0 t + projT 1 t = t := by
  rw [projT_apply, projT_apply, Extraspecial.sgn_zero, Extraspecial.sgn_one]
  module

/-- A seed may be taken inside a frame sector. -/
theorem seed_in_frame (h : SeedExists) :
    ∃ s : ZMod 2, ∃ t : TLeechT, t ∈ leechFrameT s ∧ t ≠ 0 ∧ IsSeed t := by
  obtain ⟨t, ht0, ht⟩ := h
  by_cases h0 : projT 0 t = 0
  · refine ⟨1, projT 1 t, projT_mem 1 t, fun h1 => ht0 ?_, isSeed_projT ht 1⟩
    rw [← projT_add_projT t, h0, h1, add_zero]
  · exact ⟨0, projT 0 t, projT_mem 0 t, h0, isSeed_projT ht 0⟩

theorem eL_injective (γ : leech.carrier) : Function.Injective (eL γ) := by
  intro x y h
  have h2 := congrArg (eL γ) h
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, eL_mul_self] at h2
  simp only [LinearMap.smul_apply, Module.End.one_apply] at h2
  exact smul_right_injective _ (εΛ_ne_zero γ γ) h2

/-- **The eigen-conditions from a seed**: `τ(n) = c_n e_n t` satisfies them for every `c`. -/
theorem eig_of_seed {t : TLeechT} (ht : IsSeed t) (c : leech.carrier → ℂ) {j k : Fin 24}
    (hjk : j ≠ k) {n : leech.carrier} (hn : n ∈ halfFourChi 1) :
    kP j k • eL (gP j k) (c n • eL n t) = lam j k n • (c n • eL n t) ∧
      kM j k • eL (gM j k) (c n • eL n t) = lam j k n • (c n • eL n t) := by
  obtain ⟨h1, h2⟩ := ht j k hjk
  obtain ⟨l1, l2⟩ := lam_eq hjk hn
  have cP := eT_comm_sign' leech leech_even leech_isUnit_det_gramMat (gP j k) n
  have cM := eT_comm_sign' leech leech_even leech_isUnit_det_gramMat (gM j k) n
  constructor
  · have e : eL (gP j k) (eL n t) = (-1 : ℂ) ^ leech.form (gP j k) n • eL n (eL (gP j k) t) :=
      congrArg (fun f : End ℂ TLeechT => f t) cP
    have h1' : eL (gP j k) t = (-(1 / 2 : ℂ) * (kP j k)⁻¹) • t := by
      rw [mul_comm, ← smul_smul, ← h1, AP, LinearMap.smul_apply, smul_smul,
        inv_mul_cancel₀ (kP_ne_zero hjk), one_smul]
    rw [map_smul, e, h1', map_smul]
    simp only [smul_smul]
    rw [l1]
    congr 1
    field_simp [kP_ne_zero hjk]
  · have e : eL (gM j k) (eL n t) = (-1 : ℂ) ^ leech.form (gM j k) n • eL n (eL (gM j k) t) :=
      congrArg (fun f : End ℂ TLeechT => f t) cM
    have h2' : eL (gM j k) t = ((1 / 2 : ℂ) * (kM j k)⁻¹) • t := by
      rw [mul_comm, ← smul_smul, ← h2, AM, LinearMap.smul_apply, smul_smul,
        inv_mul_cancel₀ (kM_ne_zero hjk), one_smul]
    rw [map_smul, e, h2', map_smul]
    simp only [smul_smul]
    rw [l2]
    congr 1
    field_simp [kM_ne_zero hjk]

/-- The block normalisation `μ_j`, making `μ_j e_{n_j} t` independent of `j`. -/
noncomputable def mu (j : Fin 24) : ℂ :=
  if j = 0 then 1 else εΛ (mvec 0) (gM 0 j) * (2 * kM 0 j)

theorem mvec_add_gM (j : Fin 24) : mvec 0 + gM 0 j = mvec j := by
  apply Subtype.ext
  change lv (mvec 0) + lv (gM 0 j) = lv (mvec j)
  funext i
  rw [Pi.add_apply, lv_mvec, lv_mvec, lv_gM_apply]
  by_cases h0 : i = 0 <;> by_cases hj : i = j <;> simp [h0, hj] <;> subst_vars <;> simp_all

theorem eL_nvec (j : Fin 24) : eL (nvec j) = eL (mvec j) := by
  unfold nvec; split_ifs
  · rfl
  · exact eT_neg leech leech_even leech_isUnit_det_gramMat _

theorem mu_nvec {t : TLeechT} (ht : IsSeed t) (j : Fin 24) :
    mu j • eL (nvec j) t = eL (mvec 0) t := by
  rw [eL_nvec]
  unfold mu
  split_ifs with hj
  · subst hj; rw [one_smul]
  · have h2 := (ht 0 j (Ne.symm hj)).2
    have hk := kM_ne_zero (Ne.symm hj)
    have h2' : eL (gM 0 j) t = (2 * kM 0 j)⁻¹ • t := by
      have : kM 0 j • eL (gM 0 j) t = (1 / 2 : ℂ) • t := h2
      have h3 := congrArg (fun x => (kM 0 j)⁻¹ • x) this
      simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at h3
      rw [h3]; congr 1; field_simp
    have hm := congrArg (fun f : End ℂ TLeechT => f t) (eT_mul leech leech_even leech_isUnit_det_gramMat (mvec 0) (gM 0 j))
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at hm
    change eL (mvec 0) (eL (gM 0 j) t) = εΛ (mvec 0) (gM 0 j) • eL (mvec 0 + gM 0 j) t at hm
    rw [h2', map_smul, mvec_add_gM] at hm
    have hε := εΛ_ne_zero (mvec 0) (gM 0 j)
    rw [mul_comm, ← smul_smul, ← hm, smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero hk),
      one_smul]

/-- The block-monomial assignment built from a seed: `τ(n) = c_n e_n t`. -/
noncomputable def tauOf (c : leech.carrier → ℂ) (t : TLeechT) (n : leech.carrier) : TLeechT :=
  c n • eL n t

/-- **The eigen-conditions of `topSigmaV3_of_eigen` hold for every seeded `τ`.** -/
theorem eigenV3_of_seed {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) (c : leech.carrier → ℂ) (hc : ∀ j, c (nvec j) = mu j) :
    (∀ n ∈ halfFourChi 1, tauOf c t n ∈ leechFrameT (s + 1)) ∧
      eL (mvec 0) t ∈ leechFrameT (s + 1) ∧ eL (mvec 0) t ≠ 0 ∧
      (∀ j, tauOf c t (nvec j) = eL (mvec 0) t) ∧
      (∀ j k : Fin 24, j ≠ k → ∀ n ∈ halfFourChi 1,
        kP j k • eL (gP j k) (tauOf c t n) = lam j k n • tauOf c t n ∧
        kM j k • eL (gM j k) (tauOf c t n) = lam j k n • tauOf c t n) := by
  have hfr : ∀ n : leech.carrier, frameChar n = 1 → eL n t ∈ leechFrameT (s + 1) := by
    intro n hn
    have := eT_mem_leechFrameT n hts
    rwa [hn] at this
  have hm1 : frameChar (mvec 0) = 1 := by
    have h := mvec_not_mem 0
    rw [mem_lambda0] at h
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (frameChar (mvec 0)) with h' | h'
    · exact absurd h' h
    · exact h'
  refine ⟨fun n hn => Submodule.smul_mem _ _ (hfr n (mem_halfFourChi hn).2), hfr _ hm1,
    fun h => ht0 (eL_injective _ (by rw [h, map_zero])), fun j => ?_,
    fun j k hjk n hn => eig_of_seed ht c hjk hn⟩
  rw [tauOf, hc, mu_nvec ht]

/-- **`TopSigmaV3` for a seeded `τ`, conditional only on the lattice letters.** -/
theorem topSigmaV3_of_seed {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) (c : leech.carrier → ℂ) (hc : ∀ j, c (nvec j) = mu j)
    (hlat : ∀ γ ∈ halfFourChi 0, ZM (phiV3 (tauOf c t)) OmegaV3 (lV' γ)) :
    TopSigmaV3 (s + 1) (phiV3 (tauOf c t)) := by
  obtain ⟨hτ, ht₀, h0, hblk, heig⟩ := eigenV3_of_seed hts ht0 ht c hc
  exact topSigmaV3_of_eigen hτ ht₀ h0 hblk zhuGenerated_G2 heig hlat

/-! ## §7  The transported operators `W(a) = tc(a) e_{ιa}` -/

/-- `W(a) = tc(a) e_{ι_Λ a}` for `a ∈ Λ₀`: the image on `T` of the `N`-normalised charge `a`. -/
noncomputable def Wop (a : lam0.carrier) : End ℂ TLeechT := tc a • eL (inclΛ a)

theorem tc_mul_tc (a b : lam0.carrier) :
    tc a * tc b * εΛ (inclΛ a) (inclΛ b) = εN (inclN a) (inclN b) * tc (a + b) := by
  have hΛ := latticeCocycle_map_mul_latCob lam0 leech lam0_even leech_even inclΛ inclΛ_form a b
  have hN := latticeCocycle_map_mul_latCob lam0 golayN lam0_even golayN_even inclN inclN_form a b
  have hab := charVal_add lam0 golayE a b
  have h1 := charVal_ne_zero lam0 golayE a
  have h2 := charVal_ne_zero lam0 golayE b
  have h3 := latCob_ne_zero lam0 golayN inclN a
  have h4 := latCob_ne_zero lam0 golayN inclN b
  have h5 := latCob_ne_zero lam0 golayN inclN (a + b)
  have h6 := charVal_ne_zero lam0 golayE (a + b)
  unfold tc
  rw [hab, div_mul_div_comm, div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff
    (mul_ne_zero (mul_ne_zero h1 h3) (mul_ne_zero h2 h4)) (mul_ne_zero (mul_ne_zero h1 h2) h5)]
  linear_combination (charVal lam0 golayE a * charVal lam0 golayE b * latCob lam0 golayN inclN (a + b)) * hΛ
    - (latCob lam0 leech inclΛ (a + b) * charVal lam0 golayE a * charVal lam0 golayE b) * hN

/-- **`W` is a projective representation with the `N`-cocycle**: `W(a)W(b) = ε_N(a,b) W(a+b)`. -/
theorem Wop_mul (a b : lam0.carrier) : Wop a * Wop b = εN (inclN a) (inclN b) • Wop (a + b) := by
  rw [Wop, Wop, Wop, smul_mul_smul_comm, eT_mul, map_add, smul_smul, smul_smul]
  congr 1
  rw [← tc_mul_tc]

theorem Wop_neg (a : lam0.carrier) : Wop (-a) = (eV a * eV a) • Wop a := by
  rw [Wop, Wop, tc_neg, map_neg,
    show eL (-inclΛ a) = eL (inclΛ a) from eT_neg leech leech_even leech_isUnit_det_gramMat _,
    smul_smul]
  congr 1; ring

theorem AM_eq_Wop {j k : Fin 24} (hjk : j ≠ k) :
    AM j k = ((1 / 2 : ℂ) * (golayEps k * εN (golayRoot j) (golayRoot k))) • Wop (aM j k) := by
  rw [AM, kM_eq hjk, cQ_1_eq, Wop, smul_smul]; rfl

theorem AP_eq_Wop {j k : Fin 24} (hjk : j ≠ k) :
    AP j k = ((1 / 2 : ℂ) * εN (golayRoot j) (golayRoot k)) • Wop (aP j k) := by
  rw [AP, kP_eq hjk, cQ_0_eq, Wop, smul_smul]; rfl

/-! ## §8  The block links `Z_{jk} = 2κ₋ e_{γ₋}` and the eigen-conditions on `T_{s'}⁺` -/

/-- `Z_{jk} = 2 κ₋ e_{γ₋}` (`= V_j V_k⁻¹` in the formal `sl₂`-doublet calculus). -/
noncomputable def ZZ (j k : Fin 24) : End ℂ TLeechT := (2 : ℂ) • AM j k

theorem inclN_injective : Function.Injective inclN := Leech.inclG_injective

theorem aM_add {i j k : Fin 24} : aM j k + aM i j = aM i k := by
  apply inclN_injective
  rw [map_add, inclN_aM, inclN_aM, inclN_aM]; abel

theorem aM_swap (j k : Fin 24) : aM k j = -aM j k := by
  apply inclN_injective
  rw [map_neg, inclN_aM, inclN_aM]; abel

theorem ZZ_eq_Wop {j k : Fin 24} (hjk : j ≠ k) :
    ZZ j k = (golayEps k * εN (golayRoot j) (golayRoot k)) • Wop (aM j k) := by
  rw [ZZ, AM_eq_Wop hjk, smul_smul]; congr 1; ring

theorem ZZ_mul_self {j k : Fin 24} (hjk : j ≠ k) : ZZ j k * ZZ j k = 1 := by
  rw [ZZ, smul_mul_smul_comm, AM_mul_self hjk, smul_smul]; norm_num

theorem ZZ_swap {j k : Fin 24} (hjk : j ≠ k) : ZZ k j = ZZ j k := by
  rw [ZZ_eq_Wop hjk, ZZ_eq_Wop (Ne.symm hjk), aM_swap, Wop_neg, eV_aM_sq hjk, smul_smul,
    εN_root_symm hjk]
  congr 1
  have := golayEps_mul_self j
  linear_combination (golayEps k * εN (golayRoot j) (golayRoot k)) * this

theorem εN_aM_aM {i j k : Fin 24} :
    εN (inclN (aM j k)) (inclN (aM i j)) =
      εN (golayRoot j) (golayRoot i) * golayEps j * εN (golayRoot k) (golayRoot i) *
        εN (golayRoot k) (golayRoot j) := by
  rw [inclN_aM, inclN_aM]
  simp only [εN, latticeCocycle_add_left, latticeCocycle_add_right, latticeCocycle_neg_left,
    latticeCocycle_neg_right]
  rw [← εN_root_self j]; simp only [εN]; ring

/-- **`Z_{jk} Z_{ij} = Z_{ik}`** for distinct `i, j, k`. -/
theorem ZZ_comp {i j k : Fin 24} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ZZ j k * ZZ i j = ZZ i k := by
  rw [ZZ_eq_Wop hjk, ZZ_eq_Wop hij, ZZ_eq_Wop hik, smul_mul_smul_comm, Wop_mul, aM_add, smul_smul,
    εN_aM_aM]
  congr 1
  have ha := εN_root_comm hjk
  have hb := εN_root_comm hij
  have hc := golayEps_mul_self j
  rw [εN_root_symm hik]
  linear_combination (golayEps k * εN (golayRoot i) (golayRoot k)) *
      ((εN (golayRoot i) (golayRoot j) * εN (golayRoot j) (golayRoot i)) * (golayEps j * golayEps j)) * ha
    + (golayEps k * εN (golayRoot i) (golayRoot k)) * (golayEps j * golayEps j) * hb
    + (golayEps k * εN (golayRoot i) (golayRoot k)) * hc

theorem four_dvd_lv_gP (j k i : Fin 24) : (4 : ℤ) ∣ lv (gP j k) i := by
  rw [lv_gP_apply]; exact dvd_mul_right _ _

theorem four_dvd_lv_gM (j k i : Fin 24) : (4 : ℤ) ∣ lv (gM j k) i := by
  rw [lv_gM_apply]; exact dvd_mul_right _ _

theorem form_even_of_four_dvd {x y : leech.carrier} (hx : ∀ i, (4 : ℤ) ∣ lv x i)
    (hy : ∀ i, (4 : ℤ) ∣ lv y i) : Even (leech.form x y) := by
  rw [leech_form_lv]
  have h16 : (16 : ℤ) ∣ lv x ⬝ᵥ lv y :=
    Finset.dvd_sum fun i _ => by
      have := mul_dvd_mul (hx i) (hy i); norm_num at this; exact this
  obtain ⟨m, hm⟩ := h16
  rw [hm, show (16 : ℤ) * m = 8 * (2 * m) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  exact even_two_mul m

theorem commute_eL_of_four {x y : leech.carrier} (hx : ∀ i, (4 : ℤ) ∣ lv x i)
    (hy : ∀ i, (4 : ℤ) ∣ lv y i) : Commute (eL x) (eL y) :=
  commute_eT_of_even leech leech_even leech_isUnit_det_gramMat (form_even_of_four_dvd hx hy)

theorem commute_ZZ_AP (j k l m : Fin 24) : Commute (ZZ j k) (AP l m) :=
  (((commute_eL_of_four (four_dvd_lv_gM j k) (four_dvd_lv_gP l m)).smul_left _).smul_right _).smul_left _

theorem commute_ZZ_AM (j k l m : Fin 24) : Commute (ZZ j k) (AM l m) :=
  (((commute_eL_of_four (four_dvd_lv_gM j k) (four_dvd_lv_gM l m)).smul_left _).smul_right _).smul_left _

/-- The block maps `ψ_0 = B`, `ψ_m = Z_{0m} B`. -/
noncomputable def psiOf (B : End ℂ TLeechT) (m : Fin 24) : TLeechT →ₗ[ℂ] TLeechT :=
  if m = 0 then B else ZZ 0 m * B

theorem psiOf_zero (B : End ℂ TLeechT) : psiOf B 0 = B := if_pos rfl

theorem psiOf_ne {B : End ℂ TLeechT} {m : Fin 24} (hm : m ≠ 0) : psiOf B m = ZZ 0 m * B := if_neg hm

theorem ZZ_apply (j k : Fin 24) (t : TLeechT) :
    ZZ j k t = (2 * kM j k) • eT leech leech_even leech_isUnit_det_gramMat (gM j k) t := by
  rw [ZZ, AM, smul_smul]; rfl

/-- `ψ_k = Z_{jk} ψ_j` for all `j ≠ k`. -/
theorem psiOf_link (B : End ℂ TLeechT) {j k : Fin 24} (hjk : j ≠ k) :
    psiOf B k = ZZ j k * psiOf B j := by
  by_cases hj : j = 0
  · subst hj; rw [psiOf_zero, psiOf_ne (Ne.symm hjk)]
  · by_cases hk : k = 0
    · subst hk
      rw [psiOf_zero, psiOf_ne hj, ← mul_assoc, ZZ_swap hjk, ZZ_mul_self hjk, one_mul]
    · rw [psiOf_ne hk, psiOf_ne hj, ← mul_assoc, ZZ_comp (Ne.symm hj) hjk (Ne.symm hk)]

theorem ZZ_mem_frame {j k : Fin 24} {s : ZMod 2} {t : TLeechT} (ht : t ∈ leechFrameT s) :
    ZZ j k t ∈ leechFrameT s := by
  rw [ZZ_apply]
  refine Submodule.smul_mem _ _ ?_
  have h := eT_mem_leechFrameT (gM j k) ht
  rwa [(mem_lambda0 _).mp (gM_mem j k), add_zero] at h

/-- **`TopSigmaTT` for the seeded block maps `ψ_m = Z_{0m} B`, conditional only on the lattice
letters.**  `B` must land in `T_s ∩ {(A₊+A₋) = 0}` and send `t₁` to a nonzero seed. -/
theorem topSigmaTT_of_seed {s' s : ZMod 2} {B : End ℂ TLeechT} (hBs : ∀ t, B t ∈ leechFrameT s)
    (hBE : ∀ t ∈ leechFrameT s', ∀ j k : Fin 24, j ≠ k → AP j k (B t) + AM j k (B t) = 0)
    {t₁ : TLeechT} (ht₁ : t₁ ∈ leechFrameT s') (hseed : IsSeed (B t₁)) (h0 : B t₁ ≠ 0)
    (hlat : ∀ γ ∈ halfFourChi 0, ZMT (phiTT (psiOf B)) (OmegaT s') (lV' γ)) :
    TopSigmaTT s' s (phiTT (psiOf B)) := by
  have hψ : ∀ m t, psiOf B m t ∈ leechFrameT s := by
    intro m t
    by_cases hm : m = 0
    · subst hm; rw [psiOf_zero]; exact hBs t
    · rw [psiOf_ne hm, Module.End.mul_apply]; exact ZZ_mem_frame (hBs t)
  have hblk : ∀ m, psiOf B m t₁ = B t₁ := by
    intro m
    by_cases hm : m = 0
    · subst hm; rw [psiOf_zero]
    · rw [psiOf_ne hm, Module.End.mul_apply, ZZ, LinearMap.smul_apply, (hseed 0 m (Ne.symm hm)).2,
        smul_smul]; norm_num
  refine topSigmaTT_of_eigen hψ ht₁ (hBs t₁) h0 hblk zhuGenerated_G2 ?_ ?_ ?_ hlat
  · intro j k hjk m t ht
    change AP j k (psiOf B m t) + AM j k (psiOf B m t) = 0
    by_cases hm : m = 0
    · subst hm; rw [psiOf_zero]; exact hBE t ht j k hjk
    · rw [psiOf_ne hm, Module.End.mul_apply, ← Module.End.mul_apply (AP j k),
        ← Module.End.mul_apply (AM j k), ← (commute_ZZ_AP 0 m j k).eq, ← (commute_ZZ_AM 0 m j k).eq,
        Module.End.mul_apply, Module.End.mul_apply, ← map_add, hBE t ht j k hjk, map_zero]
  · intro j k hjk t _
    rw [← ZZ_apply, ← Module.End.mul_apply, ← psiOf_link B hjk]
  · intro j k hjk t _
    rw [← ZZ_apply, ← Module.End.mul_apply, psiOf_link B hjk, ← mul_assoc, ZZ_mul_self hjk, one_mul]

end VOA.Moonshine.SigmaTop
