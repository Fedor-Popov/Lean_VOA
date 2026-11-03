/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Root

/-!
# Assembly on `V₃⁺`: the explicit candidate `φ⋆`

The block assignment `τ⋆(n) = c⋆(n) e_n t` with **`c⋆(n) = i^{n₀} · sign(n_{blk n})`** (`cStar`,
symmetrised to `cE`) — found by solving the transport rules of the root and octad letters by hand
(root moves `γ₊` flip `sign(n_blk)`, `γ₋` keep it; octad moves multiply `c⋆` by the `χ z₀` sign) —
satisfies the root transport rules (`tauStar_ruleP`, `tauStar_ruleM`).

## Main results
* `cStar`, `cE`, `tauStar`, `tauStar_neg`, `tauStar_ruleP`, `tauStar_ruleM`.
* `phiV3_hits'` — `hits_cyclic` for block-wise nonzero multiples (the blocks of `τ⋆` differ by
  the nonzero constants `cE(n_j)/μ_j`).
* `topSigmaV3_of_octad` — `TopSigmaV3 (s+1) φ⋆` from the octad letters alone.
* `OctadResidualV3`, `topSigmaV3_exists`, `sigmaV3T_exists_of_octad`.

## Status
`sorry`-free.  `OctadResidualV3` is proved in `SigmaTop2Class.lean` (`octadResidualV3`).
Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist
open Module (End)

/-! ## §1  The normalisation `c⋆(n) = i^{n₀} · sign(n_{blk n})` -/

/-- The sign of the `±3` entry of `n`. -/
noncomputable def sgnBlk (n : leech.carrier) : ℂ := ((lv n (blk n) : ℤ) : ℂ) / 3

/-- `c⋆(n) = i^{n₀} sign(n_{blk n})`. -/
noncomputable def cStar (n : leech.carrier) : ℂ := Complex.I ^ (lv n 0) * sgnBlk n

/-- The even part of `c⋆` (equal to `c⋆` on odd vectors). -/
noncomputable def cE (n : leech.carrier) : ℂ := (cStar n + cStar (-n)) / 2

/-- **The candidate block assignment** `τ⋆(n) = c⋆(n) e_n t`. -/
noncomputable def tauStar (t : TLeechT) (n : leech.carrier) : TLeechT := cE n • eL n t

theorem cE_neg (n : leech.carrier) : cE (-n) = cE n := by
  rw [cE, cE, neg_neg, add_comm]

theorem tauStar_neg (t : TLeechT) (n : leech.carrier) : tauStar t (-n) = tauStar t n := by
  rw [tauStar, tauStar, cE_neg]
  congr 1
  exact congrArg (fun f : End ℂ TLeechT => f t) (eT_neg leech leech_even leech_isUnit_det_gramMat n)

theorem I_zpow_add_four (x : ℤ) (m : ℤ) : Complex.I ^ (x + 4 * m) = Complex.I ^ x := by
  rw [zpow_add₀ Complex.I_ne_zero, zpow_mul, show Complex.I ^ (4 : ℤ) = 1 by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_pow_four], one_zpow, mul_one]

theorem I_zpow_neg_odd {x : ℤ} (hx : Odd x) : Complex.I ^ (-x) = -Complex.I ^ x := by
  obtain ⟨m, rfl⟩ := hx
  have h : -(2 * m + 1) = (2 * m + 1) + 4 * (-m - 1) + 2 := by ring
  rw [h, zpow_add₀ Complex.I_ne_zero, I_zpow_add_four, show Complex.I ^ (2 : ℤ) = -1 by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq]]
  ring

theorem cStar_neg {n : leech.carrier} (hn : n ∉ lambda0) : cStar (-n) = cStar n := by
  rw [cStar, cStar, lv_neg, Pi.neg_apply, I_zpow_neg_odd (lv_odd_of_not_mem hn 0), sgnBlk, sgnBlk,
    blk_neg, lv_neg, Pi.neg_apply]
  push_cast; ring

theorem cE_eq {n : leech.carrier} (hn : n ∉ lambda0) : cE n = cStar n := by
  rw [cE, cStar_neg hn]; ring

theorem sgnBlk_of {n : leech.carrier} (hn0 : n ∉ lambda0) (h4 : leech.form n n = 4) {i : Fin 24}
    {v : ℤ} (hv : lv n i = v) (h3 : v = 3 ∨ v = -3) : sgnBlk n = (v : ℂ) / 3 := by
  rw [sgnBlk, blk_eq_of_three hn0 h4 (hv ▸ h3), hv]

theorem cStar_ne_zero {n : leech.carrier} (hn0 : n ∉ lambda0) (h4 : leech.form n n = 4) : cStar n ≠ 0 := by
  have h := lv_sq hn0 h4 (blk n)
  rw [if_pos rfl] at h
  rw [cStar, sgnBlk]
  refine mul_ne_zero (zpow_ne_zero _ Complex.I_ne_zero) (div_ne_zero ?_ (by norm_num))
  intro h0
  have : lv n (blk n) = 0 := by exact_mod_cast h0
  rw [this] at h; norm_num at h

/-! ## §2  The root transport rules hold for `τ⋆` -/

theorem eL_gP_seed {t : TLeechT} (ht : IsSeed t) {j k : Fin 24} (hjk : j ≠ k) :
    eL (gP j k) t = (-(2 * kP j k)⁻¹) • t := by
  have h := (ht j k hjk).1
  have hk := kP_ne_zero hjk
  rw [AP, LinearMap.smul_apply] at h
  have h2 := congrArg (fun x => (kP j k)⁻¹ • x) h
  simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at h2
  rw [h2]; congr 1; field_simp

theorem eL_gM_seed {t : TLeechT} (ht : IsSeed t) {j k : Fin 24} (hjk : j ≠ k) :
    eL (gM j k) t = ((2 * kM j k)⁻¹) • t := by
  have h := (ht j k hjk).2
  have hk := kM_ne_zero hjk
  rw [AM, LinearMap.smul_apply] at h
  have h2 := congrArg (fun x => (kM j k)⁻¹ • x) h
  simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at h2
  rw [h2]; congr 1; field_simp

/-- `ε(γ,n) e_{γ+n} t = e_n (e_γ t)` when `⟨γ,n⟩` is even. -/
theorem eps_eL_add (γ n : leech.carrier) (heven : Even (leech.form γ n)) (t : TLeechT) :
    εΛ γ n • eL (γ + n) t = eL n (eL γ t) := by
  have h1 := congrArg (fun f : End ℂ TLeechT => f t) (eT_mul leech leech_even leech_isUnit_det_gramMat γ n)
  have h2 := congrArg (fun f : End ℂ TLeechT => f t) (eT_comm_sign' leech leech_even leech_isUnit_det_gramMat γ n)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1 h2
  rw [heven.neg_one_zpow, one_smul] at h2
  change eL γ (eL n t) = εΛ γ n • eL (γ + n) t at h1
  change eL γ (eL n t) = eL n (eL γ t) at h2
  rw [← h1, h2]

theorem lv_gP_zero (j k : Fin 24) : ∃ m : ℤ, lv (gP j k) 0 = 4 * m := by
  rw [lv_gP_apply]; exact ⟨_, rfl⟩

theorem lv_gM_zero (j k : Fin 24) : ∃ m : ℤ, lv (gM j k) 0 = 4 * m := by
  rw [lv_gM_apply]; exact ⟨_, rfl⟩

theorem cStar_add_root {γ n : leech.carrier} (hm : ∃ m : ℤ, lv γ 0 = 4 * m) :
    Complex.I ^ (lv (γ + n) 0) = Complex.I ^ (lv n 0) := by
  obtain ⟨m, hm⟩ := hm
  rw [lv_add, Pi.add_apply, hm, add_comm, I_zpow_add_four]


theorem pair_vals {n : leech.carrier} (hn0 : n ∉ lambda0) (h4 : leech.form n n = 4) {j k : Fin 24}
    (hjk : j ≠ k) :
    ((lv n j = 3 ∨ lv n j = -3) ∧ (lv n k = 1 ∨ lv n k = -1)) ∨
    ((lv n j = 1 ∨ lv n j = -1) ∧ (lv n k = 3 ∨ lv n k = -3)) ∨
    ((lv n j = 1 ∨ lv n j = -1) ∧ (lv n k = 1 ∨ lv n k = -1)) := by
  have hj := lv_sq hn0 h4 j
  have hk := lv_sq hn0 h4 k
  by_cases hbj : j = blk n
  · rw [if_pos hbj] at hj
    have hkb : k ≠ blk n := fun h => hjk (hbj.trans h.symm)
    rw [if_neg hkb] at hk
    exact Or.inl ⟨int_sq_nine hj, int_sq_one hk⟩
  · rw [if_neg hbj] at hj
    by_cases hbk : k = blk n
    · rw [if_pos hbk] at hk
      exact Or.inr (Or.inl ⟨int_sq_one hj, int_sq_nine hk⟩)
    · rw [if_neg hbk] at hk
      exact Or.inr (Or.inr ⟨int_sq_one hj, int_sq_one hk⟩)

theorem tauStar_ruleP {t : TLeechT} (ht : IsSeed t) {j k : Fin 24} (hjk : j ≠ k) (n : leech.carrier)
    (hn0 : n ∉ lambda0) (h4 : leech.form n n = 4) (hf : leech.form (gP j k) n = -2) :
    εΛ (gP j k) n • tauStar t (gP j k + n) = (2 * kP j k)⁻¹ • tauStar t n := by
  have h0' := not_mem_add (gP_mem j k) hn0
  have h4' := form_self_add (form_gP_self hjk) h4 hf
  have hsq := lv_sq hn0 h4
  have hsq' := lv_sq h0' h4'
  rw [form_gP_left] at hf
  have hj := hsq j
  have hk := hsq k
  have hab : lv n j + lv n k = -4 := by
    have := lv_odd_of_not_mem hn0 j; have := lv_odd_of_not_mem hn0 k
    obtain ⟨x, hx⟩ := lv_odd_of_not_mem hn0 j; obtain ⟨y, hy⟩ := lv_odd_of_not_mem hn0 k
    omega
  -- the two sign patterns
  have hsgn : cE (gP j k + n) = -cE n := by
    rw [cE_eq hn0, cE_eq h0', cStar, cStar, cStar_add_root (lv_gP_zero j k)]
    have hvals : (lv n j = -3 ∧ lv n k = -1) ∨ (lv n j = -1 ∧ lv n k = -3) := by
      rcases pair_vals hn0 h4 hjk with ⟨h1 | h1, h2 | h2⟩ | ⟨h1 | h1, h2 | h2⟩ | ⟨h1 | h1, h2 | h2⟩ <;>
        omega
    rcases hvals with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [sgnBlk_of hn0 h4 ha (Or.inr rfl),
        sgnBlk_of h0' h4' (i := k) (v := 3) (by rw [lv_add, Pi.add_apply, lv_gP_apply, hb]; simp [Ne.symm hjk]) (Or.inl rfl)]
      push_cast; ring
    · rw [sgnBlk_of hn0 h4 hb (Or.inr rfl),
        sgnBlk_of h0' h4' (i := j) (v := 3) (by rw [lv_add, Pi.add_apply, lv_gP_apply, ha]; simp [hjk]) (Or.inl rfl)]
      push_cast; ring
  rw [tauStar, tauStar, smul_comm, eps_eL_add _ _ ⟨-1, by rw [form_gP_left]; omega⟩, eL_gP_seed ht hjk,
    map_smul, hsgn, smul_smul, smul_smul]
  congr 1; ring

theorem tauStar_ruleM {t : TLeechT} (ht : IsSeed t) {j k : Fin 24} (hjk : j ≠ k) (n : leech.carrier)
    (hn0 : n ∉ lambda0) (h4 : leech.form n n = 4) (hf : leech.form (gM j k) n = -2) :
    εΛ (gM j k) n • tauStar t (gM j k + n) = (2 * kM j k)⁻¹ • tauStar t n := by
  have h0' := not_mem_add (gM_mem j k) hn0
  have h4' := form_self_add (form_gM_self hjk) h4 hf
  have hsq := lv_sq hn0 h4
  rw [form_gM_left] at hf
  have hj := hsq j
  have hk := hsq k
  have hab : lv n j - lv n k = -4 := by
    obtain ⟨x, hx⟩ := lv_odd_of_not_mem hn0 j; obtain ⟨y, hy⟩ := lv_odd_of_not_mem hn0 k
    omega
  have hsgn : cE (gM j k + n) = cE n := by
    rw [cE_eq hn0, cE_eq h0', cStar, cStar, cStar_add_root (lv_gM_zero j k)]
    have hvals : (lv n j = -3 ∧ lv n k = 1) ∨ (lv n j = -1 ∧ lv n k = 3) := by
      rcases pair_vals hn0 h4 hjk with ⟨h1 | h1, h2 | h2⟩ | ⟨h1 | h1, h2 | h2⟩ | ⟨h1 | h1, h2 | h2⟩ <;>
        omega
    rcases hvals with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [sgnBlk_of hn0 h4 ha (Or.inr rfl),
        sgnBlk_of h0' h4' (i := k) (v := -3) (by rw [lv_add, Pi.add_apply, lv_gM_apply, hb]; simp [Ne.symm hjk]) (Or.inr rfl)]
    · rw [sgnBlk_of hn0 h4 hb (Or.inl rfl),
        sgnBlk_of h0' h4' (i := j) (v := 3) (by rw [lv_add, Pi.add_apply, lv_gM_apply, ha]; simp [hjk]) (Or.inl rfl)]
  rw [tauStar, tauStar, smul_comm, eps_eL_add _ _ ⟨-1, by rw [form_gM_left]; omega⟩, eL_gM_seed ht hjk,
    map_smul, hsgn, smul_smul, smul_smul]
  congr 1; ring

/-! ## §3  Assembly: `TopSigmaV3` for `φ⋆ = φ_{τ⋆}`, conditional on the octad letters -/

/-- `φ_τ` hits `x0T t₀` as soon as every block contains a nonzero multiple of `t₀`. -/
theorem phiV3_hits' {τ : leech.carrier → TLeechT} {t₀ : TLeechT} (lam' : Fin 24 → ℂ)
    (hl : ∀ j, lam' j ≠ 0) (hblk : ∀ j, τ (nvec j) = lam' j • t₀) :
    ∃ x ∈ OmegaV3, phiV3 τ x = x0T t₀ := by
  set c0 : Fin (rank leech) := Fin.cast leech_rank.symm 0
  refine ⟨∑ j, ((cw j c0 / 8) * (lam' j)⁻¹) • frameX0P (nvec j),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (frameX0P_mem_OmegaV3 (nvec_mem j)), ?_⟩
  rw [map_sum, x0T_eq_hP, single_eq_sum_cw, hP_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, phiV3_frameX0P τ (nvec_mem j), blk_nvec, hblk, hP_smul_right, smul_smul,
    mul_assoc, inv_mul_cancel₀ (hl j), mul_one, hP_smul_left]

theorem lV'_neg (γ : leech.carrier) : lV' (-γ) = lV' γ := by
  by_cases h : γ ∈ lambda0
  · have h' : -γ ∈ lambda0 := neg_mem h
    rw [lV'_eq h, lV'_eq h']
    apply Subtype.ext
    exact frameX0P_neg γ
  · have h' : -γ ∉ lambda0 := fun h'' => h (by simpa using neg_mem h'')
    rw [lV', lV', dif_neg h, dif_neg h']

theorem mu_ne_zero (j : Fin 24) : mu j ≠ 0 := by
  unfold mu; split_ifs with hj
  · exact one_ne_zero
  · exact mul_ne_zero (εΛ_ne_zero _ _) (mul_ne_zero two_ne_zero (kM_ne_zero (Ne.symm hj)))

theorem nvec_not_mem (j : Fin 24) : nvec j ∉ lambda0 := by
  have := (mem_halfFourChi (nvec_mem j)).2
  rw [mem_lambda0, this]; exact one_ne_zero

/-- **The octad residual on `V₃⁺`**: the zero-mode identity for every lattice letter that is not
of `(±4,±4,0²²)` type (mathematically: the octad letters `(±2⁸,0¹⁶)`). -/
def OctadV3 (τ : leech.carrier → TLeechT) : Prop :=
  ∀ γ ∈ halfFourChi 0, (∀ j k : Fin 24, j ≠ k → γ ≠ gP j k ∧ γ ≠ -gP j k ∧ γ ≠ gM j k ∧ γ ≠ -gM j k) →
    ZM (phiV3 τ) OmegaV3 (lV' γ)

/-- **(R-top) on `V₃⁺`, reduced to the octad letters.**  For a seed `t ∈ T_s` the explicit map
`φ⋆ = φ_{τ⋆}`, `τ⋆(n) = i^{n₀} sign(n_{blk n}) e_n t`, satisfies `TopSigmaV3 (s+1)` as soon as the
octad letters intertwine. -/
theorem topSigmaV3_of_octad {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) (hoct : OctadV3 (tauStar t)) :
    TopSigmaV3 (s + 1) (phiV3 (tauStar t)) := by
  have hτ : ∀ n ∈ halfFourChi 1, tauStar t n ∈ leechFrameT (s + 1) := by
    intro n hn
    have := eT_mem_leechFrameT n hts
    rw [(mem_halfFourChi hn).2] at this
    exact Submodule.smul_mem _ _ this
  have hm1 : eL (mvec 0) t ∈ leechFrameT (s + 1) := by
    have := eT_mem_leechFrameT (mvec 0) hts
    rwa [frameChar_eq_one (mvec_not_mem 0)] at this
  have h0 : eL (mvec 0) t ≠ 0 := fun h => ht0 (eL_injective _ (by rw [h, map_zero]))
  have heig : ∀ j k : Fin 24, j ≠ k → ∀ n ∈ halfFourChi 1,
      kP j k • eL (gP j k) (tauStar t n) = lam j k n • tauStar t n ∧
      kM j k • eL (gM j k) (tauStar t n) = lam j k n • tauStar t n :=
    fun j k hjk n hn => eig_of_seed ht cE hjk hn
  have hblk : ∀ j, tauStar t (nvec j) = (cE (nvec j) * (mu j)⁻¹) • eL (mvec 0) t := by
    intro j
    rw [tauStar, ← mu_nvec ht j, smul_smul, mul_assoc, inv_mul_cancel₀ (mu_ne_zero j), mul_one]
  have hl : ∀ j, cE (nvec j) * (mu j)⁻¹ ≠ 0 := fun j =>
    mul_ne_zero (by rw [cE_eq (nvec_not_mem j)]
                    exact cStar_ne_zero (nvec_not_mem j) (mem_halfFourChi (nvec_mem j)).1)
      (inv_ne_zero (mu_ne_zero j))
  refine topSigmaV3_of_zhuGenerated (fun x _ => phiV3_mem_frame hτ x)
    (fun x _ => phiV3_mem_weight _ x) zhuGenerated_G2 ?_
    ⟨eL (mvec 0) t, hm1, h0, phiV3_hits' _ hl hblk⟩
  have hdV : ∀ j k : Fin 24, ZM (phiV3 (tauStar t)) OmegaV3 (dV (fw j) (fw k)) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; exact phiV3_ZM_diag _ j
    · exact phiV3_ZM_offdiag _ hjk (heig j k hjk)
  refine hGφ_V3_of_basis _ (fun a b n hn => ?_) (fun γ hγ n hn => ?_)
  · have hq := ZM_span (phiV3 (tauStar t)) OmegaV3
      (S := Set.range fun p : Fin 24 × Fin 24 => dV (fw p.1) (fw p.2))
      (by rintro _ ⟨p, rfl⟩; exact hdV p.1 p.2) (qV a b) (qV_mem_span_dV a b)
    exact hq _ (frameX0P_mem_OmegaV3 hn)
  · have hev := tauStar_neg t
    have hZM : ZM (phiV3 (tauStar t)) OmegaV3 (lV' γ) := by
      by_cases hroot : ∃ j k : Fin 24, j ≠ k ∧ (γ = gP j k ∨ γ = -gP j k ∨ γ = gM j k ∨ γ = -gM j k)
      · obtain ⟨j, k, hjk, hγ'⟩ := hroot
        have hP := phiV3_ZM_gP hev hjk (heig j k hjk) (fun n hn0 h4 hf => tauStar_ruleP ht hjk n hn0 h4 hf)
        have hM := phiV3_ZM_gM hev hjk (heig j k hjk) (fun n hn0 h4 hf => tauStar_ruleM ht hjk n hn0 h4 hf)
        rcases hγ' with rfl | rfl | rfl | rfl
        · rw [lV'_eq (gP_mem j k)]; exact hP
        · rw [lV'_neg, lV'_eq (gP_mem j k)]; exact hP
        · rw [lV'_eq (gM_mem j k)]; exact hM
        · rw [lV'_neg, lV'_eq (gM_mem j k)]; exact hM
      · push Not at hroot
        exact hoct γ hγ fun j k hjk => by
          obtain ⟨h1, h2, h3, h4⟩ := hroot j k hjk
          exact ⟨h1, h2, h3, h4⟩
    exact hZM _ (frameX0P_mem_OmegaV3 hn)

/-- **The octad residual, for all seeds.** -/
def OctadResidualV3 : Prop :=
  ∀ (s : ZMod 2) (t : TLeechT), t ∈ leechFrameT s → t ≠ 0 → IsSeed t → OctadV3 (tauStar t)

/-- **`∃ s φ, TopSigmaV3 s φ` from the octad residual alone** (the eigen-conditions, the Fock
letters and the `(±4,±4)` letters are all proved; `ZhuGenerated` is `zhuGenerated_weightTwo`). -/
theorem topSigmaV3_exists (h : OctadResidualV3) : ∃ s φ, TopSigmaV3 s φ := by
  obtain ⟨s, t, hts, ht0, ht⟩ := seed_in_frame seedExists
  exact ⟨s + 1, _, topSigmaV3_of_octad hts ht0 ht (h s t hts ht0 ht)⟩

/-- **σ on `V₃⁺`, from the octad residual.** -/
theorem sigmaV3T_exists_of_octad (h : OctadResidualV3) :
    ∃ (s : ZMod 2) (Φ : VPlus →ₗ[ℂ] TP), IsSigmaV3T Φ ∧
      ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, Φ x = x0T t₀ :=
  sigmaV3T_exists_of_top' (topSigmaV3_exists h)

end VOA.Moonshine.SigmaTop
