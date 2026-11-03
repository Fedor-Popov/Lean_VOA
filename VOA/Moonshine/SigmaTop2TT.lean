/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Class

/-!
# (R-top) on `T_s⁺`: the operator `B` and the root letters

The block maps are `ψ₀ = B`, `ψ_m = Z_{0m} B` (`SigmaTop2Eigen.psiOf`), with
`B = ∏_{k ≠ 0} (a + b Z_{0k}) ∘ proj_s`, `a = (1+ω)/2`, `b = (1−ω)/2`, `ω = e^{iπ/4}` (`Bop`).

* On the frame sector of a seed, `A₋ = −A₊` (`AM_eq_neg_AP`): `e_{γ₊} e_{γ₋}⁻¹` is a multiple of
  `e_{8e_j}`, which acts on `T_s` by the frame scalar, read off at the seed.  Hence every `ψ_m`
  satisfies the eigen-conditions of `topSigmaTT_of_seed` on all of `T_s`.
* `B` commutes with every `e_γ`, `γ ∈ 4ℤ²⁴ ∩ Λ₀` (`commute_eL_Bop`), preserves `T_s`
  (`Bop_mem`), acts on a joint `Z_{0k}`-eigenvector by `∏ (a + b u_k)` (`Bop_eigen`) and fixes the
  seed (`Bop_seed`).
* `topSigmaTT_of_seedB`: `TopSigmaTT s s φ_B`, conditional only on the lattice letters.
* `phiTT_ZMT_gP`, `phiTT_ZMT_gM`: the `(±4,±4,0²²)` letters intertwine.

The octad letters (where the choice of `B` matters) are in `SigmaTop2TTOct.lean`.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist
open Module (End)

/-! ## §1  `A₋ = −A₊` on the seed's frame sector -/

theorem fw_eq_frameW_add (j : Fin 24) : fw j = frameW + 2 • gM j 0 := by
  apply Subtype.ext
  change lv (fw j) = lv frameW + 2 • lv (gM j 0)
  rw [lv_fw, lv_gM]
  change _ = (8 : ℤ) • e0 + _
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_apply, Pi.sub_apply, nsmul_eq_mul]
  by_cases hi : i = j <;> by_cases h0 : i = 0 <;> simp [hi, h0] <;> subst_vars <;> simp_all

theorem eL_fw (j : Fin 24) : eL (fw j) = eL frameW := by
  rw [fw_eq_frameW_add]; exact eT_add_two_nsmul leech leech_even leech_isUnit_det_gramMat _ _

theorem eL_frameW_apply {s : ZMod 2} {x : TLeechT} (hx : x ∈ leechFrameT s) :
    eL frameW x = (FrameT.sqrtEps leech frameW * Extraspecial.sgn s) • x := by
  have hJ : frameJL x = Extraspecial.sgn s • x := (FrameT.mem_frameT _ _ _).mp hx
  have h : eL frameW = FrameT.sqrtEps leech frameW • frameJL := by
    rw [frameJL, FrameT.frameJ, smul_smul, mul_inv_cancel₀ (FrameT.sqrtEps_ne_zero _ _), one_smul]
  rw [h, LinearMap.smul_apply, hJ, smul_smul]

theorem gP_add_gM (j k : Fin 24) : gP j k + gM j k = fw j := by
  apply Subtype.ext
  change lv (gP j k) + lv (gM j k) = lv (fw j)
  rw [lv_gP, lv_gM, lv_fw]
  funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]; ring

/-- `A₊A₋` is a scalar on each frame sector. -/
theorem AP_AM_frame {s : ZMod 2} {x : TLeechT} (hx : x ∈ leechFrameT s) (j k : Fin 24) :
    AP j k (AM j k x) = (kP j k * kM j k * εΛ (gP j k) (gM j k) *
      (FrameT.sqrtEps leech frameW * Extraspecial.sgn s)) • x := by
  rw [AP, AM, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, smul_smul]
  have h := congrArg (fun f : End ℂ TLeechT => f x) (eT_mul leech leech_even leech_isUnit_det_gramMat (gP j k) (gM j k))
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
  change eL (gP j k) (eL (gM j k) x) = εΛ (gP j k) (gM j k) • eL (gP j k + gM j k) x at h
  rw [h, gP_add_gM, eL_fw, eL_frameW_apply hx, smul_smul, smul_smul]

/-- **`A₋ = −A₊` on the seed's frame sector.** -/
theorem AM_eq_neg_AP {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0) (ht : IsSeed t)
    {j k : Fin 24} (hjk : j ≠ k) {x : TLeechT} (hx : x ∈ leechFrameT s) : AM j k x = -AP j k x := by
  have hc := AP_AM_frame hts j k
  have hseed := ht j k hjk
  rw [hseed.2, map_smul, hseed.1, smul_smul] at hc
  set c := kP j k * kM j k * εΛ (gP j k) (gM j k) * (FrameT.sqrtEps leech frameW * Extraspecial.sgn s)
  have hc' : c = -(1 / 4 : ℂ) := by
    have := sub_eq_zero.mpr hc
    rw [← sub_smul] at this
    have := (smul_eq_zero.mp this).resolve_right ht0
    linear_combination -this
  have hx' := AP_AM_frame hx j k
  change AP j k (AM j k x) = c • x at hx'
  rw [hc'] at hx'
  have hPP := congrArg (fun f : End ℂ TLeechT => f (AM j k x)) (AP_mul_self hjk)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at hPP
  rw [hx', map_smul] at hPP
  have : AM j k x = (4 : ℂ) • ((1 / 4 : ℂ) • AM j k x) := by rw [smul_smul]; norm_num
  rw [this, ← hPP, smul_smul]
  norm_num

/-! ## §2  The operator `B = ∏_{k ≠ 0} (a + b Z_{0k})` -/

/-- `ω = e^{iπ/4}`. -/
noncomputable def ωB : ℂ := rH * (1 + Complex.I)
noncomputable def aB : ℂ := (1 + ωB) / 2
noncomputable def bB : ℂ := (1 - ωB) / 2

/-- The local factor `a + b Z_{0k}` (`1` for `k = 0`). -/
noncomputable def factB (k : Fin 24) : End ℂ TLeechT := if k = 0 then 1 else aB • 1 + bB • ZZ 0 k

/-- `∏_k (a + b Z_{0k})`. -/
noncomputable def Bprod : End ℂ TLeechT := ((List.finRange 24).map factB).prod

/-- **The `T`-part of `σ` on `T_{s}⁺`**: `B = (∏_{k≠0} (a + b Z_{0k})) ∘ π_s`; on a joint
eigenvector of the `Z_{0k}` with eigenvalues `u_k` it acts by `ω^{#{k : u_k = −1}}`. -/
noncomputable def Bop (s : ZMod 2) : End ℂ TLeechT := Bprod * projT s

theorem list_prod_eigen (l : List (Fin 24)) (f : Fin 24 → End ℂ TLeechT) (g : Fin 24 → ℂ) {z : TLeechT}
    (h : ∀ k, f k z = g k • z) : (l.map f).prod z = (l.map g).prod • z := by
  induction l with
  | nil => simp
  | cons k l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, ih,
      map_smul, h, smul_smul, mul_comm]

theorem list_prod_commute (l : List (Fin 24)) (f : Fin 24 → End ℂ TLeechT) (X : End ℂ TLeechT)
    (h : ∀ k, Commute X (f k)) : Commute X (l.map f).prod := by
  induction l with
  | nil => simp
  | cons k l ih => rw [List.map_cons, List.prod_cons]; exact (h k).mul_right ih

theorem factB_eigen {z : TLeechT} {u : Fin 24 → ℂ} (hu : ∀ k, k ≠ 0 → ZZ 0 k z = u k • z) (k : Fin 24) :
    factB k z = (if k = 0 then 1 else aB + bB * u k) • z := by
  unfold factB
  split_ifs with hk
  · simp
  · rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      hu k hk, smul_smul, ← add_smul]

theorem Bprod_eigen {z : TLeechT} {u : Fin 24 → ℂ} (hu : ∀ k, k ≠ 0 → ZZ 0 k z = u k • z) :
    Bprod z = ((List.finRange 24).map fun k => if k = 0 then 1 else aB + bB * u k).prod • z :=
  list_prod_eigen _ _ _ (factB_eigen hu)

theorem commute_factB (X : End ℂ TLeechT) (hX : ∀ k, k ≠ 0 → Commute X (ZZ 0 k)) (k : Fin 24) :
    Commute X (factB k) := by
  unfold factB; split_ifs with hk
  · exact Commute.one_right X
  · exact ((Commute.one_right X).smul_right _).add_right ((hX k hk).smul_right _)

theorem commute_Bop (s : ZMod 2) (X : End ℂ TLeechT) (hX : ∀ k, k ≠ 0 → Commute X (ZZ 0 k))
    (hJ : Commute X frameJL) : Commute X (Bop s) := by
  refine (list_prod_commute _ _ X (commute_factB X hX)).mul_right ?_
  have : projT s = (1 / 2 : ℂ) • (1 + Extraspecial.sgn s • frameJL) := rfl
  rw [this]
  exact ((Commute.one_right X).add_right (hJ.smul_right _)).smul_right _

theorem ZZ_comm_frameJL (j k : Fin 24) : Commute (ZZ j k) frameJL := by
  have h := frameJL_comm_eL (gM_mem j k)
  exact ((((Commute.symm h)).smul_left _).smul_left _)

theorem factB_mem_frame {s : ZMod 2} {x : TLeechT} (hx : x ∈ leechFrameT s) (k : Fin 24) :
    factB k x ∈ leechFrameT s := by
  unfold factB; split_ifs
  · exact hx
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ (ZZ_mem_frame hx))

theorem list_prod_mem_frame {s : ZMod 2} (l : List (Fin 24)) {x : TLeechT} (hx : x ∈ leechFrameT s) :
    (l.map factB).prod x ∈ leechFrameT s := by
  induction l with
  | nil => simpa
  | cons k l ih => rw [List.map_cons, List.prod_cons, Module.End.mul_apply]; exact factB_mem_frame ih k

theorem Bop_mem (s : ZMod 2) (x : TLeechT) : Bop s x ∈ leechFrameT s := by
  rw [Bop, Module.End.mul_apply, Bprod]; exact list_prod_mem_frame _ (projT_mem s x)

theorem aB_add_bB : aB + bB = 1 := by unfold aB bB; ring

theorem Bop_eigen {s : ZMod 2} {z : TLeechT} (hz : z ∈ leechFrameT s) {u : Fin 24 → ℂ}
    (hu : ∀ k, k ≠ 0 → ZZ 0 k z = u k • z) :
    Bop s z = ((List.finRange 24).map fun k => if k = 0 then 1 else aB + bB * u k).prod • z := by
  rw [Bop, Module.End.mul_apply, projT_of_mem hz, Bprod_eigen hu]

theorem ZZ_seed {t : TLeechT} (ht : IsSeed t) {k : Fin 24} (hk : k ≠ 0) : ZZ 0 k t = (1 : ℂ) • t := by
  rw [ZZ, LinearMap.smul_apply, (ht 0 k (Ne.symm hk)).2, smul_smul]; norm_num

theorem Bop_seed {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht : IsSeed t) : Bop s t = t := by
  rw [Bop_eigen hts (u := fun _ => 1) (fun k hk => ZZ_seed ht hk)]
  have : ∀ l : List (Fin 24), (l.map fun k => if k = 0 then (1 : ℂ) else aB + bB * 1).prod = 1 := by
    intro l; induction l with
    | nil => simp
    | cons k l ih => rw [List.map_cons, List.prod_cons, ih]; split_ifs <;> simp [aB_add_bB]
  rw [this, one_smul]

/-! ## §3  The eigen-conditions on `T_s⁺` -/

/-- **`TopSigmaTT s s φ_B`, conditional only on the lattice letters**, for a seed `t ∈ T_s`. -/
theorem topSigmaTT_of_seedB {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) (hlat : ∀ γ ∈ halfFourChi 0, ZMT (phiTT (psiOf (Bop s))) (OmegaT s) (lV' γ)) :
    TopSigmaTT s s (phiTT (psiOf (Bop s))) := by
  refine topSigmaTT_of_seed (Bop_mem s) (fun x _ j k hjk => ?_) hts (by rw [Bop_seed hts ht]; exact ht)
    (by rw [Bop_seed hts ht]; exact ht0) hlat
  rw [AM_eq_neg_AP hts ht0 ht hjk (Bop_mem s x), add_neg_cancel]

/-! ## §4  The root letters on `T_s⁺` -/

theorem commute_eL_ZZ {γ : leech.carrier} (hγ : ∀ i, (4 : ℤ) ∣ lv γ i) (j k : Fin 24) :
    Commute (eL γ) (ZZ j k) :=
  (((commute_eL_of_four hγ (four_dvd_lv_gM j k)).smul_right _).smul_right _)

theorem commute_eL_Bop {γ : leech.carrier} (hγ : ∀ i, (4 : ℤ) ∣ lv γ i) (hγ0 : γ ∈ lambda0) (s : ZMod 2) :
    Commute (eL γ) (Bop s) :=
  commute_Bop s _ (fun k _ => commute_eL_ZZ hγ 0 k) (frameJL_comm_eL hγ0).symm

theorem psiOf_comm {γ : leech.carrier} (hγ : ∀ i, (4 : ℤ) ∣ lv γ i) (hγ0 : γ ∈ lambda0) (s : ZMod 2)
    (m : Fin 24) (t : TLeechT) : psiOf (Bop s) m (eL γ t) = eL γ (psiOf (Bop s) m t) := by
  by_cases hm : m = 0
  · subst hm; rw [psiOf_zero]
    exact (congrArg (fun f : End ℂ TLeechT => f t) (commute_eL_Bop hγ hγ0 s).eq).symm
  · rw [psiOf_ne hm, Module.End.mul_apply, Module.End.mul_apply]
    have h1 := congrArg (fun f : End ℂ TLeechT => f t) (commute_eL_Bop hγ hγ0 s).eq
    have h2 := congrArg (fun f : End ℂ TLeechT => f (Bop s t)) (commute_eL_ZZ hγ 0 m).eq
    simp only [Module.End.mul_apply] at h1 h2
    rw [← h1, h2]

theorem psiOf_mem {s : ZMod 2} (m : Fin 24) (t : TLeechT) : psiOf (Bop s) m t ∈ leechFrameT s := by
  by_cases hm : m = 0
  · subst hm; rw [psiOf_zero]; exact Bop_mem s t
  · rw [psiOf_ne hm, Module.End.mul_apply]; exact ZZ_mem_frame (Bop_mem s t)

theorem actT_sig_lV_gP_gen {j k : Fin 24} (hjk : j ≠ k) (m : Fin 24) (x : TLeechT) :
    actT (sig (lV (gP j k) (gP_mem j k))) 1 (hP (cw m) x)
      = (2 * kP j k)⁻¹ • ((1 / 8 : ℂ) • hP (dL (fw j) (fw k) (cw m)) x
        + kP j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (eL (gP j k) x))
        - kM j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (eL (gM j k) x))) := by
  rw [sig_lV_gP hjk, actT_smul_left, actT_sub_left', actT_add_left, actT_smul_left, actT_smul_left,
    actT_smul_left, actT_dV_hP, actT_lV_hP (gP_mem j k) (form_gP_self hjk),
    actT_lV_hP (gM_mem j k) (form_gM_self hjk)]

theorem actT_sig_lV_gM_gen {j k : Fin 24} (hjk : j ≠ k) (m : Fin 24) (x : TLeechT) :
    actT (sig (lV (gM j k) (gM_mem j k))) 1 (hP (cw m) x)
      = (2 * kM j k)⁻¹ • ((1 / 8 : ℂ) • hP (dL (fw j) (fw k) (cw m)) x
        - kP j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (eL (gP j k) x))
        + kM j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (eL (gM j k) x))) := by
  rw [sig_lV_gM hjk, actT_smul_left, actT_add_left, actT_sub_left', actT_smul_left, actT_smul_left,
    actT_smul_left, actT_dV_hP, actT_lV_hP (gP_mem j k) (form_gP_self hjk),
    actT_lV_hP (gM_mem j k) (form_gM_self hjk)]

theorem two_zpow_neg_three : (2 : ℂ) ^ (-(3 : ℤ)) = 1 / 8 := by norm_num

theorem phiTT_hP_cw (ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT) (m : Fin 24) (c : ℂ) (j k : Fin 24) (z : TLeechT)
    (sgn : ℂ) :
    phiTT ψ (hP (cw m - c • (cw j + sgn • cw k)) z)
      = hP (cw m) (ψ m z) - c • (hP (cw j) (ψ j z) + sgn • hP (cw k) (ψ k z)) := by
  rw [hP_sub_left, hP_smul_left, hP_add_left, hP_smul_left, map_sub, map_smul, map_add, map_smul,
    phiTT_hP, phiTT_hP, phiTT_hP]

theorem hP_zero_left (t : TLeechT) : hP 0 t = 0 := by
  apply Subtype.ext; simp [hP_coe, hvec]

theorem phiTT_ZMT_gP {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0) (ht : IsSeed t)
    {j k : Fin 24} (hjk : j ≠ k) :
    ZMT (phiTT (psiOf (Bop s))) (OmegaT s) (lV (gP j k) (gP_mem j k)) := by
  refine ZMT_of_basis _ s _ fun m t' ht' => ?_
  have hcP : ∀ l (y : TLeechT), psiOf (Bop s) l (eL (gP j k) y) = eL (gP j k) (psiOf (Bop s) l y) :=
    fun l y => psiOf_comm (four_dvd_lv_gP j k) (gP_mem j k) s l y
  have hE : ∀ y ∈ leechFrameT s, kM j k • eL (gM j k) y = -(kP j k • eL (gP j k) y) :=
    fun y hy => AM_eq_neg_AP hts ht0 ht hjk hy
  have hmem : ∀ l y, psiOf (Bop s) l y ∈ leechFrameT s := fun l y => psiOf_mem l y
  have hePmem : ∀ y ∈ leechFrameT s, eL (gP j k) y ∈ leechFrameT s := fun y hy => by
    have := eT_mem_leechFrameT (gP j k) hy; rwa [(mem_lambda0 _).mp (gP_mem j k), add_zero] at this
  have hsq := kP_sq hjk
  have hkP := kP_ne_zero hjk
  have hPP : ∀ y, eL (gP j k) (eL (gP j k) y) = εΛ (gP j k) (gP j k) • y := fun y => by
    rw [← Module.End.mul_apply, eL_mul_self]; rfl
  -- `ψ_k (e_{γ₊} y) = −2κ₊ε ψ_j y` and symmetrically
  have hlinkP : ∀ {a b : Fin 24}, a ≠ b → (a = j ∧ b = k ∨ a = k ∧ b = j) →
      psiOf (Bop s) b (eL (gP j k) t') = (-(2 * kP j k * εΛ (gP j k) (gP j k))) • psiOf (Bop s) a t' := by
    intro a b hab hcase
    have hl : psiOf (Bop s) b = ZZ j k * psiOf (Bop s) a := by
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact psiOf_link (Bop s) hjk
      · rw [psiOf_link (Bop s) hjk, ← mul_assoc, ZZ_mul_self hjk, one_mul]
    rw [hl, Module.End.mul_apply, hcP, ZZ_apply, ← smul_smul,
      hE _ (hePmem _ (hmem a t')), smul_neg, ← smul_assoc, smul_eq_mul, hPP, smul_smul, neg_smul]
  rw [actT_lV_hP (gP_mem j k) (form_gP_self hjk), map_smul, latL_gP_cw, phiTT_hP,
    actT_sig_lV_gP_gen hjk m (psiOf (Bop s) m t')]
  rw [show kM j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (eL (gM j k) (psiOf (Bop s) m t')))
      = (2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gM j k) (cw m)) (-(kP j k • eL (gP j k) (psiOf (Bop s) m t'))) by
    rw [← hE _ (hmem m t'), hP_smul_right, smul_comm]]
  rw [latL_gP_cw, latL_gM_cw, dL_fw_off hjk, lv_gP_apply, lv_gM_apply, two_zpow_neg_three]
  have hr : (2 * kP j k)⁻¹ * (2 * kP j k) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hkP)
  by_cases hmj : m = j
  · subst hmj
    simp only [if_true, if_neg hjk, if_neg (Ne.symm hjk)]
    push_cast
    simp only [hP_sub_left, hP_add_left, hP_smul_left, hP_smul_right, hP_neg_right, hP_zero_left,
      map_sub, map_add, map_smul, phiTT_hP, smul_zero, zero_smul, add_zero, zero_add, mul_one, mul_zero,
      sub_zero]
    rw [hcP, hlinkP hjk (Or.inl ⟨rfl, rfl⟩)]
    simp only [hP_smul_right, smul_smul]
    have hA : (2 * kP m k)⁻¹ * kP m k = 1 / 2 := by field_simp
    have hB : kP m k * εΛ (gP m k) (gP m k) = (2 * kP m k)⁻¹ * (1 / 2) := by
      field_simp; linear_combination 4 * hsq
    linear_combination (norm := module) ((6 / 8 : ℂ) * hA) • hP (cw m) (eL (gP m k) (psiOf (Bop s) m t'))
      + hB • hP (cw k) (psiOf (Bop s) m t')
  · have hA : (2 * kP j k)⁻¹ * kP j k = 1 / 2 := by field_simp
    have hB : kP j k * εΛ (gP j k) (gP j k) = (2 * kP j k)⁻¹ * (1 / 2) := by
      field_simp; linear_combination 4 * hsq
    by_cases hmk : m = k
    · subst hmk
      simp only [if_true, if_neg hmj]
      push_cast
      simp only [hP_sub_left, hP_add_left, hP_smul_left, hP_smul_right, hP_neg_right, hP_zero_left,
        map_sub, map_add, map_smul, phiTT_hP, smul_zero, zero_smul, add_zero, zero_add]
      rw [hcP, hlinkP (Ne.symm hjk) (Or.inr ⟨rfl, rfl⟩)]
      simp only [hP_smul_right, smul_smul]
      linear_combination (norm := module) ((6 / 8 : ℂ) * hA) • hP (cw m) (eL (gP j m) (psiOf (Bop s) m t'))
        + hB • hP (cw j) (psiOf (Bop s) m t')
    · simp only [if_neg hmj, if_neg hmk]
      push_cast
      simp only [hP_sub_left, hP_add_left, hP_smul_left, hP_smul_right, hP_neg_right, hP_zero_left,
        map_sub, map_add, map_smul, phiTT_hP, smul_zero, zero_smul, add_zero, zero_add, sub_zero]
      rw [hcP]
      linear_combination (norm := module) ((-1 / 4 : ℂ) * hA) • hP (cw m) (eL (gP j k) (psiOf (Bop s) m t'))

theorem phiTT_ZMT_gM {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0) (ht : IsSeed t)
    {j k : Fin 24} (hjk : j ≠ k) :
    ZMT (phiTT (psiOf (Bop s))) (OmegaT s) (lV (gM j k) (gM_mem j k)) := by
  refine ZMT_of_basis _ s _ fun m t' ht' => ?_
  have hcM : ∀ l (y : TLeechT), psiOf (Bop s) l (eL (gM j k) y) = eL (gM j k) (psiOf (Bop s) l y) :=
    fun l y => psiOf_comm (four_dvd_lv_gM j k) (gM_mem j k) s l y
  have hE : ∀ y ∈ leechFrameT s, kP j k • eL (gP j k) y = -(kM j k • eL (gM j k) y) := fun y hy => by
    have := AM_eq_neg_AP hts ht0 ht hjk hy
    change kM j k • eL (gM j k) y = -(kP j k • eL (gP j k) y) at this
    rw [this, neg_neg]
  have hmem : ∀ l y, psiOf (Bop s) l y ∈ leechFrameT s := fun l y => psiOf_mem l y
  have hsq := kM_sq hjk
  have hkM := kM_ne_zero hjk
  have hMM : ∀ y, eL (gM j k) (eL (gM j k) y) = εΛ (gM j k) (gM j k) • y := fun y => by
    rw [← Module.End.mul_apply, eL_mul_self]; rfl
  have hlinkM : ∀ {a b : Fin 24}, a ≠ b → (a = j ∧ b = k ∨ a = k ∧ b = j) →
      psiOf (Bop s) b (eL (gM j k) t') = (2 * kM j k * εΛ (gM j k) (gM j k)) • psiOf (Bop s) a t' := by
    intro a b hab hcase
    have hl : psiOf (Bop s) b = ZZ j k * psiOf (Bop s) a := by
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact psiOf_link (Bop s) hjk
      · rw [psiOf_link (Bop s) hjk, ← mul_assoc, ZZ_mul_self hjk, one_mul]
    rw [hl, Module.End.mul_apply, hcM, ZZ_apply, hMM, smul_smul]
  rw [actT_lV_hP (gM_mem j k) (form_gM_self hjk), map_smul, latL_gM_cw, phiTT_hP,
    actT_sig_lV_gM_gen hjk m (psiOf (Bop s) m t')]
  rw [show kP j k • ((2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (eL (gP j k) (psiOf (Bop s) m t')))
      = (2 : ℂ) ^ (-(3 : ℤ)) • hP (latL (gP j k) (cw m)) (-(kM j k • eL (gM j k) (psiOf (Bop s) m t'))) by
    rw [← hE _ (hmem m t'), hP_smul_right, smul_comm]]
  rw [latL_gP_cw, latL_gM_cw, dL_fw_off hjk, lv_gP_apply, lv_gM_apply, two_zpow_neg_three]
  have hA : (2 * kM j k)⁻¹ * kM j k = 1 / 2 := by field_simp
  have hB : kM j k * εΛ (gM j k) (gM j k) = (2 * kM j k)⁻¹ * (1 / 2) := by
    field_simp; linear_combination 4 * hsq
  by_cases hmj : m = j
  · subst hmj
    simp only [if_true, if_neg hjk, if_neg (Ne.symm hjk)]
    push_cast
    simp only [hP_sub_left, hP_add_left, hP_smul_left, hP_smul_right, hP_neg_right, hP_zero_left,
      map_sub, map_add, map_smul, phiTT_hP, smul_zero, zero_smul, add_zero, zero_add]
    rw [hcM, hlinkM hjk (Or.inl ⟨rfl, rfl⟩)]
    simp only [hP_smul_right, smul_smul]
    linear_combination (norm := module) ((6 / 8 : ℂ) * hA) • hP (cw m) (eL (gM m k) (psiOf (Bop s) m t'))
      + hB • hP (cw k) (psiOf (Bop s) m t')
  · by_cases hmk : m = k
    · subst hmk
      simp only [if_true, if_neg hmj]
      push_cast
      simp only [hP_sub_left, hP_add_left, hP_smul_left, hP_smul_right, hP_neg_right, hP_zero_left,
        map_sub, map_add, map_smul, phiTT_hP, smul_zero, zero_smul, add_zero, zero_add]
      rw [hcM, hlinkM (Ne.symm hjk) (Or.inr ⟨rfl, rfl⟩)]
      simp only [hP_smul_right, smul_smul]
      linear_combination (norm := module) ((6 / 8 : ℂ) * hA) • hP (cw m) (eL (gM j m) (psiOf (Bop s) m t'))
        + hB • hP (cw j) (psiOf (Bop s) m t')
    · simp only [if_neg hmj, if_neg hmk]
      push_cast
      simp only [hP_sub_left, hP_add_left, hP_smul_left, hP_smul_right, hP_neg_right, hP_zero_left,
        map_sub, map_add, map_smul, phiTT_hP, smul_zero, zero_smul, add_zero, zero_add, sub_zero]
      rw [hcM]
      linear_combination (norm := module) ((-1 / 4 : ℂ) * hA) • hP (cw m) (eL (gM j k) (psiOf (Bop s) m t'))

end VOA.Moonshine.SigmaTop
