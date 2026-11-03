/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2Cube
import VOA.Moonshine.TForm

/-!
# The seed exists

The eigen-conditions of (R-top) reduce to one vector (`SigmaTop2Eigen.lean`): a nonzero `t ∈ T`
with `κ₊ e_{γ₊} t = −½ t`, `κ₋ e_{γ₋} t = ½ t` for all pairs (`IsSeed`).  It is constructed here.

* **Projector.**  For the Leech Lagrangian data `leechLagrangian` (`TForm.lean`:
  `γ₀ = 8e₀`, `γᵢ = 4e₀ + 4eᵢ`, partners `u`, `2rᵢ`) and arbitrary scalars `κᵢ` with
  `κᵢ² ε(γᵢ,γᵢ) = 1`, `∏ (1 + κᵢ e_{γᵢ})/2` has trace `1` (`trace_projK`), hence a common fixed
  vector exists (`exists_fixed_of_lagrangian`).
* **ξ-closure.**  `chargesS t = {a | W(a) t = ξ(a) t}` is an additive subgroup of `Λ₀`
  (`ξ` from `SigmaTop2Xi.lean`); it contains the 12 Lagrangian generators (by the projector) and the
  12 codeword charges `2·1_{D_k}` (`codeword_mem_chargesS`, by `eV_sq_codeword`, i.e. by the cube
  computation `golayTheta_codeword`), and therefore every `α₀ + α_k` (the kernel-checked codeword
  relation `colD_key`), which is all `isSeed_of_charges` needs.

## Main results
* `exists_fixed_of_lagrangian`, `chargesS`, `isSeed_of_charges`, `eV_sq_codeword`,
  `colD_key` (`decide +kernel`), `aP_codeword`.
* `seedExists : SeedExists` — unconditional.

## Status
`sorry`-free; `#print axioms seedExists`: `[propext, Classical.choice, Quot.sound]`; two
`decide +kernel` certificates on explicit integer vectors.  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open Module (End)
open VOA.Moonshine.TFormLeech

/-! ## §1  Common fixed vectors of a Lagrangian family of involutions -/

section Lag

variable (D : Lagrangian leech) (κ : ℕ → ℂ)

/-- The involutions `F_i = κ_i e_{γ_i}`. -/
noncomputable def lagK (i : ℕ) : End ℂ TLeechT := κ i • eL (D.γ i)

/-- `∏_{i<k} (1 + F_i)/2`. -/
noncomputable def projK : ℕ → End ℂ TLeechT
  | 0 => 1
  | k + 1 => projK k * ((1 / 2 : ℂ) • (1 + lagK D κ k))

variable {D κ}

theorem lagK_mul_self (hκ : ∀ i < D.m, κ i * κ i * εΛ (D.γ i) (D.γ i) = 1) {i : ℕ} (hi : i < D.m) :
    lagK D κ i * lagK D κ i = 1 := by
  rw [lagK, smul_mul_smul_comm, eL_mul_self, smul_smul, hκ i hi, one_smul]

theorem commute_lagK {i j : ℕ} (hi : i < D.m) (hj : j < D.m) : Commute (lagK D κ i) (lagK D κ j) :=
  ((commute_eT_of_even leech leech_even leech_isUnit_det_gramMat (D.form_even i hi j hj)).smul_left _).smul_right _

theorem commute_lagK_projK {j : ℕ} (hj : j < D.m) :
    ∀ k ≤ D.m, Commute (lagK D κ j) (projK D κ k)
  | 0, _ => Commute.one_right _
  | k + 1, hk => by
      refine (commute_lagK_projK hj k (by omega)).mul_right ?_
      exact ((Commute.one_right _).add_right (commute_lagK hj (by omega))).smul_right _

theorem commute_partner_projK {k : ℕ} (hk : k < D.m) :
    ∀ l ≤ k, Commute (eL (D.g k)) (projK D κ l)
  | 0, _ => Commute.one_right _
  | l + 1, hl => by
      refine (commute_partner_projK hk l (by omega)).mul_right ?_
      refine ((Commute.one_right _).add_right ?_).smul_right _
      exact (commute_eT_of_even leech leech_even leech_isUnit_det_gramMat
        (D.partner_even k hk l (by omega))).smul_right _

theorem trace_projK_mul_lagK {k : ℕ} (hk : k < D.m) :
    LinearMap.trace ℂ TLeechT (projK D κ k * lagK D κ k) = 0 := by
  set G := eL (D.g k)
  set P := projK D κ k
  set F := lagK D κ k
  have hGP : G * P = P * G := commute_partner_projK hk k le_rfl
  have hGF : G * F = -(F * G) := by
    simp only [G, F, lagK, mul_smul_comm, smul_mul_assoc, ← smul_neg]
    rw [eT_anticomm_of_odd leech leech_even leech_isUnit_det_gramMat (D.partner_odd k hk)]
  have hGG : G * G = εΛ (D.g k) (D.g k) • 1 := eL_mul_self _
  have h1 : LinearMap.trace ℂ TLeechT (P * F * G * G) = LinearMap.trace ℂ TLeechT (G * (P * F * G)) :=
    LinearMap.trace_mul_comm ℂ (P * F * G) G
  have hX : G * (P * F * G) = -(P * F * G * G) := by
    rw [← mul_assoc, ← mul_assoc, hGP, mul_assoc P G F, hGF]; noncomm_ring
  rw [hX, map_neg, mul_assoc (P * F), hGG, mul_smul_comm, mul_one, map_smul] at h1
  have hc := εΛ_ne_zero (D.g k) (D.g k)
  have h2 : εΛ (D.g k) (D.g k) * LinearMap.trace ℂ TLeechT (P * F) = 0 := by
    rw [smul_eq_mul] at h1
    linear_combination h1 / 2
  exact (mul_eq_zero.mp h2).resolve_left hc

theorem trace_projK : ∀ k ≤ D.m,
    LinearMap.trace ℂ TLeechT (projK D κ k) * 2 ^ k = (Module.finrank ℂ TLeechT : ℂ)
  | 0, _ => by simp [projK, LinearMap.trace_one]
  | k + 1, hk => by
      rw [projK, mul_smul_comm, mul_add, mul_one, map_smul, map_add,
        trace_projK_mul_lagK (by omega), add_zero, ← trace_projK k (by omega), smul_eq_mul, pow_succ]
      ring

theorem lagK_projK (hκ : ∀ i < D.m, κ i * κ i * εΛ (D.γ i) (D.γ i) = 1) {i : ℕ} (hi : i < D.m) :
    ∀ k ≤ D.m, i < k → lagK D κ i * projK D κ k = projK D κ k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, hk, h => by
      rw [projK]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · rw [← mul_assoc, lagK_projK hκ hi k (by omega) h']
      · subst h'
        rw [← mul_assoc, (commute_lagK_projK hi i (by omega)).eq, mul_assoc]
        congr 1
        rw [mul_smul_comm, mul_add, mul_one, lagK_mul_self hκ hi, add_comm]

/-- **A common fixed vector of the Lagrangian involutions `κ_i e_{γ_i}`.** -/
theorem exists_fixed_of_lagrangian (hκ : ∀ i < D.m, κ i * κ i * εΛ (D.γ i) (D.γ i) = 1) :
    ∃ t : TLeechT, t ≠ 0 ∧ ∀ i < D.m, κ i • eL (D.γ i) t = t := by
  have htr := trace_projK (D := D) (κ := κ) D.m le_rfl
  have hfr : Module.finrank ℂ TLeechT = 2 ^ D.m := by
    rw [Extraspecial.finrank_rep]
    have := D.two_mul_m
    congr 1; rw [bRank_eq_rank] at this ⊢; omega
  have hP : projK D κ D.m ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul, hfr] at htr
    exact (Nat.cast_ne_zero.mpr (by positivity) : ((2 ^ D.m : ℕ) : ℂ) ≠ 0) htr.symm
  obtain ⟨v, hv⟩ : ∃ v, projK D κ D.m v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP (LinearMap.ext hcon)
  refine ⟨projK D κ D.m v, hv, fun i hi => ?_⟩
  have h := congrArg (fun f : End ℂ TLeechT => f v) (lagK_projK hκ hi D.m le_rfl hi)
  simpa [lagK] using h

end Lag

/-! ## §2  The `ξ`-closure: the set of charges on which `W(a) t = ξ(a) t` -/

theorem phiR_injective : Function.Injective phiR := by
  intro x y h
  have h' := congrArg gv h
  rw [gv_phiR, gv_phiR] at h'
  funext i
  have := congrFun h' i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  omega

theorem tc_zero : tc 0 = 1 := by
  unfold tc; rw [latCob_zero, latCob_zero, charVal_zero]; norm_num

theorem Wop_zero : Wop 0 = 1 := by
  rw [Wop, tc_zero, one_smul, map_zero]
  exact eT_zero leech leech_even leech_isUnit_det_gramMat

/-- The charges `a ∈ R₀` with `W(a) t = ξ(a) t`; an additive subgroup. -/
noncomputable def chargesS (t : TLeechT) : AddSubgroup lam0.carrier where
  carrier := {a | ∃ x, inclN a = phiR x ∧ Wop a t = xi x • t}
  zero_mem' := ⟨0, by rw [map_zero, map_zero], by rw [Wop_zero, xi_zero, one_smul]; rfl⟩
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x + y, by rw [map_add, map_add, hx, hy], ?_⟩
    have hm := congrArg (fun f : End ℂ TLeechT => f t) (Wop_mul a b)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at hm
    rw [hb, map_smul, ha, smul_smul, hx, hy, mul_comm, xi_mul] at hm
    have hs := εN_sq (phiR x) (phiR y)
    calc Wop (a + b) t = (εN (phiR x) (phiR y) * εN (phiR x) (phiR y)) • Wop (a + b) t := by
          rw [hs, one_smul]
      _ = εN (phiR x) (phiR y) • (εN (phiR x) (phiR y) • Wop (a + b) t) := by rw [smul_smul]
      _ = εN (phiR x) (phiR y) • ((εN (phiR x) (phiR y) * xi (x + y)) • t) := by rw [← hm]
      _ = xi (x + y) • t := by rw [smul_smul, ← mul_assoc, hs, one_mul]
  neg_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨-x, by rw [map_neg, map_neg, hx], ?_⟩
    have hm := congrArg (fun f : End ℂ TLeechT => f t) (Wop_mul (-a) a)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, ha, map_smul, neg_add_cancel, Wop_zero,
      Module.End.one_apply] at hm
    have hx' := xi_mul x (-x)
    rw [add_neg_cancel, xi_zero, mul_one, map_neg] at hx'
    simp only [εN, latticeCocycle_neg_right] at hx'
    rw [map_neg, hx] at hm
    simp only [εN, latticeCocycle_neg_left] at hm
    have hne := xi_ne_zero x
    have : Wop (-a) t = (xi x)⁻¹ • (latticeCocycle golayN (phiR x) (phiR x) • t) := by
      rw [← hm, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this, smul_smul]
    congr 1
    rw [← hx']; field_simp

theorem mem_chargesS {t : TLeechT} {a : lam0.carrier} (h : a ∈ chargesS t) {y : Fin 24 → ℤ}
    (hy : inclN a = phiR y) : Wop a t = xi y • t := by
  obtain ⟨x, hx, ha⟩ := h
  rw [ha, phiR_injective (hx.symm.trans hy)]

/-! ## §3  `ξ` on pairs -/

theorem xi_pair (j k : Fin 24) :
    xi (Pi.single j 1 + Pi.single k 1) = -εN (golayRoot j) (golayRoot k) := by
  have h := xi_mul (Pi.single j 1) (Pi.single k 1)
  rw [xi_single, xi_single, phiR_single, phiR_single, Complex.I_mul_I] at h
  have hs := εN_sq (golayRoot j) (golayRoot k)
  linear_combination (-(εN (golayRoot j) (golayRoot k))) * h - xi (Pi.single j 1 + Pi.single k 1) * hs

theorem xi_neg_single (k : Fin 24) : xi (-Pi.single k 1) = -Complex.I * golayEps k := by
  have h := xi_mul (Pi.single k 1) (-Pi.single k 1)
  rw [add_neg_cancel, xi_zero, mul_one, xi_single, map_neg, phiR_single] at h
  change Complex.I * xi (-Pi.single k 1) = golayEps k at h
  have hI := Complex.I_mul_I
  linear_combination (-Complex.I) * h + xi (-Pi.single k 1) * hI

theorem xi_pairM (j k : Fin 24) :
    xi (Pi.single j 1 - Pi.single k 1) = golayEps k * εN (golayRoot j) (golayRoot k) := by
  have h := xi_mul (Pi.single j 1) (-Pi.single k 1)
  rw [xi_single, xi_neg_single, map_neg, phiR_single, phiR_single, ← sub_eq_add_neg] at h
  change Complex.I * (-Complex.I * golayEps k) = latticeCocycle golayN (golayRoot j) (-golayRoot k) * _ at h
  rw [latticeCocycle_neg_right] at h
  have hs := εN_sq (golayRoot j) (golayRoot k)
  have hI : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  linear_combination (-(εN (golayRoot j) (golayRoot k))) * h
    - xi (Pi.single j 1 - Pi.single k 1) * hs + (εN (golayRoot j) (golayRoot k) * golayEps k) * hI

theorem phiR_pair (j k : Fin 24) : phiR (Pi.single j 1 + Pi.single k 1) = inclN (aP j k) := by
  rw [map_add, phiR_single, phiR_single, inclN_aP]

theorem phiR_pairM (j k : Fin 24) : phiR (Pi.single j 1 - Pi.single k 1) = inclN (aM j k) := by
  rw [map_sub, phiR_single, phiR_single, inclN_aM, sub_eq_add_neg]

/-- **The seed from the `ξ`-closure**: if every `aP 0 j` lies in `chargesS t`, then `t` is a seed. -/
theorem isSeed_of_charges {t : TLeechT} (h : ∀ j, aP 0 j ∈ chargesS t) : IsSeed t := by
  have hP : ∀ j k, aP j k ∈ chargesS t := by
    intro j k
    have e : aP j k = aP 0 j + aP 0 k - aP 0 0 := by
      apply inclN_injective
      rw [map_sub, map_add, inclN_aP, inclN_aP, inclN_aP, inclN_aP]; abel
    rw [e]
    exact sub_mem (add_mem (h j) (h k)) (h 0)
  have hM : ∀ j k, aM j k ∈ chargesS t := by
    intro j k
    have e : aM j k = aP 0 j - aP 0 k := by
      apply inclN_injective
      rw [map_sub, inclN_aP, inclN_aP, inclN_aM]; abel
    rw [e]
    exact sub_mem (h j) (h k)
  intro j k hjk
  constructor
  · rw [AP_eq_Wop hjk, LinearMap.smul_apply, mem_chargesS (hP j k) (phiR_pair j k).symm,
      xi_pair j k, smul_smul]
    have hs := εN_sq (golayRoot j) (golayRoot k)
    congr 1
    linear_combination (-(1 / 2 : ℂ)) * hs
  · rw [AM_eq_Wop hjk, LinearMap.smul_apply, mem_chargesS (hM j k) (phiR_pairM j k).symm,
      xi_pairM j k, smul_smul]
    have hs := εN_sq (golayRoot j) (golayRoot k)
    have he := golayEps_mul_self k
    congr 1
    linear_combination (1 / 2 : ℂ) * (golayEps k * golayEps k) * hs + (1 / 2 : ℂ) * he

/-! ## §4  Codeword relations: `W(2b_D) = ξ(1_D)` from `Θ` on the spinor `e^{1_D}` -/

theorem charVal_negE (b : lam0.carrier) : charVal lam0 (-golayE) b = (eV b)⁻¹ := by
  simp [charVal, eV]

/-- **The Θ-scalar of a codeword charge**: `e(b)^{-2} = ξ(1_D)` when `ι_N b = 1_D`. -/
theorem eV_sq_codeword {b : lam0.carrier} {D : Finset (Fin 24)} (hb : gv (inclN b) = ind D)
    (h4 : 4 ∣ D.card) : (eV b * eV b)⁻¹ = xi (ind D) := by
  have h1 := golayTheta_bridgeN_latChargeGen b
  have hneg : charVal lam0 golayE (-b) = (eV b)⁻¹ := eV_neg b
  rw [bridgeN_latChargeGen, bridgeN_latChargeGen, aut_smul, golayTheta_codeword (inclN b) hb h4,
    smul_smul, map_neg, latCob_neg, charVal_negE, hneg, smul_smul] at h1
  have hne := latChargeGen_ne_zero' (-inclN b)
  have hc := latCob_ne_zero lam0 golayN inclN b
  have h2 := smul_left_injective ℂ hne h1
  simp only at h2
  have h3 : xi (ind D) = (eV b)⁻¹ * (eV b)⁻¹ := mul_right_cancel₀ hc (by rw [mul_comm, h2])
  rw [h3, mul_inv]

theorem eL_add_self (x : leech.carrier) : eL (x + x) = 1 := by
  have h := eT_add_two_nsmul leech leech_even leech_isUnit_det_gramMat 0 x
  rw [zero_add, two_nsmul] at h
  change eT leech leech_even leech_isUnit_det_gramMat (x + x) = 1
  rw [h]; exact eT_zero leech leech_even leech_isUnit_det_gramMat

theorem tc_add_self (b : lam0.carrier) : tc (b + b) = (eV b * eV b)⁻¹ := by
  unfold tc
  rw [latCob_add_self, latCob_add_self, charVal_add, mul_one, one_div]

theorem Wop_add_self (b : lam0.carrier) : Wop (b + b) = (eV b * eV b)⁻¹ • (1 : End ℂ TLeechT) := by
  rw [Wop, tc_add_self, map_add, eL_add_self]

theorem codeword_mem_chargesS (t : TLeechT) {b : lam0.carrier} {D : Finset (Fin 24)}
    (hb : gv (inclN b) = ind D) (h4 : 4 ∣ D.card) : b + b ∈ chargesS t := by
  refine ⟨ind D, ?_, ?_⟩
  · apply Subtype.ext
    change gv (inclN b) + gv (inclN b) = gv (phiR (ind D))
    rw [gv_phiR, hb, two_smul]
  · rw [Wop_add_self, LinearMap.smul_apply, Module.End.one_apply, eV_sq_codeword hb h4]

/-! ## §5  The explicit Golay data -/

/-- The codeword `D_k` with `D_k ∩ {12,…,23} = {12 + k}`: `(column k of B, e_k)`. -/
def colD (k : Fin 12) : Fin 24 → ℤ := fun l => ((Code.golayEnc (fun i => Code.golayB i k) l).val : ℤ)

theorem colD_four : ∀ k : Fin 12, (4 : ℤ) ∣ ∑ l, colD k l := by decide +kernel
theorem colD_01 : ∀ k : Fin 12, ∀ l, colD k l = 0 ∨ colD k l = 1 := by decide +kernel

/-- The coefficients of the codeword relation. -/
def ccD (k : Fin 12) (l : Fin 24) : ℤ := if 1 ≤ l.val ∧ l.val ≤ 11 then colD k l else 0
def mmD (k : Fin 12) : ℤ := ((∑ l, colD k l) - 2 * colD k 0) / 2
def apv (j k : Fin 24) : Fin 24 → ℤ := (2 : ℤ) • (Pi.single j 1 + (1 : ℤ) • Pi.single k 1)

/-- **The codeword relation** (kernel-checked): `α₀ + α_{12+k} = 2·1_{D_k} − Σ_{l=1}^{11} d_l (α₀ + α_l) + m (2α₀)`. -/
theorem colD_key : ∀ k : Fin 12, apv 0 (Fin.natAdd 12 k) =
    (2 : ℤ) • colD k - ∑ l, ccD k l • apv 0 l + mmD k • apv 0 0 := by decide +kernel

theorem gamVec_eq : ∀ i : Fin 12, gamVec i = (2 : ℤ) • apv 0 (Fin.castLE (by norm_num) i) := by
  decide +kernel

theorem colD_mem (k : Fin 12) : colD k ∈ Leech.subA := by
  refine ⟨Leech.mem_preG.2 ?_, colD_four k⟩
  have : reduceMod 2 24 (colD k) = Code.golayEnc (fun i => Code.golayB i k) := by
    funext l
    change (((Code.golayEnc (fun i => Code.golayB i k) l).val : ℤ) : ZMod 2) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [this]; exact Code.golayEnc_mem _

/-- The codeword charge `b_k = 1_{D_k} ∈ Λ₀`. -/
def bD (k : Fin 12) : lam0.carrier := (⟨colD k, colD_mem k⟩ : ↥Leech.subA)

/-- The support of `D_k`. -/
def DK (k : Fin 12) : Finset (Fin 24) := Finset.univ.filter fun l => colD k l = 1

theorem ind_DK (k : Fin 12) : ind (DK k) = colD k := by
  funext l
  simp only [ind, DK, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases colD_01 k l with h | h <;> simp [h]

theorem four_dvd_card_DK (k : Fin 12) : 4 ∣ (DK k).card := by
  have h := colD_four k
  rw [← ind_DK] at h
  simp only [ind, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter] at h
  exact_mod_cast h

theorem gv_inclN_bD (k : Fin 12) : gv (inclN (bD k)) = ind (DK k) := by
  rw [ind_DK]; rfl

theorem aP_val (j k : Fin 24) : ((show ↥Leech.subA from aP j k) : Fin 24 → ℤ) = apv j k := rfl

/-- The coordinates of `Λ₀ = A ⊆ ℤ²⁴`, as a `ℤ`-linear map. -/
def valA : lam0.carrier →ₗ[ℤ] (Fin 24 → ℤ) where
  toFun a := (show ↥Leech.subA from a).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valA_injective : Function.Injective valA := fun _ _ h => Subtype.ext h

/-- The codeword relation in `Λ₀`. -/
theorem aP_codeword (k : Fin 12) :
    aP 0 (Fin.natAdd 12 k) = (bD k + bD k) - ∑ l, ccD k l • aP 0 l + mmD k • aP 0 0 := by
  apply valA_injective
  rw [map_add, map_sub, map_add, map_sum]
  simp only [map_zsmul]
  change apv 0 (Fin.natAdd 12 k) = colD k + colD k - ∑ l, ccD k l • apv 0 l + mmD k • apv 0 0
  rw [colD_key k, two_smul]

/-! ## §6  The seed -/

theorem γ_eq (i : ℕ) (hi : i < 12) : leechLagrangian.γ i = inclΛ (aP 0 ⟨i, by omega⟩) := by
  change γL i = _
  rw [γL, dif_pos hi]
  apply Subtype.ext
  change gamVec ⟨i, hi⟩ = (2 : ℤ) • apv 0 ⟨i, by omega⟩
  exact gamVec_eq ⟨i, hi⟩

theorem aP00_eq : aP 0 0 = aP 0 1 + aM 0 1 := by
  apply inclN_injective
  rw [map_add, inclN_aP, inclN_aP, inclN_aM]; abel

theorem tc_aP00_sq : tc (aP 0 0) * tc (aP 0 0) = εΛ (inclΛ (aP 0 0)) (inclΛ (aP 0 0)) := by
  have h := tc_mul_self (aP 0 0)
  have he : eV (aP 0 0) * eV (aP 0 0) = 1 := by
    rw [aP00_eq]
    change charVal lam0 golayE (aP 0 1 + aM 0 1) * charVal lam0 golayE (aP 0 1 + aM 0 1) = 1
    rw [charVal_add]
    have h1 := eV_aP_sq (show (0 : Fin 24) ≠ 1 by decide)
    have h2 := eV_aM_sq (show (0 : Fin 24) ≠ 1 by decide)
    have e0 := golayEps_mul_self 0
    have e1 := golayEps_mul_self 1
    change eV (aP 0 1) * eV (aM 0 1) * (eV (aP 0 1) * eV (aM 0 1)) = 1
    linear_combination (eV (aM 0 1) * eV (aM 0 1)) * h1 + (golayEps 0 * golayEps 1) * h2
      + (golayEps 1 * golayEps 1) * e0 + e1
  have hN : εN (inclN (aP 0 0)) (inclN (aP 0 0)) = 1 := by
    rw [inclN_aP]
    have hs := εN_sq (golayRoot 0) (golayRoot 0)
    simp only [εN, latticeCocycle_add_left, latticeCocycle_add_right] at hs ⊢
    linear_combination (latticeCocycle golayN (golayRoot 0) (golayRoot 0) ^ 2 + 1) * hs
  rw [he, hN, mul_one, mul_one] at h
  exact h

/-- The scalars of the Lagrangian involutions `F_i = −ε_N(α₀,α_i) W(α₀ + α_i)`. -/
noncomputable def κS (i : ℕ) : ℂ :=
  if h : i < 24 then -εN (golayRoot 0) (golayRoot ⟨i, h⟩) * tc (aP 0 ⟨i, h⟩) else 0

theorem tc_aP0_sq (i : Fin 24) : tc (aP 0 i) * tc (aP 0 i) = εΛ (inclΛ (aP 0 i)) (inclΛ (aP 0 i)) := by
  by_cases hi : i = 0
  · subst hi; exact tc_aP00_sq
  · exact tc_aP_sq (Ne.symm hi)

theorem hκS : ∀ i < leechLagrangian.m, κS i * κS i *
    εΛ (leechLagrangian.γ i) (leechLagrangian.γ i) = 1 := by
  intro i hi
  have hi' : i < 12 := hi
  rw [γ_eq i hi', κS, dif_pos (by omega)]
  have h1 := tc_aP0_sq ⟨i, by omega⟩
  have h2 := εN_sq (golayRoot 0) (golayRoot ⟨i, by omega⟩)
  have h3 := εΛ_sq (inclΛ (aP 0 ⟨i, by omega⟩)) (inclΛ (aP 0 ⟨i, by omega⟩))
  linear_combination (tc (aP 0 ⟨i, by omega⟩) * tc (aP 0 ⟨i, by omega⟩) *
      εΛ (inclΛ (aP 0 ⟨i, by omega⟩)) (inclΛ (aP 0 ⟨i, by omega⟩))) * h2
    + εΛ (inclΛ (aP 0 ⟨i, by omega⟩)) (inclΛ (aP 0 ⟨i, by omega⟩)) * h1 + h3

/-- **The seed exists** (unconditional): a nonzero `t ∈ T` with `κ₊ e_{γ₊} t = −½ t` and
`κ₋ e_{γ₋} t = ½ t` for all pairs `j ≠ k`. -/
theorem seedExists : SeedExists := by
  obtain ⟨t, ht0, hfix⟩ := exists_fixed_of_lagrangian (D := leechLagrangian) (κ := κS) hκS
  refine ⟨t, ht0, isSeed_of_charges ?_⟩
  have hgen : ∀ i (hi : i < 12), aP 0 ⟨i, by omega⟩ ∈ chargesS t := by
    intro i hi
    have h := hfix i hi
    rw [γ_eq i hi, κS, dif_pos (by omega)] at h
    refine ⟨Pi.single 0 1 + Pi.single ⟨i, by omega⟩ 1, (phiR_pair 0 ⟨i, by omega⟩).symm, ?_⟩
    rw [xi_pair, Wop, LinearMap.smul_apply]
    have hs := εN_sq (golayRoot 0) (golayRoot ⟨i, by omega⟩)
    calc tc (aP 0 ⟨i, by omega⟩) • eL (inclΛ (aP 0 ⟨i, by omega⟩)) t
        = (-εN (golayRoot 0) (golayRoot ⟨i, by omega⟩)) •
            ((-εN (golayRoot 0) (golayRoot ⟨i, by omega⟩) * tc (aP 0 ⟨i, by omega⟩)) •
              eL (inclΛ (aP 0 ⟨i, by omega⟩)) t) := by
          rw [smul_smul, ← mul_assoc, neg_mul_neg, hs, one_mul]
      _ = _ := by rw [h]
  have hgen' : ∀ j : Fin 24, j.val < 12 → aP 0 j ∈ chargesS t := fun j hj => hgen j.val hj
  intro j
  rcases lt_or_ge j.val 12 with hj | hj
  · exact hgen' j hj
  · have hk : j = Fin.natAdd 12 (⟨j.val - 12, by omega⟩ : Fin 12) := by
      ext; simp; omega
    rw [hk, aP_codeword]
    refine add_mem (sub_mem (codeword_mem_chargesS t (gv_inclN_bD _) (four_dvd_card_DK _))
      (sum_mem fun l _ => ?_)) (zsmul_mem (hgen' 0 (by norm_num)) _)
    by_cases hl : 1 ≤ l.val ∧ l.val ≤ 11
    · exact zsmul_mem (hgen' l (by omega)) _
    · rw [ccD, if_neg hl, zero_smul]; exact zero_mem _

end VOA.Moonshine.SigmaTop
